//! Runs a ZoKrates `@test` through compilation, assertion checking, setup,
//! proving, and verification.
//!
//! The runner is generic over [`ProofSystem`](crate::target::r1cs::proof::ProofSystem).
//! Bellman and Mirage implement
//! this interface, and `ztest` selects between them for each test. Spartan uses
//! a separate interface and is not supported here. CLI output remains in `ztest`.

use crate::cfg::cfg;
use crate::compile::{opt_for_proof, to_proof_data};
use crate::front::zsharpcurly::{Inputs, TestCase, ZSharpCurlyFE};
use crate::front::{FrontEnd, Mode};
use crate::ir::term::{eval, Value};
use crate::target::r1cs::proof::ProofSystem;
use fxhash::FxHashMap;
use std::cell::Cell;
use std::sync::Once;

/// Result of running one test.
///
/// Assertion failures are kept separate from compile/backend errors, so
/// execution failures are not treated as expected test rejections.
#[derive(Debug)]
pub enum Outcome {
    /// The assertion pre-check passed and the proof verified.
    Pass,
    /// The assertion pre-check failed.
    AssertionFailed(String),
    /// Frontend compilation, optimization, or R1CS lowering failed.
    CompileError(String),
    /// Proof setup, proving, or verification failed.
    BackendError(String),
}

thread_local! {
    /// Set while a [catch] call is running on this thread, so the shared panic
    /// hook stays quiet for *this thread's* panics only.
    static SUPPRESS_PANIC: Cell<bool> = const { Cell::new(false) };
}

static HOOK_INIT: Once = Once::new();

/// Installs one panic hook that uses a thread-local flag to silence panics
/// caught by [`catch`]. Installing it once avoids races from replacing the
/// global hook on every call.
fn install_quiet_hook() {
    HOOK_INIT.call_once(|| {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            if !SUPPRESS_PANIC.with(|s| s.get()) {
                prev(info);
            }
        }));
    });
}

/// Run `f`, converting a panic on the current thread into `Err(message)`.
/// The frontend and the prover report failures by panicking. Panic-hook noise
/// is suppressed for this thread only (see [install_quiet_hook]). Cannot
/// contain `process::exit` paths (some frontend semantic errors exit rather
/// than unwind).
///
/// Public because discovery can panic too ([`ZSharpCurlyFE::eval_test_inputs`]
/// panics on a parse/load failure).
///
/// TODO: replace with `Result` propagation once the frontend and prover
/// return structured errors.
pub fn catch<R>(f: impl FnOnce() -> R) -> Result<R, String> {
    install_quiet_hook();
    let was = SUPPRESS_PANIC.with(|s| s.replace(true));
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    SUPPRESS_PANIC.with(|s| s.set(was));
    result.map_err(|e| {
        if let Some(msg) = e.downcast_ref::<String>() {
            msg.clone()
        } else if let Some(msg) = e.downcast_ref::<&str>() {
            (*msg).to_string()
        } else {
            "unknown panic".to_string()
        }
    })
}

/// Runs one `@test` using the proof system `PS`.
///
/// The test is recompiled from its own source file ([`TestCase::file`]), so the
/// case stays bound to the file it was discovered in. The config is read from
/// the process-global [`cfg()`]; the caller must have set it (via `circ::cfg::set`
/// or `set_default`) and it fixes the field and compiler options for the process.
pub fn run_test<PS: ProofSystem>(test: &TestCase) -> Outcome {
    // Compile the test function as its own entry point, from the file it was
    // discovered in. A failure here means the test never became a circuit.
    let name = test.name().to_string();
    let file = test.file().to_path_buf();
    let comps = match catch(move || {
        ZSharpCurlyFE::gen(Inputs {
            file,
            entry: name,
            mode: Mode::Proof,
        })
    }) {
        Ok(c) => c,
        Err(e) => return Outcome::CompileError(e),
    };

    // Give the prover all inputs and the verifier only public inputs.
    let mut prover_map: FxHashMap<String, Value> = FxHashMap::default();
    let mut verifier_map: FxHashMap<String, Value> = FxHashMap::default();
    for input in test.inputs() {
        let entries = input.flat_entries();
        if input.public() {
            verifier_map.extend(entries.iter().cloned());
        }
        prover_map.extend(entries);
    }

    //Optimization replaces private values with constants when required by the circuit,
    //allowing some private inputs that would fail assertions to actually pass proof verification.
    //We check these asserts separately, before optimization, and fail on these inputs.
    //Note: this differs from what the real prove/verify pipeline does!
    //TODO: Make this a warning instead of a failure.

    let held = catch(|| {
        comps
            .get(test.name())
            .outputs
            .iter()
            .all(|a| matches!(eval(a, &prover_map), Value::Bool(true)))
    });
    match held {
        Ok(true) => {}
        Ok(false) => {
            return Outcome::AssertionFailed(
                "an assertion does not hold for the given inputs".to_string(),
            )
        }
        // A panic while evaluating the compiled IR is an internal/compile-side
        // failure, not an assertion rejection.
        Err(e) => return Outcome::CompileError(e),
    }

    // Lower to prover/verifier data: the canonical proof-mode IR optimization
    // pipeline (shared with the CLI driver via opt_for_proof — required so
    // array/tuple terms are scalarized before R1CS lowering) followed by
    // R1CS lowering.
    let name = test.name().to_string();
    let lowered = catch(move || {
        let comps = opt_for_proof(comps, cfg());
        let cs = comps.get(&name);
        let (p_data, v_data, _stats) = to_proof_data(cs, cfg());
        (p_data, v_data)
    });
    let (p_data, v_data) = match lowered {
        Ok(d) => d,
        Err(e) => return Outcome::CompileError(e),
    };

    // Run backend setup, proving, and verification. Failures in this phase are
    // reported as `BackendError`.
    let setup = catch(move || PS::setup(p_data, v_data));
    let (pk, vk) = match setup {
        Ok(keys) => keys,
        Err(e) => return Outcome::BackendError(e),
    };
    match catch(|| {
        let pf = PS::prove(&pk, &prover_map);
        PS::verify(&vk, &verifier_map, &pf)
    }) {
        Ok(true) => Outcome::Pass,
        Ok(false) => Outcome::BackendError("proof did not verify".to_string()),
        Err(e) => Outcome::BackendError(e),
    }
}
