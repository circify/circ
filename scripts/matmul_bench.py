#!/usr/bin/env python3
"""Matrix-expression benchmarks: the paper's AIP suite, written in Z# for CirC.

Each benchmark is one naive program -- `assert(P == <matrix expression>)` over
`n x n` matrices -- compiled under three configurations, which differ only in
compiler flags:

  -rand     --ir-matmul-ip false     the verifier recomputes every product
                                     (O(n^3) constraints per product)
  default   --ir-matmul-ip true      each product becomes a prover hint checked
                                     at a fresh uniform independent random
                                     vector (Freivalds); O(n^2) per product
  +share    ... --ir-share-challenges true   as default, but the coins the
                                     transform named alike are merged into one
                                     vector, shared by every product

`-reord` has no analogue: CirC's challenge skolemization (src/ir/opt/chall.rs)
gives every challenge the earliest legal round on its own, so the merged form is
the only one it emits.

`hand` and `hand+share` compile a hand-written randomized protocol instead --
the same optimization spelled out in Z# with `unsafe witness` and
`sample_challenge`. They are the oracle the transform is checked against, not
part of the paper's configuration set.

Usage:
    scripts/matmul_bench.py --n 30 --count-only          # constraints, fast
    scripts/matmul_bench.py --n 30 --trials 3            # + setup/prove/verify
    scripts/matmul_bench.py --n 8 --only AB ABCD         # a subset

CSV goes to stdout (one row per program x configuration x trial); progress and
compiler output go to stderr.
"""

import argparse
import csv
import os
import random
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
# ark_bls12_381::Fr, the field the artifact's compiler fixes.
MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513

# The artifact's benchmark list (artifact/rust/examples/bench.rs).
BENCHMARKS = [
    ("AB", "A * B"),
    ("ABC", "A * B * C"),
    ("AB+CD", "A * B + C * D"),
    ("AB+BC", "A * B + B * C"),
    ("A(B+C)D", "A * (B + C) * D"),
    ("A(BC+D)", "A * (B * C + D)"),
    ("ABCD", "A * B * C * D"),
    ("ABC+AD", "A * B * C + A * D"),
    ("ABAB", "A * B * A * B"),
    ("AB+CD+AC", "A * B + C * D + A * C"),
]

# CLI name -> (label in the CSV, source form, extra compiler flags).
# The labels are the paper's; the CLI names avoid argparse's leading `-`/`+`.
CONFIGS = {
    "norand": ("-rand", "naive", ["--ir-matmul-ip", "false"]),
    "default": ("default", "naive", ["--ir-matmul-ip", "true"]),
    "share": ("+share", "naive",
              ["--ir-matmul-ip", "true", "--ir-share-challenges", "true"]),
    "hand": ("hand", "hand", ["--ir-matmul-ip", "false"]),
    "handshare": ("hand+share", "hand-share", ["--ir-matmul-ip", "false"]),
}
DEFAULT_CONFIGS = ["norand", "default", "share"]


# ---------------------------------------------------------------- expressions

def parse(s, assoc="left"):
    """`A * (B + C) * D` -> a binary tree; `assoc` picks how `*` chains nest.

    The MA front end (`artifact/rust/src/parse.rs`) makes `*` **right**-
    associative, Z# makes it left-associative. The choice is invisible to the
    value (matrix product is associative) but not to the compiled protocol: with
    a shared challenge vector, `A*(B*(C*D))` makes each Freivalds check's operand
    exactly the previous check's `m_i * v`, which CSE then computes once, while
    `((A*B)*C)*D` needs `m_i * (C*v)` and shares nothing. Pass `assoc="right"` to
    hand CirC the same tree the MA harness compiles.
    """
    toks = re.findall(r"[A-Za-z]\w*|[*+()]", s)
    pos = 0

    def peek():
        return toks[pos] if pos < len(toks) else None

    def eat(t=None):
        nonlocal pos
        got = toks[pos]
        assert t is None or got == t, f"expected {t}, got {got}"
        pos += 1
        return got

    def atom():
        if peek() == "(":
            eat("(")
            e = add()
            eat(")")
            return e
        return ("var", eat())

    def mul():
        e = atom()
        if peek() != "*":
            return e
        eat("*")
        if assoc == "right":
            return ("*", e, mul())
        while True:
            e = ("*", e, atom())
            if peek() != "*":
                return e
            eat("*")

    def add():
        e = mul()
        while peek() == "+":
            eat("+")
            e = ("+", e, mul())
        return e

    e = add()
    assert pos == len(toks), f"trailing tokens in {s!r}"
    return e


def variables(e):
    """The matrix variables an expression uses, in first-use order."""
    if e[0] == "var":
        return [e[1]]
    seen = []
    for sub in e[1:]:
        for v in variables(sub):
            if v not in seen:
                seen.append(v)
    return seen


def evaluate(e, mats):
    """Evaluate over Python matrices, mod MODULUS."""
    if e[0] == "var":
        return mats[e[1]]
    l, r = evaluate(e[1], mats), evaluate(e[2], mats)
    n = len(l)
    if e[0] == "+":
        return [[(l[i][j] + r[i][j]) % MODULUS for j in range(n)] for i in range(n)]
    return [
        [sum(l[i][k] * r[k][j] for k in range(n)) % MODULUS for j in range(n)]
        for i in range(n)
    ]


# ------------------------------------------------------------------- codegen

def helpers(n):
    return f"""def matmul(field[{n}][{n}] a, field[{n}][{n}] b) -> field[{n}][{n}]:
    field[{n}][{n}] c = [[0; {n}]; {n}]
    for field i in 0..{n} do
        for field j in 0..{n} do
            field s = 0
            for field k in 0..{n} do
                s = s + a[i][k] * b[k][j]
            endfor
            c[i][j] = s
        endfor
    endfor
    return c

def matadd(field[{n}][{n}] a, field[{n}][{n}] b) -> field[{n}][{n}]:
    field[{n}][{n}] c = [[0; {n}]; {n}]
    for field i in 0..{n} do
        for field j in 0..{n} do
            c[i][j] = a[i][j] + b[i][j]
        endfor
    endfor
    return c

def matvec(field[{n}][{n}] a, field[{n}] v) -> field[{n}]:
    field[{n}] r = [0; {n}]
    for field i in 0..{n} do
        field s = 0
        for field k in 0..{n} do
            s = s + a[i][k] * v[k]
        endfor
        r[i] = s
    endfor
    return r

def eqvec(field[{n}] a, field[{n}] b) -> bool:
    for field i in 0..{n} do
        assert(a[i] == b[i])
    endfor
    return true

def eqmat(field[{n}][{n}] a, field[{n}][{n}] b) -> bool:
    for field i in 0..{n} do
        assert(eqvec(a[i], b[i]))
    endfor
    return true
"""


def signature(vs, n):
    args = ", ".join(f"public field[{n}][{n}] {v}" for v in vs + ["P"])
    return f"def main({args}) -> bool:"


def render(e):
    """The expression in Z# syntax, fully parenthesized."""
    if e[0] == "var":
        return e[1]
    return f"({render(e[1])} {e[0]} {render(e[2])})"


def gen_naive(expr, n):
    """The input program: assert the matrix expression, and let CirC decide how.

    This is the program all three of the paper's configurations compile; they
    differ only in what the compiler does with the products in it.
    """
    return "\n".join(
        [signature(variables(expr), n),
         f"    assert(P == {render(expr)})",
         "    return true", ""]
    )


def gen_hand(expr, n, share):
    """The hand-written randomized protocol -- the oracle for the transform.

    Each product becomes a prover hint checked at a random vector.

    Statements are emitted in dependency order (products and sums interleaved),
    then the challenge vectors, then the checks. The challenges therefore depend
    on every witness, which puts all of them in one round after the prover's
    single message -- the "randomized 1 round" shape from the paper.

    A challenge's IR children only fix *which round* it belongs to
    (src/ir/opt/chall.rs); its value comes from Mirage's Fiat-Shamir over the
    commitment to the whole previous round (`alloc_random` in
    src/target/r1cs/mirage.rs), so listing one entry per witness is enough.
    """
    stmts, checks, counter = [], [], [0]

    def go(e):
        if e[0] == "var":
            return e[1]
        l, r = go(e[1]), go(e[2])
        name = f"t{counter[0]}"
        counter[0] += 1
        if e[0] == "+":
            stmts.append(f"    field[{n}][{n}] {name} = matadd({l}, {r})")
        else:
            stmts.append(f"    unsafe witness field[{n}][{n}] {name} = matmul({l}, {r})")
            checks.append((name, l, r))
        return name

    top = go(expr)
    witnesses = [name for name, _, _ in checks]
    # One entry per witness: enough to place every challenge after the prover's
    # message. (Empty is impossible: every benchmark has at least one product.)
    deps = "[" + ", ".join(f"{w}[0][0]" for w in witnesses) + "]"
    k = len(witnesses)

    def sample(vec):
        return [
            f"    field[{n}] {vec} = [0; {n}]",
            f"    for field i in 0..{n} do",
            f"        {vec}[i] = sample_challenge::<{k}>({deps})",
            f"    endfor",
        ]

    coin_lines, check_lines = [], []
    if share:
        coin_lines += sample("v")
    for i, (name, l, r) in enumerate(checks):
        vec = "v" if share else f"v{i}"
        if not share:
            coin_lines += sample(vec)
        check_lines.append(
            f"    assert(eqvec(matvec({name}, {vec}), matvec({l}, matvec({r}, {vec}))))"
        )

    return "\n".join(
        ['from "EMBED" import sample_challenge', "", helpers(n), "",
         signature(variables(expr), n), *stmts, *coin_lines, *check_lines,
         f"    assert(eqmat({top}, P))", "    return true", ""]
    )


def hand_coins(expr, n, share):
    """Verifier coins in a hand-written protocol: one per challenge."""
    products = str(expr).count("'*'")
    return n if share else n * products


# ------------------------------------------------------------------- instance

def instance_files(expr, n, path, seed=0):
    """Write the `.pin` (prover) and `.vin` (verifier) input files."""
    rng = random.Random(seed)
    vs = variables(expr)
    mats = {v: [[rng.randrange(MODULUS) for _ in range(n)] for _ in range(n)] for v in vs}
    mats["P"] = evaluate(expr, mats)
    binds = "\n".join(
        f"({m}.{i}.{j} #f{mats[m][i][j]})"
        for m in vs + ["P"]
        for i in range(n)
        for j in range(n)
    )
    header = f"(set_default_modulus {MODULUS}\n(let (\n"
    path.with_suffix(".zok.pin").write_text(header + binds + "\n) true; ignored\n))\n")
    path.with_suffix(".zok.vin").write_text(
        header + binds + "\n(return true)\n) true; ignored\n))\n"
    )


# --------------------------------------------------------------------- runner

COIN_RE = re.compile(r"(\d+) challenge\(s\) skolemized")
COUNT_RE = re.compile(r"Final r1cs: (\d+) constraints, (\d+) variables, (\d+) entries, (\d+) rounds")


def run(cmd, cwd, env):
    t = time.time()
    p = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True)
    return p, (time.time() - t) * 1000.0


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--n", type=int, default=30, help="matrix dimension (default: 30)")
    ap.add_argument("--out", type=Path, default=REPO / "matmul_bench",
                    help="directory for generated programs and keys")
    ap.add_argument("--trials", type=int, default=0,
                    help="prove/verify trials per configuration (0 = count only)")
    ap.add_argument("--count-only", action="store_true", help="same as --trials 0")
    ap.add_argument("--only", nargs="*", metavar="NAME", help="run only these benchmarks")
    ap.add_argument("--configs", nargs="*", default=DEFAULT_CONFIGS, choices=list(CONFIGS))
    ap.add_argument("--mode", default="release", choices=["release", "debug"])
    ap.add_argument("--assoc", default="right", choices=["left", "right"],
                    help="how `*` chains nest (default: right, matching the MA "
                         "front end, so both compilers see the same tree; "
                         "`left` is Z#'s own associativity)")
    args = ap.parse_args()
    trials = 0 if args.count_only else args.trials

    circ = REPO / "target" / args.mode / "examples" / "circ"
    zk = REPO / "target" / args.mode / "examples" / "zk"
    for b in (circ, zk):
        if not b.exists():
            sys.exit(f"{b} not built; run ./driver.py --features bellman r1cs poly zok && ./driver.py -b")

    env = dict(os.environ)
    # The skolemizer reports how many coins became variables; that is the
    # honest count, whatever the transform and the sharing pass did.
    env["RUST_LOG"] = "circ::ir::opt::chall=debug"
    # The stdlib path must match *this* checkout, whatever the shell exports.
    env["ZSHARP_STDLIB_PATH"] = str(REPO / "third_party/ZoKrates/zokrates_stdlib/stdlib")
    if shutil.which("cvc5") and not shutil.which("cvc4"):
        env.setdefault("RSMT2_CVC4_CMD", "cvc5")

    args.out.mkdir(parents=True, exist_ok=True)
    benches = [(name, e) for name, e in BENCHMARKS
               if not args.only or name in args.only]

    w = csv.writer(sys.stdout)
    w.writerow("program n optimization trial constraints challenge_rounds coins "
               "setup_ms prove_ms verify_ms proof_bytes verified".split())

    for name, src in benches:
        expr = parse(src, args.assoc)
        slug = re.sub(r"[^A-Za-z0-9]", "_", name)
        for config in args.configs:
            label, source, flags = CONFIGS[config]
            stem = args.out / f"{slug}_{config}_{args.n}"
            zok = stem.with_suffix(".zok")
            zok.write_text(
                gen_naive(expr, args.n) if source == "naive"
                else gen_hand(expr, args.n, share=(source == "hand-share"))
            )
            instance_files(expr, args.n, stem)
            print(f"[{name} {label}] compiling", file=sys.stderr)

            action = "count" if trials == 0 else "setup"
            p, setup_ms = run([str(circ), *flags, str(zok), "r1cs", "--action", action,
                               "--proof-impl", "mirage"], args.out, env)
            m = COUNT_RE.search(p.stdout)
            if p.returncode != 0 or not m:
                sys.stderr.write(p.stdout + p.stderr)
                w.writerow([name, args.n, label, "", "", "", "", "", "", "", "", "error"])
                continue
            constraints, rounds = int(m.group(1)), int(m.group(4))
            coin_line = COIN_RE.search(p.stderr)
            c = int(coin_line.group(1)) if coin_line else 0
            print(f"[{name} {label}] {constraints} constraints, {rounds} rounds, "
                  f"{c} coins", file=sys.stderr)

            if trials == 0:
                w.writerow([name, args.n, label, "", constraints, rounds, c,
                            "", "", "", "", ""])
                sys.stdout.flush()
                continue

            for trial in range(1, trials + 1):
                pp, prove_ms = run([str(zk), "--inputs", str(stem.with_suffix(".zok.pin")),
                                    "--action", "prove", "--proof-impl", "mirage"],
                                   args.out, env)
                vp, verify_ms = run([str(zk), "--inputs", str(stem.with_suffix(".zok.vin")),
                                     "--action", "verify", "--proof-impl", "mirage"],
                                    args.out, env)
                ok = pp.returncode == 0 and vp.returncode == 0 and "invalid proof" not in vp.stderr
                pi = args.out / "pi"
                w.writerow([name, args.n, label, trial, constraints, rounds, c,
                            f"{setup_ms:.1f}", f"{prove_ms:.1f}", f"{verify_ms:.1f}",
                            pi.stat().st_size if pi.exists() else "",
                            str(ok).lower()])
                sys.stdout.flush()


if __name__ == "__main__":
    main()
