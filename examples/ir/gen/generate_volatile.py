#!/usr/bin/env python3

import argparse
import subprocess as sub
import shutil as sh
import os
import textwrap

script_dir = os.path.dirname(os.path.realpath(__file__))
for A in [10, 50]:
    for logN in [5, 10, 20, 40, 60]:
        N = 2**logN
        p = 0x73EDA753299D7D483339D80809A1D80553BDA402FFFE5BFEFFFFFFFF00000001
        comp = f"""
            (set_default_modulus {p}
            (declare
                (
                    (x (mod {p}))
                    (y (mod {p}))
                    (b bool)
                )
            (let (
                (a0 (#a (mod {p}) #f0 {N} ()))
                (pow0 #f1)
            """
        for a_i in range(A - 1):
            comp += f"""
                (a{a_i + 1} (ite b (store a{a_i} (+ x #f{a_i}) pow{a_i}) a{a_i}))
                (pow{a_i + 1} (* pow{a_i} y))
            """
        comp += f"""
                (output (select a{A - 1} y))
                )
        """
        comp_suffix = ")))"
        contents = textwrap.dedent(
            f"""
        ; TEST_FILE
        ; FEATURES: r1cs poly
        ; CMD: $circ $file r1cs --proof-impl mirage --action count
        (computations
         (main
          (computation
           (metadata
            (parties prover verifier)
            (inputs
                (x (mod {p}))
                (y (mod {p}))
                (b bool)
            )
            (commitments))
           (precompute
            ()
            ((return (mod {p})))
            (tuple {comp}
                output
            {comp_suffix})
            )
           (ram_arrays (#a (mod {p}) #f0m{p} {N} ()))
           {comp}
           (= output y)
           {comp_suffix}
           )))"""
        )
        with open(f"{script_dir}/../volatile_{A}accs_size{N}.circir", "w") as f:
            print(contents, file=f)

