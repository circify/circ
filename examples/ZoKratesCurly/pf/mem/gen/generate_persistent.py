#!/usr/bin/env python3

import argparse
import subprocess as sub
import shutil as sh
import os
import textwrap

script_dir = os.path.dirname(os.path.realpath(__file__))
for A in [10, 50]:
    for logN in [5, 10]:
        N = 2**logN
        output = f"{script_dir}/../persistent_{A}accs_size{N}.zok"
        sub.run(
            f'cat {script_dir}/persistent_template.zok | sed "s/7777/{N}/g" | sed "s/99/{A}/g" > {output}',
            shell=True,
            check=True,
        )
