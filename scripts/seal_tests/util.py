import os 
from subprocess import Popen, PIPE
import sys
from typing import List
from tqdm import tqdm

def rename_test(name: str, lang: str) -> str:
    """Append path with language type"""
    return f"{name}_{lang}"

def build_cmd(name:str, test_file: str) -> List[str]:
    bytecode = f"./scripts/seal_tests/tests/{name}_bytecode.txt"
    return [os.getenv("SEAL_SOURCE") + "/build/bin/sealinterpreter", "-M", "fhe", "-b", bytecode, "-t", test_file] 

def get_result(file_path):
    if os.path.exists(file_path):
        with open(file_path) as f:
            lines = f.read().splitlines()
            for line in lines:
                l = line.split()
                if l and l[0] == "res":
                    return l[1]
            raise RuntimeError("Unable to find result: "+file_path)
    else:
        raise RuntimeError("Unable to open file: "+file_path)


def run_test(expected: str, cmd: List[str]) -> bool:
    try:
        proc = Popen(" ".join(cmd), shell=True, stdout=PIPE, stderr=PIPE)

        out, err = proc.communicate(timeout=30)

        if err:
            raise RuntimeError("Error: "+err.decode("utf-8").strip())

        out = out.decode("utf-8").strip()

        assert out == expected, "out: "+out+"\nexpected: "+expected
        return True, ""
    except Exception as e:
        # print("Exception: ", e)
        return False, e

def run_tests(lang: str, tests: List[dict]):
    """
    tests will be a list of all tests to run. each element in the list will be 
    1. description of test case: str
    2. test name: str
    4. test file path: str 
    """
    print(f"Running FHE tests for {lang} frontend")
    failed_test_descs = []
    num_retries = 2
    
    for test in tqdm(tests, leave=False, dynamic_ncols=True):
        assert len(test) == 3, "test configurations are wrong for test: "+test[0]
        desc = test[0]
        name = test[1]
        rename = rename_test(name, lang)

        cmd = build_cmd(rename, test[2])

        expected = get_result(test[2])

        test_results = []
        for _ in range(num_retries):
            test_results.append(run_test(expected, cmd))
        
        if all([not r[0] for r in test_results]):
            failed_test_descs += [(desc, e[1], " ".join(cmd)) for e in test_results]
    
    if len(failed_test_descs) == 0:
        print("All tests passed ✅")

    failed_test_descs = [f"{r}:\n{e}\n{cmd}" for r, e, cmd in failed_test_descs]
    assert len(failed_test_descs) == 0, "there were failed test cases:\n======\n" + "\n\n".join(failed_test_descs)