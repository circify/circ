import os 
from subprocess import Popen, PIPE
import sys
from typing import List

def init_progress_bar(toolbar_width=40):
    """ Initialize progress bar """
    sys.stdout.write("[%s]" % ("." * toolbar_width))
    sys.stdout.flush()
    sys.stdout.write("\b" * (toolbar_width+1)) 

def update_progress_bar():
    """ Increment progress bar """
    sys.stdout.write("#")
    sys.stdout.flush()

def end_progress_bar():
    """ Close progress bar """
    sys.stdout.write("]\n") # this ends the progress bar

def rename_test(name: str, lang: str) -> str:
    """Append path with language type"""
    return f"{name}_{lang}"

def build_cmd(name:str, test_file: str, role: int) -> List[str]:
    bytecode = f"./scripts/aby_tests/tests/{name}_bytecode.txt"
    share_map = f"./scripts/aby_tests/tests/{name}_share_map.txt"
    param_map= f"./scripts/aby_tests/tests/{name}_param_map.txt"
    return [os.getenv("ABY_SOURCE") + "/build/bin/aby_interpreter", "-M", "mpc", "-R", str(role), "-b", bytecode, "-t", test_file, "-s", share_map, "-p", param_map] 

def get_result(file_path):
    if os.path.exists(file_path):
        with open(file_path) as f:
            lines = f.read().splitlines()
            res_flag = False
            res = []
            for l in lines:
                l = l.strip()
                if not l: continue
                if res_flag:
                    res.append(l)
                if l.startswith("//") and "result" in l:
                    res_flag = True
                elif l.startswith("//"):
                    res_flag = False
            return "\n".join(res)
    else:
        raise RuntimeError("Unable to open file: "+file_path)


def run_test(expected: str, server_cmd: List[str], client_cmd: List[str]) -> bool:
    assert server_cmd[0] == client_cmd[0], "server and client do not have the same cmd: " + server_cmd[0] + ", " + client_cmd[0]
    
    try:
        server_proc = Popen(" ".join(server_cmd), shell=True, stdout=PIPE, stderr=PIPE)
        client_proc = Popen(" ".join(client_cmd), shell=True, stdout=PIPE, stderr=PIPE)

        server_out, server_err = server_proc.communicate(timeout=30)
        client_out, client_err = client_proc.communicate(timeout=30)

        if server_err:
            raise RuntimeError("Server error: "+server_err.decode("utf-8").strip())
        if client_err:
            raise RuntimeError("Client error: "+client_err.decode("utf-8").strip())

        server_out = server_out.decode("utf-8").strip()
        client_out = client_out.decode("utf-8").strip()

        assert server_out == client_out, "server out != client out\nserver_out: "+server_out+"\nclient_out: "+client_out
        assert server_out == expected, "server_out: "+server_out+"\nexpected: "+expected
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
    print(f"Running ABY tests for {lang} frontend")
    failed_test_descs = []
    num_retries = 2
    progress_inc = 5
    init_progress_bar(len(tests) // progress_inc + 1)
    for t, test in enumerate(tests):
        assert len(test) == 3, "test configurations are wrong for test: "+test[0]
        desc = test[0]
        name = test[1]
        rename = rename_test(name, lang)

        server_cmd = build_cmd(rename, test[2], 0)
        client_cmd = build_cmd(rename, test[2], 1)

        expected = get_result(test[2])

        test_results = []
        for _ in range(num_retries):
            test_results.append(run_test(expected, server_cmd, client_cmd))
        
        if all([not r[0] for r in test_results]):
            failed_test_descs += [(desc, e[1], " ".join(server_cmd)) for e in test_results]

        if t % progress_inc == 0:
            update_progress_bar()
    end_progress_bar()
    
    if len(failed_test_descs) == 0:
        print("All tests passed ✅")

    failed_test_descs = [f"{r}:\n{e}\n{cmd}" for r, e, cmd in failed_test_descs]
    assert len(failed_test_descs) == 0, "there were failed test cases:\n======\n" + "\n\n".join(failed_test_descs)