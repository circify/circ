def batch_add_inputs(s):
    filename = "scripts/seal_tests/tests/batch_add_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        line1 = ["arr", "a"]
        line2 = ["arr", "b"]
        line3 = ["res"] + [str(s)] * s
        for i in range(s):
            line1.append(str(i))
            line2.append(str(s-i))
        f.write(" ".join(line1) + "\n")
        f.write(" ".join(line2) + "\n")
        f.write(" ".join(line3))    

def batch_mul_inputs(s):
    filename = "scripts/seal_tests/tests/batch_mul_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        line1 = ["arr", "a"]
        line2 = ["arr", "b"]
        line3 = ["res"]
        for i in range(s):
            line1.append(str(i))
            line2.append(str(s-i))
            line3.append(str(i * (s-i)))
        f.write(" ".join(line1) + "\n")
        f.write(" ".join(line2) + "\n")
        f.write(" ".join(line3))

def batch_add_bytecode(s):
    filename = "scripts/seal_tests/tests/batch_add_bytecode_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        f.write("3 1 a 1 " + str(s) + " 1 ARR_IN\n")
        f.write("3 1 b 1 " + str(s) + " 0 ARR_IN\n")
        f.write("2 1 1 0 2 ADD\n")
        f.write("2 0 2 " + str(s) + " ARR_OUT")

def batch_mul_bytecode(s):
    filename = "scripts/seal_tests/tests/batch_mul_bytecode_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        f.write("3 1 a 1 " + str(s) + " 1 ARR_IN\n")
        f.write("3 1 b 1 " + str(s) + " 0 ARR_IN\n")
        f.write("2 1 1 0 2 MUL\n")
        f.write("2 0 2 " + str(s) + " ARR_OUT")

def naive_add_inputs(s):
    filename = "scripts/seal_tests/tests/naive_add_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        lines = []
        for i in range(s):
            lines.append(f"a_{i} {i}")
            lines.append(f"b_{i} {s-i}")
        lines.append(f"res {s}")
        f.write("\n".join(lines))

def naive_mul_inputs(s):
    filename = "scripts/seal_tests/tests/naive_mul_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        lines = []
        for i in range(s):
            lines.append(f"a_{i} {i}")
            lines.append(f"b_{i} {s-i}")
        lines.append("res 0")
        f.write("\n".join(lines))    

def naive_add_bytecode(s):
    filename = "scripts/seal_tests/tests/naive_add_bytecode_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        for i in range(s):
            f.write(f"2 1 a_{i} 1 {2*i} IN\n")
            f.write(f"2 1 b_{i} 1 {2*i + 1} IN\n")
        for i in range(s):
            f.write(f"2 1 {2*i} {2*i + 1} {2*s + i} ADD\n")
        f.write(f"1 0 {2*s} OUT")

def naive_mul_bytecode(s):
    filename = "scripts/seal_tests/tests/naive_mul_bytecode_" + str(s) + ".txt"
    with open(filename, 'w') as f:
        for i in range(s):
            f.write(f"2 1 a_{i} 1 {2*i} IN\n")
            f.write(f"2 1 b_{i} 1 {2*i + 1} IN\n")
        for i in range(s):
            f.write(f"2 1 {2*i} {2*i + 1} {2*s + i} MUL\n")
        f.write(f"1 0 {2*s} OUT")


sizes = [4, 16, 64, 256, 1024]

for s in sizes:
    batch_add_inputs(s)
    batch_mul_inputs(s)
    batch_add_bytecode(s)
    batch_mul_bytecode(s)

    naive_add_inputs(s)
    naive_mul_inputs(s)
    naive_add_bytecode(s)
    naive_mul_bytecode(s)

with open("scripts/seal_tests/tests/code_to_add.txt", "w") as f:
    for s in sizes:
        f.write(f"    run_test(['99'], [\"./../SEAL/build/bin/sealinterpreter -M fhe -b  ./scripts/seal_tests/tests/batch_add_bytecode_{s}.txt -t ./scripts/seal_tests/tests/batch_add_{s}.txt\"], True)\n")
        f.write(f"    run_test(['99'], [\"./../SEAL/build/bin/sealinterpreter -M fhe -b  ./scripts/seal_tests/tests/naive_add_bytecode_{s}.txt -t ./scripts/seal_tests/tests/naive_add_{s}.txt\"], True)\n")
    for s in sizes:
        f.write(f"    run_test(['99'], [\"./../SEAL/build/bin/sealinterpreter -M fhe -b  ./scripts/seal_tests/tests/batch_mul_bytecode_{s}.txt -t ./scripts/seal_tests/tests/batch_mul_{s}.txt\"], True)\n")
        f.write(f"    run_test(['99'], [\"./../SEAL/build/bin/sealinterpreter -M fhe -b  ./scripts/seal_tests/tests/naive_mul_bytecode_{s}.txt -t ./scripts/seal_tests/tests/naive_mul_{s}.txt\"], True)\n")