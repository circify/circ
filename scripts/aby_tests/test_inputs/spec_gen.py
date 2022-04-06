N = 8192

fo = open("biomatch_"+str(N)+".txt", "w")

A = 4 * N
B = 4

input_A = "db "
input_B = "sample "

data_A = []
data_B = []

for i in range(A):
    data_A.append(i)
    if i == A - 1:
        input_A += str(i)
    else:
        input_A += str(i) + " "

for i in range(B):
    data_B.append(i)
    if i == B - 1:
        input_B += str(i)
    else:
        input_B += str(i) + " "       

input_A += "\n"
input_B += "\n"

# biomatch

def match_fix(x1, x2, x3, x4, y1, y2, y3, y4):
    return (x1 - y1)*(x1 - y1) + \
        (x2 - y2)*(x2 - y2) + \
        (x3 - y3)*(x3 - y3) + \
        (x4 - y4)*(x4 - y4)

def biomatch(A, B, N, K):
    res = []
    for i in range(N):
        res.append(match_fix(A[i*K], A[i*K+1], A[i*K+2], A[i*K+3], B[0], B[1], B[2], B[3]))
    return min(res)

fo.write(input_A)
fo.write(input_B)
fo.write("res "+str(biomatch(data_A, data_B, N, 4)))
fo.close()