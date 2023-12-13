#!/usr/bin/env python

from math import log2


def cost_gcd_uniq(N: int, r: int) -> (int, str):
    return 6 * N, ""


def cost_bitsplit(N: int, r: int) -> (int, str):
    return r * N, ""


def cost_sort(N: int, r: int) -> (int, str):
    return 3 * (2**r + N), ""


def cost_subbitsplit(N: int, r: int) -> (int, str):
    def cost_subbitsplit_window(N: int, r: int, k: int) -> int:
        blocks = r // k
        remainder = r - blocks * k
        return 3 * 2**k + min(
            3 * N * blocks + N * remainder,  # bitsplit remainder
            3 * N * (blocks + 2),  # double-window remainder
        )

    cost, _, k = min([(cost_subbitsplit_window(N, r, k), -k, k) for k in range(1, r + 1)])
    return cost, f"{k}"


print("log2_accesses,addr_bits,name,cost,k")
for r in range(4, 65):
    for N in [2**i for i in range(0, 21, 3)]:
        for f in [cost_bitsplit, cost_sort, cost_subbitsplit, cost_gcd_uniq]:
            name = f.__name__.removeprefix("cost_")
            cost, note = f(N, r)
            log2N = int(log2(N))
            print(f"{log2N},{r},{name},{float(cost)},{note}")
