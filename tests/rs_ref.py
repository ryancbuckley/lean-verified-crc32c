#!/usr/bin/env python3
"""Independent reference for the Reed-Solomon prototype: the Backblaze
JavaReedSolomon / klauspost construction (Vandermonde matrix r^c over GF(2^8)
with polynomial 0x11D, multiplied by the inverse of its top k x k block).
Reads `bench_rs vectors` lines on stdin and checks the parity."""
import sys

EXP = [0] * 510
LOG = [0] * 256
x = 1
for i in range(255):
    EXP[i] = x
    LOG[x] = i
    x <<= 1
    if x & 0x100:
        x ^= 0x11D
for i in range(255, 510):
    EXP[i] = EXP[i - 255]

def mul(a, b):
    return 0 if a == 0 or b == 0 else EXP[LOG[a] + LOG[b]]

def inv(a):
    return EXP[255 - LOG[a]]

def gpow(a, n):
    if n == 0:
        return 1
    return 0 if a == 0 else EXP[(LOG[a] * n) % 255]

def matmul(A, B):
    return [[__import__("functools").reduce(lambda s, t: s ^ t, (mul(A[i][l], B[l][j]) for l in range(len(B))), 0)
             for j in range(len(B[0]))] for i in range(len(A))]

def invert(M):
    n = len(M)
    A = [row[:] + [1 if i == j else 0 for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c])
        A[c], A[p] = A[p], A[c]
        s = inv(A[c][c])
        A[c] = [mul(v, s) for v in A[c]]
        for r in range(n):
            if r != c and A[r][c]:
                f = A[r][c]
                A[r] = [v ^ mul(f, w) for v, w in zip(A[r], A[c])]
    return [row[n:] for row in A]

def encode_matrix(k, n):
    V = [[gpow(r, c) for c in range(k)] for r in range(n)]
    return matmul(V, invert(V[:k]))

ok = 0
for line in sys.stdin:
    k, m, L, dh, ph = line.split()
    k, m, L = int(k), int(m), int(L)
    data, par = bytes.fromhex(dh), bytes.fromhex(ph)
    E = encode_matrix(k, k + m)
    assert E[:k] == [[1 if i == j else 0 for j in range(k)] for i in range(k)]
    for j in range(m):
        for w in range(L):
            v = 0
            for i in range(k):
                v ^= mul(E[k + j][i], data[i * L + w])
            if v != par[j * L + w]:
                sys.exit(f"MISMATCH k={k} m={m} L={L} row={j} byte={w}")
    ok += 1
print(f"parity matches the Vandermonde-construction reference on {ok} configurations")
