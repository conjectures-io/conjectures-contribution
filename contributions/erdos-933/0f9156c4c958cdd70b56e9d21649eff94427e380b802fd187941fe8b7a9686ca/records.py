#!/usr/bin/env python3
"""Record values of R(n) = 2^k 3^l / (n log n) for Erdos problem 933.

Here k = v2(n(n+1)) and l = v3(n(n+1)). Usage: python3 records.py [A] [B] [THR]
(defaults 1500 1000 8). Plain Python 3, no dependencies, deterministic.

Why the search is complete. If R(n) > 2/log n, then 2^k and 3^l divide different members
of {n, n+1} (reduction.md, Lemma 1). Then n is the least positive element of its residue
class mod 2^k 3^l, because n < 2^k 3^l. So enumerating every (a, b) with a <= A, b <= B and
both orientations finds every n with R(n) > THR whose exact valuations satisfy v2 <= A and
v3 <= B. That covers every n < min(2^A, 3^B), and in particular every n < 10^451 for the
defaults.

Orientation 1: n = 2^a u and 3^b | n+1, with u = (-2^-a) mod 3^b.
Orientation 2: n+1 = 2^a u and 3^b | n, with u = (2^-a) mod 3^b.
In both cases the candidate ratio is 3^b / (u * log n), and every candidate above THR is
re-checked by computing v2 and v3 of n(n+1) directly.
"""
import math
import sys


def val(p, x):
    c = 0
    while x % p == 0:
        x //= p
        c += 1
    return c


def exact_ratio(n):
    m = n * (n + 1)
    k, l = val(2, m), val(3, m)
    log_s = k * math.log(2) + l * math.log(3)
    return math.exp(log_s - math.log(n)) / math.log(n), k, l


def main():
    A = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    B = int(sys.argv[2]) if len(sys.argv) > 2 else 1000
    thr = float(sys.argv[3]) if len(sys.argv) > 3 else 8.0
    ln2 = math.log(2)
    cand = {}
    for b in range(1, B + 1):
        M = 3 ** b
        t = 1
        for a in range(1, A + 1):
            t = t >> 1 if t % 2 == 0 else (t + M) >> 1        # t = 2^(-a) mod 3^b
            for orient, u in ((1, M - t), (2, t)):
                if u * a * 69 * int(thr) >= M * 100:          # cheap filter: ratio < thr
                    continue
                lu = math.log(u)
                if math.exp(b * math.log(3) - lu) / (a * ln2 + lu) > thr:
                    n = (u << a) if orient == 1 else (u << a) - 1
                    if n > 1:
                        cand[n] = orient
    hits = []
    for n in cand:
        r, k, l = exact_ratio(n)
        if r > thr:
            hits.append((n, r, k, l))
    hits.sort()
    print(f"# search box: v2 <= {A}, v3 <= {B}; hits with R(n) > {thr}: {len(hits)}")
    print("| n | log10 n | v2 | v3 | power of 2 divides | R(n) |")
    print("|---|---|---|---|---|---|")
    best = 0.0
    for n, r, k, l in hits:
        if r > best * (1 + 1e-9):          # ignore float ties, e.g. R(2^(3^j)) = 3/log 2
            best = r
            side = "n" if n % 2 == 0 else "n+1"
            if n < 10 ** 20:
                shown = str(n)
            elif side == "n":
                shown = f"2^{k} * {n >> k}"
            else:
                shown = f"3^{l} * {n // 3 ** l}"
            print(f"| {shown} | {math.log10(n):.2f} | {k} | {l} | {side} | {r:.3f} |")
    per = {}
    for n, r, k, l in hits:
        d = int(math.log10(n)) // 100
        per[d] = per.get(d, 0) + 1
    print("hits per 100 decades of log10 n:", sorted(per.items()))


if __name__ == "__main__":
    main()
