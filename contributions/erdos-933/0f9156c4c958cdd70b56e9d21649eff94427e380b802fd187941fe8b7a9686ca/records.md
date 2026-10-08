# Erdős 933: verified record values of R(n) = 2^k 3^l / (n log n)

Reproduce with `python3 records.py 1500 1000 4`. It needs only plain Python 3 and takes a few
seconds.

The search covers every pair (a, b) with a ≤ 1500, b ≤ 1000 and both orientations. By Lemma 3 of
`reduction.md` it is complete for every n with v₂(n(n+1)) ≤ 1500 and v₃(n(n+1)) ≤ 1000, and in
particular for every n < 10^451. Every row below was re-checked by computing v₂ and v₃ of n(n+1)
directly, and again independently outside the script.

Running records (each row strictly beats every smaller n):

| n | log10 n | v2 | v3 | power of 2 divides | R(n) |
|---|---|---|---|---|---|
| 2 | 0.30 | 1 | 1 | n | 4.328 |
| 1487503359 | 9.17 | 15 | 14 | n+1 | 4.989 |
| 50755272704 | 10.71 | 22 | 13 | n | 5.345 |
| 1092914558009343 | 15.04 | 41 | 11 | n+1 | 10.293 |
| 713412772707958784 | 17.85 | 18 | 32 | n | 16.563 |
| 89241795446991486975 | 19.95 | 30 | 29 | n+1 | 17.975 |
| 3^56 * 50015 | 31.42 | 29 | 56 | n+1 | 148.381 |
| 2^423 * 55 | 129.08 | 423 | 15 | n | 877.798 |

Notes:

* n = 2, 8, 2^27, …, i.e. n = 2^{3^j}, all give exactly 3/log 2 ≈ 4.328 (Steinerberger's
  family). The script ignores these exact ties.
* n = 1487503359 (R ≈ 4.99) was first given by Woett on the erdosproblems.com forum. It refutes
  a claimed uniform bound of 3/log 2.
* 55·2^{423}: here n = 2^{423}·55 and 3^{15} ∣ n + 1. Equivalently, the discrete logarithm of
  −55⁻¹ to base 2 modulo 3^{15} is 423, far below the period 2·3^{14} = 9565938.

Density (distinct n < 10^451, from the same enumeration):

| C | #{n < 10^451 : R(n) > C} | count · C / ln(10^451) |
|---|---|---|
| 4 | 207 | 0.80 |
| 8 | 106 | 0.82 |
| 16 | 51 | 0.79 |
| 32 | 19 | 0.59 |
| 64 | 12 | 0.74 |
| 128 | 7 | 0.86 |

So #{n ≤ X : R(n) > C} ≈ 0.8 · ln X / C, with clean 1/C scaling. Counted over pairs (a, b, side)
instead of distinct n, there are 274 incidences with R > 8 below 10^451. The uniform-residue model
predicts 342. Both are consistent with the CRT residues behaving randomly. In that case the answer
to the problem is yes, and the maximum of R up to X grows like a constant times log X.

This is evidence, not proof. The open step is exactly the criterion proved sufficient in
`script.lean`.
