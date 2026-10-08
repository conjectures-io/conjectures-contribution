# Erdős 933: the exact reduction

Notation. For n ≥ 1 let k(n) = v₂(n(n+1)), l(n) = v₃(n(n+1)), S(n) = 2^{k(n)} 3^{l(n)}
and R(n) = S(n)/(n log n). The formalized task (with `answer(sorry)` set to `True`) is

    True ↔ limsup_{n→∞} (R(n) : EReal) = ⊤.

The pinned body is `↑↑(2^k n * 3^l n) / (↑↑n * ↑(Real.log ↑n))`. Its arithmetic happens in
`EReal` after the leaves are coerced. For n ≥ 2 the value is the coerced real R(n); for n = 0, 1
it is 0, because 0⁻¹ = 0 in `EReal`. So the task is equivalent to

    (★)  for every real C and every N there is n ≥ N with R(n) ≥ C.

`script.lean` proves (★) ⇒ task (`limsup_eq_top_of_frequently_ge`). It also proves that the
divisibility criterion of the Corollary below implies the task (`limsup_eq_top_of_dvd`,
`erdos_933_true_of_dvd`). Lemmas 1–3 and the 3-adic form are proved here on paper and are not
formalized.

## Lemma 1 (the 2-part and the 3-part must split)

Since gcd(n, n+1) = 1, each prime power 2^{k}, 3^{l} exactly dividing n(n+1) divides exactly one
of n and n+1. Suppose both divide the same one. Then S(n) ≤ n+1, so R(n) ≤ (n+1)/(n log n) → 0.
Hence R(n) ≥ 2/log n forces one of two cases:

* (A) n = 2^a u and n+1 = 3^b v, or
* (B) n = 3^b v and n+1 = 2^a u,

where a = v₂ of the even member and b = v₃ of the other one. In both cases u is odd and v is
prime to 3; also u is prime to 3 and v is odd, because 3 and 2 already divide the other member.

## Lemma 2 (exact ratio)

In case (A), S(n) = 2^a 3^b, so

    R(n) = 2^a 3^b / (2^a u · log n) = 3^b / (u · log n),   log n = a log 2 + log u.

Case (B) is symmetric after swapping the roles of 2 and 3:

    R(n) = 2^a / (v · log n),   n = 3^b v.

## Corollary (arithmetic form of the conjecture)

(★) holds iff for every C there are infinitely many triples (a, b, u) with u ≥ 1 and either

* 3^b ∣ 2^a u + 1 and 3^b ≥ C · u · log(2^a u), or
* 2^a ∣ 3^b u + 1 and 2^a ≥ C · u · log(3^b u).

⇐ (the direction formalized in `script.lean`): take n = 2^a u (respectively n = 3^b u). Then
2^a ∣ n(n+1) and 3^b ∣ n(n+1). By `pow_mul_pow_le_smooth`, 2^a 3^b ≤ S(n). The inequality
gives 2^a 3^b ≥ C·n·log n, so R(n) ≥ C.

⇒: apply Lemmas 1 and 2 with the exact valuations.

## Lemma 3 (minimality: why a finite search is complete)

In case (A), n ≡ 0 (mod 2^a), n ≡ −1 (mod 3^b), and n < 2^a 3^b whenever R(n) > 1/log n. So n is
the least positive element of its CRT class:

    n = 2^a · ((−2^{−a}) mod 3^b).

Similarly, in case (B), n + 1 = 2^a · (2^{−a} mod 3^b). So enumerating all (a, b) with a ≤ A,
b ≤ B and both orientations finds every n with R(n) > 1 and v₂ ≤ A, v₃ ≤ B. In particular it
finds every such n < min(2^A, 3^B). This is what `records.py` does.

## Equivalent 3-adic form (proved, not formalized)

For 3 ∤ u put μ(u) = −log₃(u²)/log₃(4) ∈ ℤ₃, using the 3-adic logarithm; v₃(log₃ 4) = 1. Then

    2^a u ≡ ±1 (mod 3^b)   ⇔   a ≡ μ(u) (mod 3^{b−1}).

Proof: (ℤ/3^b)^× is cyclic, so its only square roots of 1 are ±1. Hence 2^a u ≡ ±1 iff
4^a u² ≡ 1 (mod 3^b). log₃ is an isometric isomorphism 1 + 3ℤ₃ → 3ℤ₃, so this holds iff
a·log 4 + log u² ∈ 3^b ℤ₃. Dividing by log 4, which has valuation 1, gives
a − μ(u) ∈ 3^{b−1} ℤ₃.

Consequently, in case (A), R ≥ C at level b iff μ(u) mod 3^{b−1} ≤ 3^b/(C·u·log n). That is,
the ternary digits of μ(u) in positions b−1−log₃(Cu)−O(1) through b−2 are all 0. So:

> (★) ⇔ for every K some integer u has a zero block of length ≥ log₃ u + K in the ternary
> expansion of μ(u).

For any fixed u this is a normality-type statement about one specific 3-adic number. The
forum heuristics (see `sources.md`) assume it. The record R(55·2^{423}) ≈ 877.8 corresponds to the
8-zero block of μ(55) in positions 6–13.
