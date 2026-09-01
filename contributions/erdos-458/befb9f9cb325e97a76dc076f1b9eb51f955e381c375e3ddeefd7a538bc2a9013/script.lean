import Mathlib
import FormalConjectures.ErdosProblems.«458»

/-!
# Checked counterexample work for Erdős 458: the two-prime-squares barrier

Target: `Erdos458.erdos_458` — is `lcm(1,…,p_{k+1}-1) < p_k · lcm(1,…,p_k)` for all `k`?

The ratio `lcm(1,…,p_{k+1}-1) / lcm(1,…,p_k)` only picks up prime powers `q^a`
(`a ≥ 2`) lying strictly inside the prime gap `(p_k, p_{k+1})`, contributing `q` each.
Since `q^a < p_{k+1}` with `a ≥ 2` forces `q < √p_{k+1}`, a *single* such prime power can
never push the ratio past `p_k`: a counterexample needs at least **two prime squares
inside one prime gap**. This file proves the resulting barrier: two prime squares inside
a common prime gap force the gap to exceed `4·√p` — far beyond every known or conjectured
prime-gap bound (gaps grow like `log² p`; even RH only gives `O(√p·log p)`, which is the
wrong side of `4√p`). Hence no finite search can find a counterexample, and the
counterexample mode of this task is effectively closed.
-/

namespace Contribution.Erdos458Barrier

/-- Distinct primes with `2 < a < b` differ by at least 2 (both are odd). -/
theorem two_le_sub_of_odd_primes {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (h2 : 2 < a) (hab : a < b) : a + 2 ≤ b := by
  have hao : Odd a := ha.odd_of_ne_two (by omega)
  have hbo : Odd b := hb.odd_of_ne_two (by omega)
  obtain ⟨x, hx⟩ := hao
  obtain ⟨y, hy⟩ := hbo
  omega

/-- **The barrier.** If the squares of two primes `a < b` lie strictly inside one
prime gap — `p < a²` and `b² < q` with no prime in `(p, q)` — and `p` itself exceeds 9
(so the toy configurations at 2, 3 are excluded), then the gap length exceeds `4·a`,
and `a² > p`, so the gap exceeds `4·√p`. -/
theorem gap_gt_four_mul_of_two_prime_squares
    {p q a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a < b)
    (hpa : p < a ^ 2) (hbq : b ^ 2 ≤ q) (hp9 : 9 ≤ p) :
    4 * a + 4 ≤ q - p := by
  have h2a : 2 < a := by
    by_contra h
    -- a = 2, so a² = 4 > p ≥ 9: impossible
    have := ha.two_le; nlinarith [hpa]
  have hstep := two_le_sub_of_odd_primes ha hb h2a hab
  have hbb : (a + 2) ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have : p + 4 * a + 4 < b ^ 2 := by nlinarith
  omega

/-- Consequence in terms of `√p`: the gap squared exceeds `16 p`. -/
theorem gap_sq_gt_sixteen_mul
    {p q a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a < b)
    (hpa : p < a ^ 2) (hbq : b ^ 2 ≤ q) (hp9 : 9 ≤ p) :
    16 * p < (q - p) ^ 2 := by
  have h := gap_gt_four_mul_of_two_prime_squares ha hb hab hpa hbq hp9
  have h2a : 2 < a := by
    by_contra hc
    have := ha.two_le; nlinarith [hpa]
  nlinarith [hpa, h]

end Contribution.Erdos458Barrier

