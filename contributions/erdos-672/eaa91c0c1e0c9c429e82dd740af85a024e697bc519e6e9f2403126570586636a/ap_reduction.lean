import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Module.NatInt

/-!
# General Coprime-AP Diophantine Reduction Framework (Erdős Problem #672)

Develops the general structural reduction for Erdős Problem #672:
given a coprime arithmetic progression `n, n + d, ..., n + (k - 1) * d` (`n, d > 0`,
`Nat.Coprime n d`) whose product equals an `l`-th power `q ^ l` (`l > 1`), proves:
1. Pairwise gcd divisibility: `Nat.gcd (n + i * d) (n + j * d) ∣ (j - i)` for `i < j`.
2. Unique-term prime divisibility: every prime `p ≥ k` divides at most one term.
3. Exact `p`-adic exponent divisibility: `l ∣ padicValNat p (n + i * d)` for all primes `p ≥ k`.
4. Canonical decomposition `n + i * d = a * x ^ l` where every prime factor of `a` is `< k`
   and `padicValNat p a < l` for all primes `p`.
5. Exact bridge theorems matching the expanded form of `Erdos672.Erdos672With k l`.
-/

namespace Contribution.Erdos672APReduction

theorem ap_term_pos {n d : ℕ} (hn : 0 < n) (i : ℕ) : 0 < n + i * d := by
  omega

/-- For `Nat.Coprime n d` and `i < j`, `Nat.gcd (n + i * d) (n + j * d)` divides `j - i`,
independent of `n` and `d`. -/
theorem ap_pairwise_gcd_dvd {n d i j : ℕ} (hcop : Nat.Coprime n d) (hij : i < j) :
    Nat.gcd (n + i * d) (n + j * d) ∣ (j - i) := by
  set g := Nat.gcd (n + i * d) (n + j * d)
  have hgi : g ∣ n + i * d := Nat.gcd_dvd_left _ _
  have hgj : g ∣ n + j * d := Nat.gcd_dvd_right _ _
  have hdiff : n + j * d = (n + i * d) + (j - i) * d := by
    have hle : i ≤ j := Nat.le_of_lt hij
    calc
      n + j * d = n + (i + (j - i)) * d := by rw [Nat.add_sub_cancel' hle]
      _ = (n + i * d) + (j - i) * d := by ring
  have hgd : g ∣ (j - i) * d := by
    rw [hdiff] at hgj
    exact (Nat.dvd_add_right hgi).mp hgj
  have hcop_gd : Nat.Coprime g d := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have hc_n : Nat.gcd g d ∣ n :=
      (Nat.dvd_add_left (dvd_mul_of_dvd_right (Nat.gcd_dvd_right g d) i)).mp
        (dvd_trans (Nat.gcd_dvd_left g d) hgi)
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hc_n (Nat.gcd_dvd_right g d))
  exact hcop_gd.dvd_of_dvd_mul_right hgd

/-- Any prime `p ≥ k` divides at most one term among `n + 0*d, ..., n + (k-1)*d`. -/
theorem ap_prime_unique_term {n d k p i j : ℕ} (hcop : Nat.Coprime n d) (hp : p.Prime)
    (hpk : k ≤ p) (hi : i < k) (hj : j < k)
    (hpi : p ∣ n + i * d) (hpj : p ∣ n + j * d) : i = j := by
  have _ := hp.pos
  by_contra hne
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · have hpd : p ∣ j - i :=
      dvd_trans (Nat.dvd_gcd hpi hpj) (ap_pairwise_gcd_dvd hcop hij)
    have hle : p ≤ j - i := Nat.le_of_dvd (Nat.sub_pos_of_lt hij) hpd
    omega
  · exact hne rfl
  · have hpd : p ∣ i - j :=
      dvd_trans (Nat.dvd_gcd hpj hpi) (ap_pairwise_gcd_dvd hcop hji)
    have hle : p ≤ i - j := Nat.le_of_dvd (Nat.sub_pos_of_lt hji) hpd
    omega

private theorem padicValNat_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    {p : ℕ} [Fact p.Prime] (hf : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (∏ x ∈ s, f x) = ∑ x ∈ s, padicValNat p (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : ∀ x ∈ s, f x ≠ 0 := fun x hx => hf x (Finset.mem_insert_of_mem hx)
    have hprod0 : ∏ x ∈ s, f x ≠ 0 := Finset.prod_ne_zero_iff.mpr hs0
    rw [Finset.prod_insert ha, Finset.sum_insert ha, padicValNat.mul ha0 hprod0, ih hs0]

/-- If `∏_{j < k} (n + j * d) = q ^ l` with `Nat.Coprime n d` and `n > 0`, then for every
prime `p ≥ k` and every `i < k`, `l ∣ padicValNat p (n + i * d)`. -/
theorem ap_padicValNat_dvd_of_prod_eq_pow {n d k l q p i : ℕ}
    (hn : 0 < n) (hcop : Nat.Coprime n d) (hp : p.Prime) (hpk : k ≤ p) (hi : i < k)
    (hprod : ∏ j ∈ Finset.range k, (n + j * d) = q ^ l) :
    l ∣ padicValNat p (n + i * d) := by
  have : Fact p.Prime := ⟨hp⟩
  by_cases hdiv : p ∣ n + i * d
  · have hne : ∀ j ∈ Finset.range k, n + j * d ≠ 0 := fun j _ => by omega
    have hsum : ∑ j ∈ Finset.range k, padicValNat p (n + j * d) = padicValNat p (n + i * d) := by
      refine Finset.sum_eq_single i ?_ ?_
      · intro j hj hji
        have hjlt : j < k := Finset.mem_range.mp hj
        have hnot : ¬ p ∣ n + j * d := by
          intro hdj
          exact hji (ap_prime_unique_term hcop hp hpk hjlt hi hdj hdiv)
        exact padicValNat.eq_zero_of_not_dvd hnot
      · intro hi_mem
        exact absurd (Finset.mem_range.mpr hi) hi_mem
    have hpow : padicValNat p (∏ j ∈ Finset.range k, (n + j * d)) = l * padicValNat p q := by
      rw [hprod, padicValNat.pow]
    rw [padicValNat_finset_prod (Finset.range k) (fun j => n + j * d) hne, hsum] at hpow
    exact ⟨padicValNat p q, hpow⟩
  · rw [padicValNat.eq_zero_of_not_dvd hdiv]
    exact dvd_zero l

/-- Canonical decomposition of every term `n + i * d` when `∏_{j < k} (n + j * d) = q ^ l`:
`n + i * d = a * x ^ l` where every prime factor of `a` is strictly less than `k`
and `a` is `l`-th power free (`padicValNat p a < l` for all primes `p`). -/
theorem ap_canonical_factor_splitting {n d k l q i : ℕ}
    (hn : 0 < n) (hl : 1 < l) (hcop : Nat.Coprime n d) (hi : i < k)
    (hprod : ∏ j ∈ Finset.range k, (n + j * d) = q ^ l) :
    ∃ a x : ℕ, 0 < a ∧ 0 < x ∧ n + i * d = a * x ^ l ∧
      (∀ p : ℕ, p.Prime → p ∣ a → p < k) ∧
      (∀ p : ℕ, p.Prime → padicValNat p a < l) := by
  classical
  set m := n + i * d
  have hm0 : m ≠ 0 := by omega
  set a := ∏ p ∈ m.primeFactors, p ^ (m.factorization p % l)
  set x := ∏ p ∈ m.primeFactors, p ^ (m.factorization p / l)
  have ha_pos : 0 < a :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hx_pos : 0 < x :=
    Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hl_pos : 0 < l := by omega
  have ha_mul_x : n + i * d = a * x ^ l := by
    calc
      n + i * d = m := rfl
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p) :=
        Nat.prod_primeFactors_pow_factorization hm0
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p % l + l * (m.factorization p / l)) := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [Nat.mod_add_div]
      _ = ∏ p ∈ m.primeFactors, p ^ (m.factorization p % l) * (p ^ (m.factorization p / l)) ^ l := by
        refine Finset.prod_congr rfl fun p _ => ?_
        rw [pow_add, mul_comm l (m.factorization p / l), pow_mul]
      _ = (∏ p ∈ m.primeFactors, p ^ (m.factorization p % l)) *
            (∏ p ∈ m.primeFactors, (p ^ (m.factorization p / l)) ^ l) :=
        Finset.prod_mul_distrib
      _ = a * x ^ l := by rw [Finset.prod_pow]
  have ha_fact : ∀ p : ℕ, a.factorization p = if p ∈ m.primeFactors then m.factorization p % l else 0 := by
    intro p
    have hp_nz : ∀ r ∈ m.primeFactors, r ^ (m.factorization r % l) ≠ 0 := fun r hr =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hr).ne_zero
    change (∏ r ∈ m.primeFactors, r ^ (m.factorization r % l)).factorization p = _
    rw [Nat.factorization_prod hp_nz, Finsupp.coe_finsetSum, Finset.sum_apply]
    by_cases hp : p ∈ m.primeFactors
    · rw [if_pos hp]
      rw [Finset.sum_eq_single p]
      · exact (Nat.prime_of_mem_primeFactors hp).factorization_pow ▸ by simp
      · intro r hr hrp
        have hpr := Nat.prime_of_mem_primeFactors hr
        rw [hpr.factorization_pow, Finsupp.single_apply, if_neg hrp]
      · intro h; exact absurd hp h
    · rw [if_neg hp]
      refine Finset.sum_eq_zero fun r hr => ?_
      have hpr := Nat.prime_of_mem_primeFactors hr
      have hrp : r ≠ p := fun heq => hp (heq ▸ hr)
      rw [hpr.factorization_pow, Finsupp.single_apply, if_neg hrp]
  refine ⟨a, x, ha_pos, hx_pos, ha_mul_x, ?_, ?_⟩
  · intro p hp hpa
    by_contra hge
    have hpk : k ≤ p := Nat.le_of_not_lt hge
    have hdvd : l ∣ padicValNat p m :=
      ap_padicValNat_dvd_of_prod_eq_pow hn hcop hp hpk hi hprod
    have hmod : m.factorization p % l = 0 := by
      rw [Nat.factorization_def m hp]
      exact Nat.mod_eq_zero_of_dvd hdvd
    have haf0 : a.factorization p = 0 := by
      rw [ha_fact p]
      split_ifs <;> simp [hmod]
    have haf_pos : 0 < a.factorization p := hp.factorization_pos_of_dvd ha_pos.ne' hpa
    omega
  · intro p hp
    rw [← Nat.factorization_def a hp, ha_fact p]
    split_ifs
    · exact Nat.mod_lt _ hl_pos
    · exact hl_pos

/-- Equivalence between `Set.IsAPOfLengthWith` (expanded cleanly without importing FormalConjectures)
and the image of `Finset.range k`. -/
theorem finset_ap_eq_image_range {s : Finset ℕ} {k n d : ℕ} (_hd : 0 < d)
    (hap : ENat.card (s : Set ℕ) = (k : ℕ∞) ∧
      (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (k : ℕ∞))}) :
    s = (Finset.range k).image (fun i => n + i * d) := by
  ext x
  have hmem_set : x ∈ (s : Set ℕ) ↔ ∃ i : ℕ, (i : ℕ∞) < (k : ℕ∞) ∧ n + i • d = x := by
    rw [hap.2]
    simp only [Set.mem_ofPred_eq, exists_prop]
  rw [Finset.mem_coe] at hmem_set
  rw [hmem_set, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, Finset.mem_range.mpr (ENat.natCast_lt_natCast.mp hi), ?_⟩
    simp only [smul_eq_mul]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i, ENat.natCast_lt_natCast.mpr (Finset.mem_range.mp hi), ?_⟩
    simp only [smul_eq_mul]

/-- The product over `s` equals `∏ i ∈ Finset.range k, (n + i * d)`. -/
theorem finset_ap_prod_eq_range_prod {s : Finset ℕ} {k n d : ℕ} (hd : 0 < d)
    (hap : ENat.card (s : Set ℕ) = (k : ℕ∞) ∧
      (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (k : ℕ∞))}) :
    ∏ x ∈ s, x = ∏ i ∈ Finset.range k, (n + i * d) := by
  rw [finset_ap_eq_image_range hd hap, Finset.prod_image]
  intro i _ j _ hij
  exact Nat.mul_right_cancel hd (Nat.add_left_cancel hij)

/-- Bridge theorem connecting the expanded `Erdos672.Erdos672With` predicate to
canonical prime-bounded factor splitting on `[0, k)`. -/
theorem erdos_672_reduction_bridge {s : Finset ℕ} {k l n d q : ℕ}
    (_hk : s.card = k) (hn : 0 < n) (hd : 0 < d) (hl : 1 < l) (hcop : n.gcd d = 1)
    (hap : ENat.card (s : Set ℕ) = (k : ℕ∞) ∧
      (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (k : ℕ∞))})
    (hprod : ∏ x ∈ s, x = q ^ l) :
    ∀ i < k, ∃ a x : ℕ, 0 < a ∧ 0 < x ∧ n + i * d = a * x ^ l ∧
      (∀ p : ℕ, p.Prime → p ∣ a → p < k) ∧
      (∀ p : ℕ, p.Prime → padicValNat p a < l) := by
  have hprod_range : ∏ j ∈ Finset.range k, (n + j * d) = q ^ l := by
    rw [← finset_ap_prod_eq_range_prod hd hap]
    exact hprod
  intro i hi
  exact ap_canonical_factor_splitting hn hl hcop hi hprod_range

/-- Monotonicity in the exponent: if no `k`-term coprime AP product is an `l`-th power,
then none is an `(l * m)`-th power for `0 < m`. -/
theorem erdos_672_pow_mul_monotone {k l m : ℕ} (_hm : 0 < m)
    (h : ∀ (s : Finset ℕ), s.card = k → ∀ (n : ℕ), n > 0 → ∀ (d : ℕ), d > 0 → n.gcd d = 1 →
      (ENat.card (s : Set ℕ) = (k : ℕ∞) ∧
        (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (k : ℕ∞))}) →
      ∀ q, ∏ i ∈ s, i ≠ q ^ l) :
    ∀ (s : Finset ℕ), s.card = k → ∀ (n : ℕ), n > 0 → ∀ (d : ℕ), d > 0 → n.gcd d = 1 →
      (ENat.card (s : Set ℕ) = (k : ℕ∞) ∧
        (s : Set ℕ) = {n + i • d | (i : ℕ) (_ : (i : ℕ∞) < (k : ℕ∞))}) →
      ∀ q, ∏ i ∈ s, i ≠ q ^ (l * m) := by
  intro s hs n hn d hd hcop hap q heq
  apply h s hs n hn d hd hcop hap (q ^ m)
  rw [heq, pow_mul']

end Contribution.Erdos672APReduction
