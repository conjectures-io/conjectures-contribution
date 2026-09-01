/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjectures.ErdosProblems.«141»

/-!
# Erdős Problem 141: the first cases `3 ≤ k ≤ 10` are solved

We prove `erdos_141.variants.first_cases`: for every `3 ≤ k ≤ 10` there exist `k`
consecutive primes in arithmetic progression.

A single witness suffices for all eight cases: the CPAP-10 discovered by Manfred Toplic
in the CP10 project (Dubner, Forbes, Lygeros, Mizony, Nelson, Zimmermann,
*Ten consecutive primes in arithmetic progression*, Math. Comp. 71 (2002), 1323–1328).
Its ten primes are `P + 210 * n` for `n = 0, …, 9` where

`P = 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719`.

The first `k` of these ten consecutive primes form `k` consecutive primes in arithmetic
progression, for every `k ≤ 10`.

The proof is fully certified inside Lean:

* primality of the ten 93-digit primes (and of all large prime factors appearing in the
  recursive certificate tree, 146 numbers in total) is proved via Pratt/Lucas certificates
  using Mathlib's `lucas_primality`, with modular exponentiation performed by a
  kernel-reducible divide-and-conquer function `pw` (recursion depth logarithmic in the
  exponent's bit length, so `decide +kernel` can evaluate it);
* compositeness of all `209 × 9 = 1881` numbers strictly between consecutive members of
  the progression is certified either by an explicit factor or by a Fermat test
  `2 ^ (n - 1) % n ≠ 1`;
* the bookkeeping connecting these certificates to `Nat.nth Nat.Prime` (the `n`-th prime)
  is handled by the prime-counting function `Nat.count`.
-/

namespace Contribution.Erdos141FirstCases

open Nat Erdos141

/-- Modular exponentiation `b ^ e % n`, computable by kernel reduction with recursion
depth logarithmic in the bit-length of `e`: at fuel `f` the exponent is split as
`e = hi * 2 ^ 2 ^ f + lo`. The result is valid for `e ≤ 2 ^ 2 ^ f` (see `pw_eq`). -/
def pw (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, b, e => if e = 0 then 1 % n else if e = 1 then b % n else b * b % n
  | f+1, b, e =>
    if e = 0 then 1 % n else if e = 1 then b % n
    else pw n f (pw n f b (2 ^ 2 ^ f)) (e / 2 ^ 2 ^ f) * pw n f b (e % 2 ^ 2 ^ f) % n

/-- `pw` computes modular exponentiation. -/
theorem pw_eq (n : ℕ) : ∀ f b e : ℕ, e ≤ 2 ^ 2 ^ f → pw n f b e = b ^ e % n := by
  intro f
  induction f with
  | zero =>
    intro b e he
    norm_num at he
    interval_cases e
    · simp [pw]
    · simp [pw]
    · simp [pw, pow_two]
  | succ f ih =>
    intro b e he
    by_cases h0 : e = 0
    · simp [pw, h0]
    by_cases h1 : e = 1
    · simp [pw, h1]
    have hh : (0:ℕ) < 2 ^ 2 ^ f := Nat.two_pow_pos _
    have hsq : (2:ℕ) ^ 2 ^ (f+1) = 2 ^ 2 ^ f * 2 ^ 2 ^ f := by
      rw [← pow_add]
      congr 1
      rw [pow_succ]
      ring
    have hdiv : e / 2 ^ 2 ^ f ≤ 2 ^ 2 ^ f := by
      calc e / 2 ^ 2 ^ f ≤ 2 ^ 2 ^ f * 2 ^ 2 ^ f / 2 ^ 2 ^ f :=
            Nat.div_le_div_right (hsq ▸ he)
        _ = 2 ^ 2 ^ f := Nat.mul_div_cancel_left _ hh
    have hmod : e % 2 ^ 2 ^ f ≤ 2 ^ 2 ^ f := (Nat.mod_lt _ hh).le
    show pw n (f+1) b e = b ^ e % n
    rw [pw]
    rw [if_neg h0, if_neg h1]
    rw [ih b (2 ^ 2 ^ f) le_rfl]
    rw [ih _ _ hdiv, ih b _ hmod]
    rw [← Nat.pow_mod, ← pow_mul, ← Nat.mul_mod, ← pow_add]
    rw [Nat.div_add_mod e (2 ^ 2 ^ f)]

/-- Lucas primality certificate checker: `l` lists all prime factors of `p - 1`
with multiplicity and `a` is a witness of order `p - 1`. -/
theorem prime_of_lucas (p a : ℕ) (l : List ℕ) (hp : 1 < p)
    (hfac : p - 1 = l.prod)
    (hlt : p - 1 ≤ 2 ^ 2 ^ 9)
    (hl : ∀ q ∈ l, q.Prime)
    (ha : pw p 9 a (p - 1) = 1)
    (hd : ∀ q ∈ l, pw p 9 a ((p - 1) / q) ≠ 1) : p.Prime := by
  haveI : Fact (1 < p) := ⟨hp⟩
  haveI : NeZero p := ⟨by omega⟩
  have hcast : ∀ e : ℕ, e ≤ 2 ^ 2 ^ 9 → ((a : ZMod p) ^ e = 1 ↔ pw p 9 a e = 1) := by
    intro e helt
    rw [pw_eq p 9 a e helt]
    constructor
    · intro h
      have hc : ((a ^ e % p : ℕ) : ZMod p) = 1 := by
        rw [ZMod.natCast_mod, Nat.cast_pow, h]
      calc a ^ e % p
          = ((a ^ e % p : ℕ) : ZMod p).val :=
            (ZMod.val_cast_of_lt (Nat.mod_lt _ (by omega))).symm
        _ = (1 : ZMod p).val := by rw [hc]
        _ = 1 := ZMod.val_one p
    · intro h
      have hc : ((a ^ e % p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by rw [h]
      rw [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one] at hc
      exact hc
  apply lucas_primality p (a : ZMod p)
  · exact (hcast _ hlt).2 ha
  · intro q hq hqdvd
    have hmem : q ∈ l := by
      have hdvd' : q ∣ l.prod := hfac ▸ hqdvd
      obtain ⟨x, hxl, hqx⟩ := (Prime.dvd_prod_iff hq.prime).1 hdvd'
      rwa [(Nat.prime_dvd_prime_iff_eq hq (hl x hxl)).1 hqx]
    intro hcontra
    exact hd q hmem ((hcast _ ((Nat.div_le_self _ _).trans hlt)).1 hcontra)

/-- Fermat compositeness certificate: if `2 ^ (n - 1) % n ≠ 1` then `n` is not prime. -/
theorem not_prime_of_fermat (n : ℕ) (h2 : 2 < n) (hlt : n - 1 ≤ 2 ^ 2 ^ 9)
    (h : pw n 9 2 (n - 1) ≠ 1) : ¬ n.Prime := by
  intro hp
  haveI : Fact (1 < n) := ⟨by omega⟩
  haveI : Fact n.Prime := ⟨hp⟩
  have h2z : (2 : ZMod n) ≠ 0 := by
    intro hz
    have hv : ((2 : ℕ) : ZMod n).val = (0 : ZMod n).val := by
      rw [show ((2 : ℕ) : ZMod n) = (2 : ZMod n) from by push_cast; ring, hz]
    rw [ZMod.val_cast_of_lt h2, ZMod.val_zero] at hv
    omega
  have hfl : (2 : ZMod n) ^ (n - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2z
  apply h
  rw [pw_eq n 9 2 (n-1) hlt]
  have hc : (((2:ℕ) ^ (n-1) % n : ℕ) : ZMod n) = 1 := by
    rw [ZMod.natCast_mod, Nat.cast_pow]
    push_cast
    exact hfl
  calc (2:ℕ) ^ (n-1) % n
      = (((2:ℕ) ^ (n-1) % n : ℕ) : ZMod n).val :=
        (ZMod.val_cast_of_lt (Nat.mod_lt _ (by omega))).symm
    _ = (1 : ZMod n).val := by rw [hc]
    _ = 1 := ZMod.val_one n

/-- Compositeness from an explicit factorization. -/
theorem not_prime_of_factor {n : ℕ} (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (h : n = a * b) : ¬ n.Prime := by
  subst h
  exact Nat.not_prime_mul (by omega) (by omega)

/-- An empty open interval contains no primes. -/
theorem gap_nil (k : ℕ) : ∀ m, k < m → m < k + 1 → ¬ m.Prime := by
  intro m h1 h2
  omega

/-- Extend a prime-free open interval downward by one composite element. -/
theorem gap_cons {k t : ℕ} (hj : ¬ (k + 1).Prime)
    (rest : ∀ m, k + 1 < m → m < t → ¬ m.Prime) :
    ∀ m, k < m → m < t → ¬ m.Prime := by
  intro m h1 h2
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt h1) with he | hlt
  · rwa [← he]
  · exact rest m hlt h2

/-- If `p` is prime and everything strictly between `p` and `q` is composite, then the
prime count at `q` is one more than at `p`. -/
theorem count_succ_of_gap {p q : ℕ} (hp : p.Prime) (hpq : p < q)
    (h : ∀ m, p < m → m < q → ¬ m.Prime) :
    Nat.count Nat.Prime q = Nat.count Nat.Prime p + 1 := by
  classical
  have key : ∀ r, p < r → r ≤ q → Nat.count Nat.Prime r = Nat.count Nat.Prime p + 1 := by
    intro r
    induction r with
    | zero => omega
    | succ r ihr =>
      intro h1 h2
      rcases Nat.lt_or_ge p r with hpr | hpr
      · rw [Nat.count_succ, ihr hpr (by omega), if_neg (h r hpr (by omega))]
      · have hpr' : p = r := by omega
        subst hpr'
        rw [Nat.count_succ, if_pos hp]
  exact key q hpq le_rfl

/-- Along a chain of consecutive primes in arithmetic progression the prime-counting
function increments by exactly one per step. -/
theorem count_chain (p d k : ℕ)
    (hprimes : ∀ i, i < k → (p + i * d).Prime)
    (hgaps : ∀ i, i + 1 < k → ∀ m, p + i * d < m → m < p + (i + 1) * d → ¬ m.Prime)
    (hd : 0 < d) :
    ∀ n, n < k → Nat.count Nat.Prime (p + n * d) = Nat.count Nat.Prime p + n := by
  intro n
  induction n with
  | zero => simp
  | succ n ihn =>
    intro hn
    have hlt : p + n * d < p + (n + 1) * d := by
      have hmul : n * d < (n + 1) * d :=
        Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hd
      omega
    rw [count_succ_of_gap (hprimes n (by omega)) hlt (hgaps n hn), ihn (by omega)]
    omega

/-- Builder: `k` consecutive primes in arithmetic progression give a witness set for
`IsAPAndPrimeProgressionOfLength k`. -/
theorem exists_witness (p d k : ℕ) (hd : 0 < d)
    (hprimes : ∀ i, i < k → (p + i * d).Prime)
    (hgaps : ∀ i, i + 1 < k → ∀ m, p + i * d < m → m < p + (i + 1) * d → ¬ m.Prime) :
    ∃ s : Set ℕ, s.IsAPAndPrimeProgressionOfLength k := by
  have hnth : ∀ n, n < k →
      Nat.nth Nat.Prime (Nat.count Nat.Prime p + n) = p + n * d := by
    intro n hn
    rw [← count_chain p d k hprimes hgaps hd n hn]
    exact Nat.nth_count (hprimes n hn)
  have hinj : Function.Injective fun n : ℕ => p + n * d := by
    intro x y hxy
    simp only at hxy
    have hxy' := Nat.eq_of_mul_eq_mul_right hd (by omega : x * d = y * d)
    omega
  classical
  refine ⟨↑((Finset.range k).image fun n => p + n * d), ?_, ?_⟩
  · refine ⟨p, d, ?_, ?_⟩
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _ hinj, Finset.card_range]
    · ext x
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
        Set.mem_setOf_eq, smul_eq_mul, Nat.cast_lt]
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, rfl⟩
  · refine ⟨Nat.count Nat.Prime p, ?_, ?_⟩
    · rw [ENat.card_coe_set_eq, Set.encard_coe_eq_coe_finsetCard,
        Finset.card_image_of_injective _ hinj, Finset.card_range]
    · ext x
      simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
        Set.mem_setOf_eq, Nat.cast_lt]
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n, hn, hnth n hn⟩
      · rintro ⟨n, hn, hx⟩
        exact ⟨n, hn, by rw [← hx, hnth n hn]⟩

/- ### Primality certificates for the small primes in the certificate tree -/


/- ### Pratt–Lucas certificates for all large primes in the certificate tree,
in increasing order, ending with the ten primes of the CPAP-10 -/


theorem SP0 : Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 ∧ Nat.Prime 11 ∧ Nat.Prime 13 ∧ Nat.Prime 17 ∧ Nat.Prime 19 ∧ Nat.Prime 23 ∧ Nat.Prime 29 ∧ Nat.Prime 31 ∧ Nat.Prime 37 ∧ Nat.Prime 41 ∧ Nat.Prime 43 ∧ Nat.Prime 47 ∧ Nat.Prime 53 ∧ Nat.Prime 59 ∧ Nat.Prime 61 ∧ Nat.Prime 67 ∧ Nat.Prime 71 ∧ Nat.Prime 79 ∧ Nat.Prime 83 ∧ Nat.Prime 89 ∧ Nat.Prime 97 ∧ Nat.Prime 101 ∧ Nat.Prime 103 ∧ Nat.Prime 109 ∧ Nat.Prime 113 ∧ Nat.Prime 127 ∧ Nat.Prime 131 ∧ Nat.Prime 137 ∧ Nat.Prime 139 ∧ Nat.Prime 149 ∧ Nat.Prime 167 ∧ Nat.Prime 173 ∧ Nat.Prime 179 ∧ Nat.Prime 193 ∧ Nat.Prime 199 ∧ Nat.Prime 223 ∧ Nat.Prime 233 ∧ Nat.Prime 271 ∧ Nat.Prime 307 ∧ Nat.Prime 311 ∧ Nat.Prime 313 ∧ Nat.Prime 347 := by norm_num
theorem SP1 : Nat.Prime 353 ∧ Nat.Prime 359 ∧ Nat.Prime 373 ∧ Nat.Prime 409 ∧ Nat.Prime 439 ∧ Nat.Prime 461 ∧ Nat.Prime 487 ∧ Nat.Prime 499 ∧ Nat.Prime 503 ∧ Nat.Prime 523 ∧ Nat.Prime 569 ∧ Nat.Prime 577 ∧ Nat.Prime 587 ∧ Nat.Prime 601 ∧ Nat.Prime 617 ∧ Nat.Prime 643 ∧ Nat.Prime 653 ∧ Nat.Prime 659 ∧ Nat.Prime 691 ∧ Nat.Prime 751 ∧ Nat.Prime 757 ∧ Nat.Prime 797 ∧ Nat.Prime 823 ∧ Nat.Prime 859 ∧ Nat.Prime 877 ∧ Nat.Prime 881 ∧ Nat.Prime 929 ∧ Nat.Prime 937 ∧ Nat.Prime 983 ∧ Nat.Prime 991 ∧ Nat.Prime 1049 ∧ Nat.Prime 1061 ∧ Nat.Prime 1087 ∧ Nat.Prime 1093 ∧ Nat.Prime 1259 ∧ Nat.Prime 1499 ∧ Nat.Prime 1567 ∧ Nat.Prime 1597 ∧ Nat.Prime 1777 ∧ Nat.Prime 1787 ∧ Nat.Prime 1831 ∧ Nat.Prime 2309 ∧ Nat.Prime 2521 ∧ Nat.Prime 2729 ∧ Nat.Prime 2971 := by norm_num
theorem SP2 : Nat.Prime 3533 ∧ Nat.Prime 4483 ∧ Nat.Prime 4703 ∧ Nat.Prime 4783 ∧ Nat.Prime 4931 ∧ Nat.Prime 4937 ∧ Nat.Prime 5023 ∧ Nat.Prime 5557 ∧ Nat.Prime 5839 ∧ Nat.Prime 5849 ∧ Nat.Prime 6037 ∧ Nat.Prime 6397 ∧ Nat.Prime 6917 ∧ Nat.Prime 7027 ∧ Nat.Prime 7057 ∧ Nat.Prime 7243 ∧ Nat.Prime 8537 ∧ Nat.Prime 8951 ∧ Nat.Prime 9011 ∧ Nat.Prime 9239 ∧ Nat.Prime 9277 ∧ Nat.Prime 9829 ∧ Nat.Prime 10301 ∧ Nat.Prime 10597 ∧ Nat.Prime 11927 ∧ Nat.Prime 12263 ∧ Nat.Prime 13309 ∧ Nat.Prime 13313 ∧ Nat.Prime 15443 ∧ Nat.Prime 16069 ∧ Nat.Prime 17203 ∧ Nat.Prime 18047 ∧ Nat.Prime 23671 ∧ Nat.Prime 23767 ∧ Nat.Prime 23971 ∧ Nat.Prime 26417 ∧ Nat.Prime 28591 ∧ Nat.Prime 28837 ∧ Nat.Prime 30071 ∧ Nat.Prime 32843 ∧ Nat.Prime 34127 ∧ Nat.Prime 37003 ∧ Nat.Prime 37337 ∧ Nat.Prime 37489 ∧ Nat.Prime 40627 := by norm_num
theorem SP3 : Nat.Prime 41681 ∧ Nat.Prime 47809 ∧ Nat.Prime 49019 ∧ Nat.Prime 55697 ∧ Nat.Prime 58193 ∧ Nat.Prime 59791 ∧ Nat.Prime 63617 ∧ Nat.Prime 66109 ∧ Nat.Prime 73553 ∧ Nat.Prime 74761 ∧ Nat.Prime 82217 ∧ Nat.Prime 84827 ∧ Nat.Prime 92269 ∧ Nat.Prime 93257 ∧ Nat.Prime 111341 ∧ Nat.Prime 114649 ∧ Nat.Prime 116959 ∧ Nat.Prime 123731 ∧ Nat.Prime 129707 ∧ Nat.Prime 133241 ∧ Nat.Prime 157351 ∧ Nat.Prime 161779 ∧ Nat.Prime 169199 ∧ Nat.Prime 185821 ∧ Nat.Prime 217661 ∧ Nat.Prime 229939 ∧ Nat.Prime 248827 ∧ Nat.Prime 275491 ∧ Nat.Prime 312553 ∧ Nat.Prime 318691 ∧ Nat.Prime 337969 ∧ Nat.Prime 339887 ∧ Nat.Prime 360293 ∧ Nat.Prime 403061 ∧ Nat.Prime 440239 ∧ Nat.Prime 471313 ∧ Nat.Prime 475141 ∧ Nat.Prime 492673 ∧ Nat.Prime 695171 ∧ Nat.Prime 720653 ∧ Nat.Prime 771233 ∧ Nat.Prime 930157 ∧ Nat.Prime 952111 ∧ Nat.Prime 965357 := by norm_num

theorem pc0 : Nat.Prime 1083707 :=
  prime_of_lucas _ 2 [2, 13, 41681]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.1), List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc1 : Nat.Prime 1305599 :=
  prime_of_lucas _ 11 [2, 7, 93257]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc2 : Nat.Prime 1652947 :=
  prime_of_lucas _ 2 [2, 3, 275491]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc3 : Nat.Prime 1858211 :=
  prime_of_lucas _ 10 [2, 5, 185821]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc4 : Nat.Prime 2018591 :=
  prime_of_lucas _ 7 [2, 5, 7, 28837]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc5 : Nat.Prime 2161759 :=
  prime_of_lucas _ 3 [2, 3, 360293]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc6 : Nat.Prime 2380463 :=
  prime_of_lucas _ 5 [2, 7, 193, 881]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc7 : Nat.Prime 2544811 :=
  prime_of_lucas _ 3 [2, 3, 5, 84827]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc8 : Nat.Prime 2591189 :=
  prime_of_lucas _ 2 [2, 2, 659, 983]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc9 : Nat.Prime 2611199 :=
  prime_of_lucas _ 13 [2, 1305599]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc1, List.forall_mem_nil _⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc10 : Nat.Prime 4037183 :=
  prime_of_lucas _ 5 [2, 2018591]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc4, List.forall_mem_nil _⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc11 : Nat.Prime 4062701 :=
  prime_of_lucas _ 2 [2, 2, 5, 5, 40627]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc12 : Nat.Prime 4676323 :=
  prime_of_lucas _ 3 [2, 3, 7, 111341]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc13 : Nat.Prime 4975823 :=
  prime_of_lucas _ 5 [2, 67, 71, 523]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc14 : Nat.Prime 5182379 :=
  prime_of_lucas _ 2 [2, 2591189]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc8, List.forall_mem_nil _⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc15 : Nat.Prime 7152083 :=
  prime_of_lucas _ 2 [2, 7, 487, 1049]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc16 : Nat.Prime 15982339 :=
  prime_of_lucas _ 2 [2, 3, 1499, 1777]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc17 : Nat.Prime 16467721 :=
  prime_of_lucas _ 11 [2, 2, 2, 3, 5, 109, 1259]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc18 : Nat.Prime 18675439 :=
  prime_of_lucas _ 3 [2, 3, 881, 3533]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc19 : Nat.Prime 19189553 :=
  prime_of_lucas _ 3 [2, 2, 2, 2, 751, 1597]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc20 : Nat.Prime 21651121 :=
  prime_of_lucas _ 13 [2, 2, 2, 2, 3, 3, 5, 30071]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc21 : Nat.Prime 26360903 :=
  prime_of_lucas _ 5 [2, 461, 28591]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc22 : Nat.Prime 30164033 :=
  prime_of_lucas _ 3 [2, 2, 2, 2, 2, 2, 471313]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc23 : Nat.Prime 31569287 :=
  prime_of_lucas _ 5 [2, 7, 503, 4483]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc24 : Nat.Prime 37937261 :=
  prime_of_lucas _ 2 [2, 2, 5, 179, 10597]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc25 : Nat.Prime 43243117 :=
  prime_of_lucas _ 2 [2, 2, 3, 7, 587, 877]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc26 : Nat.Prime 46694521 :=
  prime_of_lucas _ 14 [2, 2, 2, 3, 3, 5, 129707]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc27 : Nat.Prime 56784023 :=
  prime_of_lucas _ 5 [2, 4703, 6037]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc28 : Nat.Prime 60534853 :=
  prime_of_lucas _ 2 [2, 2, 3, 7, 720653]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc29 : Nat.Prime 60703897 :=
  prime_of_lucas _ 5 [2, 2, 2, 3, 11, 229939]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc30 : Nat.Prime 79944847 :=
  prime_of_lucas _ 5 [2, 3, 17, 31, 131, 193]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc31 : Nat.Prime 97169879 :=
  prime_of_lucas _ 7 [2, 13, 101, 37003]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc32 : Nat.Prime 183577111 :=
  prime_of_lucas _ 3 [2, 3, 5, 499, 12263]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc33 : Nat.Prime 238771427 :=
  prime_of_lucas _ 2 [2, 17, 757, 9277]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc34 : Nat.Prime 247956283 :=
  prime_of_lucas _ 2 [2, 3, 3, 3, 7, 71, 9239]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc35 : Nat.Prime 319779389 :=
  prime_of_lucas _ 2 [2, 2, 79944847]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc30, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc36 : Nat.Prime 329668739 :=
  prime_of_lucas _ 2 [2, 7, 79, 347, 859]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc37 : Nat.Prime 335730821 :=
  prime_of_lucas _ 2 [2, 2, 5, 1087, 15443]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc38 : Nat.Prime 357852113 :=
  prime_of_lucas _ 5 [2, 2, 2, 2, 29, 771233]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc39 : Nat.Prime 461096189 :=
  prime_of_lucas _ 10 [2, 2, 7, 16467721]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨pc17, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc40 : Nat.Prime 1058408119 :=
  prime_of_lucas _ 3 [2, 3, 3, 173, 339887]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc41 : Nat.Prime 1081539587 :=
  prime_of_lucas _ 2 [2, 499, 1083707]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc0, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc42 : Nat.Prime 1110031619 :=
  prime_of_lucas _ 2 [2, 47, 103, 114649]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc43 : Nat.Prime 1625900707 :=
  prime_of_lucas _ 5 [2, 3, 3, 17, 17, 312553]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc44 : Nat.Prime 2109160373 :=
  prime_of_lucas _ 2 [2, 2, 11, 29, 1652947]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc2, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc45 : Nat.Prime 2695073261 :=
  prime_of_lucas _ 3 [2, 2, 5, 11, 149, 82217]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc46 : Nat.Prime 2854582189 :=
  prime_of_lucas _ 2 [2, 2, 3, 7243, 32843]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc47 : Nat.Prime 3262224011 :=
  prime_of_lucas _ 6 [2, 5, 17, 19189553]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc19, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc48 : Nat.Prime 3308813021 :=
  prime_of_lucas _ 3 [2, 2, 5, 17, 17, 43, 13313]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc49 : Nat.Prime 5390146523 :=
  prime_of_lucas _ 2 [2, 2695073261]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc45, List.forall_mem_nil _⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc50 : Nat.Prime 6823638763 :=
  prime_of_lucas _ 2 [2, 3, 17203, 66109]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc51 : Nat.Prime 9135179189 :=
  prime_of_lucas _ 2 [2, 2, 307, 313, 23767]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc52 : Nat.Prime 11197579487 :=
  prime_of_lucas _ 5 [2, 23, 131, 1858211]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc3, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc53 : Nat.Prime 12231997963 :=
  prime_of_lucas _ 2 [2, 3, 6397, 318691]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc54 : Nat.Prime 12882676069 :=
  prime_of_lucas _ 2 [2, 2, 3, 3, 357852113]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨pc38, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc55 : Nat.Prime 16174127069 :=
  prime_of_lucas _ 2 [2, 2, 11, 23, 15982339]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc16, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc56 : Nat.Prime 22829695829 :=
  prime_of_lucas _ 2 [2, 2, 17, 335730821]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc37, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc57 : Nat.Prime 27565782029 :=
  prime_of_lucas _ 2 [2, 2, 55697, 123731]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc58 : Nat.Prime 37907731723 :=
  prime_of_lucas _ 2 [2, 3, 7, 7, 797, 161779]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc59 : Nat.Prime 47053325621 :=
  prime_of_lucas _ 2 [2, 2, 5, 7, 353, 952111]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc60 : Nat.Prime 102678983629 :=
  prime_of_lucas _ 6 [2, 2, 3, 13, 23, 71, 403061]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc61 : Nat.Prime 146783975557 :=
  prime_of_lucas _ 2 [2, 2, 3, 12231997963]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨pc53, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc62 : Nat.Prime 164433225403 :=
  prime_of_lucas _ 3 [2, 3, 3, 9135179189]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨pc51, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc63 : Nat.Prime 198528781261 :=
  prime_of_lucas _ 7 [2, 2, 3, 5, 3308813021]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨pc48, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc64 : Nat.Prime 218447926987 :=
  prime_of_lucas _ 2 [2, 3, 17, 71, 30164033]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc22, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc65 : Nat.Prime 248692063469 :=
  prime_of_lucas _ 2 [2, 2, 19, 31, 5849, 18047]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc66 : Nat.Prime 327757380757 :=
  prime_of_lucas _ 14 [2, 2, 3, 13, 37, 56784023]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc67 : Nat.Prime 528124563007 :=
  prime_of_lucas _ 5 [2, 3, 23, 31, 37, 89, 37489]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc68 : Nat.Prime 582536588861 :=
  prime_of_lucas _ 2 [2, 2, 5, 617, 1787, 26417]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc69 : Nat.Prime 804992177299 :=
  prime_of_lucas _ 2 [2, 3, 47, 2854582189]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc46, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc70 : Nat.Prime 2653541220611 :=
  prime_of_lucas _ 2 [2, 5, 7, 37907731723]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨pc58, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc71 : Nat.Prime 3339337037807 :=
  prime_of_lucas _ 5 [2, 7, 11, 131, 10301, 16069]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc72 : Nat.Prime 3495219533167 :=
  prime_of_lucas _ 5 [2, 3, 582536588861]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨pc68, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc73 : Nat.Prime 5357493895483 :=
  prime_of_lucas _ 3 [2, 3, 3, 116959, 2544811]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc7, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc74 : Nat.Prime 9052516320917 :=
  prime_of_lucas _ 2 [2, 2, 29, 37, 2109160373]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc44, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc75 : Nat.Prime 14134419850597 :=
  prime_of_lucas _ 2 [2, 2, 3, 101, 23671, 492673]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc76 : Nat.Prime 15427219380457 :=
  prime_of_lucas _ 7 [2, 2, 2, 3, 13, 17, 53, 59, 930157]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc77 : Nat.Prime 69955944598277 :=
  prime_of_lucas _ 2 [2, 2, 11, 233, 6823638763]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc50, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc78 : Nat.Prime 544896287951143 :=
  prime_of_lucas _ 3 [2, 3, 41, 53, 131, 13309, 23971]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc79 : Nat.Prime 631331429277859 :=
  prime_of_lucas _ 2 [2, 3, 271, 359, 1081539587]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.1), List.forall_mem_cons.2 ⟨pc41, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc80 : Nat.Prime 1165527773351003 :=
  prime_of_lucas _ 2 [2, 643, 4937, 183577111]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc32, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc81 : Nat.Prime 2575135369222133 :=
  prime_of_lucas _ 2 [2, 2, 23, 53, 528124563007]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc67, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc82 : Nat.Prime 3585642171096043 :=
  prime_of_lucas _ 3 [2, 3, 3, 3, 3, 89, 248692063469]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc65, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc83 : Nat.Prime 4859376605767591 :=
  prime_of_lucas _ 12 [2, 3, 5, 29, 92269, 60534853]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc28, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc84 : Nat.Prime 6065932345248247 :=
  prime_of_lucas _ 3 [2, 3, 21651121, 46694521]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨pc20, List.forall_mem_cons.2 ⟨pc26, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc85 : Nat.Prime 6708178025567341 :=
  prime_of_lucas _ 6 [2, 2, 3, 5, 7, 167, 2521, 37937261]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc24, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc86 : Nat.Prime 21437605762796233 :=
  prime_of_lucas _ 5 [2, 2, 2, 3, 3, 29, 47, 218447926987]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc64, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc87 : Nat.Prime 27598490420822947 :=
  prime_of_lucas _ 2 [2, 3, 3, 19, 337969, 238771427]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc33, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc88 : Nat.Prime 36336800512160839 :=
  prime_of_lucas _ 3 [2, 3, 3, 223, 9052516320917]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc74, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc89 : Nat.Prime 58312519269211093 :=
  prime_of_lucas _ 2 [2, 2, 3, 4859376605767591]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨pc83, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc90 : Nat.Prime 106906181114016397 :=
  prime_of_lucas _ 22 [2, 2, 3, 3, 7, 17, 31, 804992177299]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc69, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc91 : Nat.Prime 118505370149481239 :=
  prime_of_lucas _ 11 [2, 7, 11, 11, 69955944598277]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc77, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc92 : Nat.Prime 178448335245923551 :=
  prime_of_lucas _ 6 [2, 3, 5, 5, 73553, 16174127069]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc55, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc93 : Nat.Prime 1039454884912343621 :=
  prime_of_lucas _ 2 [2, 2, 5, 7, 127, 8951, 49019, 133241]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc94 : Nat.Prime 1863545304792909061 :=
  prime_of_lucas _ 6 [2, 2, 3, 3, 5, 19, 544896287951143]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc78, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc95 : Nat.Prime 5022872233605666871 :=
  prime_of_lucas _ 3 [2, 3, 5, 1093, 5557, 27565782029]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc57, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc96 : Nat.Prime 14648913693107146357 :=
  prime_of_lucas _ 2 [2, 2, 3, 61, 60703897, 329668739]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc29, List.forall_mem_cons.2 ⟨pc36, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc97 : Nat.Prime 299051868215083704971 :=
  prime_of_lucas _ 6 [2, 5, 823, 36336800512160839]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc88, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc98 : Nat.Prime 353729277480602391317 :=
  prime_of_lucas _ 2 [2, 2, 13, 601, 1831, 63617, 97169879]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc99 : Nat.Prime 614789822365154359909 :=
  prime_of_lucas _ 6 [2, 2, 3, 101, 439, 7027, 164433225403]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc62, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc100 : Nat.Prime 974736250413007345943 :=
  prime_of_lucas _ 7 [2, 7, 577, 8537, 14134419850597]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc75, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc101 : Nat.Prime 1975395304598545436017 :=
  prime_of_lucas _ 10 [2, 2, 2, 2, 3, 440239, 2161759, 43243117]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc5, List.forall_mem_cons.2 ⟨pc25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc102 : Nat.Prime 4440908034265130232169 :=
  prime_of_lucas _ 11 [2, 2, 2, 3, 7, 13, 137, 74761, 198528781261]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc103 : Nat.Prime 55993568495231890452157 :=
  prime_of_lucas _ 2 [2, 2, 3, 217661, 21437605762796233]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc86, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc104 : Nat.Prime 1310045520555081872947393 :=
  prime_of_lucas _ 10 [2, 2, 2, 2, 2, 2, 3, 7, 974736250413007345943]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨pc100, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc105 : Nat.Prime 1339318016517813805619527 :=
  prime_of_lucas _ 5 [2, 3, 113, 1975395304598545436017]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc101, List.forall_mem_nil _⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc106 : Nat.Prime 5160441010808557806518429 :=
  prime_of_lucas _ 3 [2, 2, 11, 29, 34127, 118505370149481239]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc91, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc107 : Nat.Prime 14731071218372842851056069 :=
  prime_of_lucas _ 2 [2, 2, 169199, 4062701, 5357493895483]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc11, List.forall_mem_cons.2 ⟨pc73, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc108 : Nat.Prime 72246174151319809291258007 :=
  prime_of_lucas _ 5 [2, 7, 5160441010808557806518429]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨pc106, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc109 : Nat.Prime 81467999847607904321136377 :=
  prime_of_lucas _ 3 [2, 2, 2, 695171, 14648913693107146357]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc96, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc110 : Nat.Prime 553143617296955601932204753 :=
  prime_of_lucas _ 3 [2, 2, 2, 2, 53, 1061, 614789822365154359909]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc99, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc111 : Nat.Prime 6053413019594444547884628917 :=
  prime_of_lucas _ 2 [2, 2, 311, 2611199, 1863545304792909061]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc9, List.forall_mem_cons.2 ⟨pc94, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc112 : Nat.Prime 148303579333636000036955565587 :=
  prime_of_lucas _ 2 [2, 247956283, 299051868215083704971]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc34, List.forall_mem_cons.2 ⟨pc97, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc113 : Nat.Prime 232921665463855065155015814569 :=
  prime_of_lucas _ 3 [2, 2, 2, 13, 31, 72246174151319809291258007]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc108, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc114 : Nat.Prime 90778245483882153483569567724259 :=
  prime_of_lucas _ 3 [2, 3, 7, 13, 37337, 59791, 3262224011, 22829695829]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc47, List.forall_mem_cons.2 ⟨pc56, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc115 : Nat.Prime 265457494880237509401972762941993 :=
  prime_of_lucas _ 3 [2, 2, 2, 5023, 18675439, 353729277480602391317]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc18, List.forall_mem_cons.2 ⟨pc98, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc116 : Nat.Prime 19386837104810232468830979355794989 :=
  prime_of_lucas _ 2 [2, 2, 11, 2971, 148303579333636000036955565587]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2), List.forall_mem_cons.2 ⟨pc112, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc117 : Nat.Prime 282789059470568586463609095534188131 :=
  prime_of_lucas _ 15 [2, 3, 5, 7, 11, 31, 37, 102678983629, 1039454884912343621]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc60, List.forall_mem_cons.2 ⟨pc93, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc118 : Nat.Prime 23567721955657194776649723510218140673 :=
  prime_of_lucas _ 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 937, 2729, 3495219533167, 2575135369222133]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc72, List.forall_mem_cons.2 ⟨pc81, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc119 : Nat.Prime 410716897908682995496769866714903337573 :=
  prime_of_lucas _ 2 [2, 2, 17, 61, 373, 265457494880237509401972762941993]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.1), List.forall_mem_cons.2 ⟨pc115, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc120 : Nat.Prime 31260942106937851086988820434353782113597 :=
  prime_of_lucas _ 2 [2, 2, 3, 3, 7, 5182379, 5390146523, 4440908034265130232169]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨pc14, List.forall_mem_cons.2 ⟨pc49, List.forall_mem_cons.2 ⟨pc102, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc121 : Nat.Prime 2567189623092244449323981439041677545536149 :=
  prime_of_lucas _ 2 [2, 2, 3, 13, 58193, 282789059470568586463609095534188131]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc117, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc122 : Nat.Prime 8373094558265845827516770230329627536146799 :=
  prime_of_lucas _ 7 [2, 5839, 47809, 11197579487, 1339318016517813805619527]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.1), List.forall_mem_cons.2 ⟨pc52, List.forall_mem_cons.2 ⟨pc105, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc123 : Nat.Prime 165337136995061861490728657086431249608356451 :=
  prime_of_lucas _ 2 [2, 5, 5, 79, 461096189, 90778245483882153483569567724259]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc39, List.forall_mem_cons.2 ⟨pc114, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc124 : Nat.Prime 334130122469124376448502703576854973706716799 :=
  prime_of_lucas _ 17 [2, 27598490420822947, 6053413019594444547884628917]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc87, List.forall_mem_cons.2 ⟨pc111, List.forall_mem_nil _⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc125 : Nat.Prime 472362132581542660756039516449996870043763098571 :=
  prime_of_lucas _ 2 [2, 5, 2309, 4676323, 3339337037807, 1310045520555081872947393]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc12, List.forall_mem_cons.2 ⟨pc71, List.forall_mem_cons.2 ⟨pc104, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc126 : Nat.Prime 166537906346951949512555048980432872272371711730863 :=
  prime_of_lucas _ 5 [2, 3, 47, 53, 139, 6917, 12882676069, 15427219380457, 58312519269211093]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc54, List.forall_mem_cons.2 ⟨pc76, List.forall_mem_cons.2 ⟨pc89, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc127 : Nat.Prime 7605097443758365136139127684454071607399120106122204869 :=
  prime_of_lucas _ 11 [2, 2, 3, 7, 4931, 7152083, 2567189623092244449323981439041677545536149]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc15, List.forall_mem_cons.2 ⟨pc121, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc128 : Nat.Prime 172065054976772107675581285529480503164616022973170886021 :=
  prime_of_lucas _ 2 [2, 2, 5, 7, 146783975557, 8373094558265845827516770230329627536146799]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨pc61, List.forall_mem_cons.2 ⟨pc122, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc129 : Nat.Prime 297944641350014385275436610378443430138886610872100450151 :=
  prime_of_lucas _ 21 [2, 3, 5, 5, 11927, 166537906346951949512555048980432872272371711730863]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc126, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc130 : Nat.Prime 273555355051988393946924422809812955718146350217215709137931 :=
  prime_of_lucas _ 3 [2, 3, 5, 11, 109, 7605097443758365136139127684454071607399120106122204869]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc131 : Nat.Prime 40687297931583212434454439521483153605327032354191178561100493 :=
  prime_of_lucas _ 2 [2, 2, 4037183, 106906181114016397, 23567721955657194776649723510218140673]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨pc10, List.forall_mem_cons.2 ⟨pc90, List.forall_mem_cons.2 ⟨pc118, List.forall_mem_nil _⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc132 : Nat.Prime 6297297448939257420492825692420433831955731153612194642748437393 :=
  prime_of_lucas _ 5 [2, 2, 2, 2, 7, 31, 83, 127, 172065054976772107675581285529480503164616022973170886021]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc128, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc133 : Nat.Prime 30463286638653519166134094991866993173323371437334932151335007280987 :=
  prime_of_lucas _ 2 [2, 691, 7057, 2380463, 31569287, 178448335245923551, 232921665463855065155015814569]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc6, List.forall_mem_cons.2 ⟨pc23, List.forall_mem_cons.2 ⟨pc92, List.forall_mem_cons.2 ⟨pc113, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc134 : Nat.Prime 61471288489178400502227511463990027154771532183167217954139642300211427949197 :=
  prime_of_lucas _ 2 [2, 2, 3, 3, 3, 3, 569, 26360903, 1625900707, 47053325621, 165337136995061861490728657086431249608356451]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc21, List.forall_mem_cons.2 ⟨pc43, List.forall_mem_cons.2 ⟨pc59, List.forall_mem_cons.2 ⟨pc123, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc135 : Nat.Prime 446092199703710200243488189611814726284358184224501445344992905869145850914339049 :=
  prime_of_lucas _ 3 [2, 2, 2, 19, 653, 2653541220611, 3585642171096043, 472362132581542660756039516449996870043763098571]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc70, List.forall_mem_cons.2 ⟨pc82, List.forall_mem_cons.2 ⟨pc125, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc136 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 :=
  prime_of_lucas _ 3 [2, 3, 11, 409, 9011, 9829, 6708178025567341, 6297297448939257420492825692420433831955731153612194642748437393]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc85, List.forall_mem_cons.2 ⟨pc132, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc137 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 :=
  prime_of_lucas _ 7 [2, 2, 2, 3, 17, 1567, 14731071218372842851056069, 553143617296955601932204753, 19386837104810232468830979355794989]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc107, List.forall_mem_cons.2 ⟨pc110, List.forall_mem_cons.2 ⟨pc116, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc138 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 :=
  prime_of_lucas _ 2 [2, 3, 3, 929, 248827, 81467999847607904321136377, 297944641350014385275436610378443430138886610872100450151]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc109, List.forall_mem_cons.2 ⟨pc129, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc139 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 :=
  prime_of_lucas _ 2 [2, 2, 3, 31, 991, 1110031619, 6065932345248247, 40687297931583212434454439521483153605327032354191178561100493]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc42, List.forall_mem_cons.2 ⟨pc84, List.forall_mem_cons.2 ⟨pc131, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc140 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 :=
  prime_of_lucas _ 3 [2, 3, 23, 4783, 5022872233605666871, 30463286638653519166134094991866993173323371437334932151335007280987]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP2.2.2.2.1), List.forall_mem_cons.2 ⟨pc95, List.forall_mem_cons.2 ⟨pc133, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc141 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 :=
  prime_of_lucas _ 7 [2, 2, 2, 2, 3, 3, 3, 97, 157351, 55993568495231890452157, 273555355051988393946924422809812955718146350217215709137931]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc103, List.forall_mem_cons.2 ⟨pc130, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc142 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 :=
  prime_of_lucas _ 3 [2, 3, 13, 4975823, 1058408119, 631331429277859, 1165527773351003, 334130122469124376448502703576854973706716799]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc13, List.forall_mem_cons.2 ⟨pc40, List.forall_mem_cons.2 ⟨pc79, List.forall_mem_cons.2 ⟨pc80, List.forall_mem_cons.2 ⟨pc124, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc143 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 :=
  prime_of_lucas _ 7 [2, 2, 3, 59, 319779389, 446092199703710200243488189611814726284358184224501445344992905869145850914339049]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨pc35, List.forall_mem_cons.2 ⟨pc135, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc144 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 :=
  prime_of_lucas _ 3 [2, 3, 3, 199, 475141, 965357, 61471288489178400502227511463990027154771532183167217954139642300211427949197]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨(SP0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1), List.forall_mem_cons.2 ⟨(SP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2), List.forall_mem_cons.2 ⟨pc134, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

theorem pc145 : Nat.Prime 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 :=
  prime_of_lucas _ 7 [2, 2, 2, 3, 327757380757, 410716897908682995496769866714903337573, 31260942106937851086988820434353782113597]
    (by norm_num) (by decide +kernel) (by decide +kernel)
    (List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.1), List.forall_mem_cons.2 ⟨(SP0.2.1), List.forall_mem_cons.2 ⟨pc66, List.forall_mem_cons.2 ⟨pc119, List.forall_mem_cons.2 ⟨pc120, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
    (by decide +kernel) (by decide +kernel)

/- ### The 1881 numbers strictly between consecutive members of the CPAP-10 are composite -/

/-- No primes strictly between `P + 0 * 210` and `P + 1 * 210`. -/
theorem gap0_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229858 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229928 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229927 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614964 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229926 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566357 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229925 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614963 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229924 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409975 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229923 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614962 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229922 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 149 677832029998082198911319836160871411607445132142215045661767904422176789955361625228639127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229921 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614961 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229920 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 173 583797528726671951663506679699247631962481645602254576899441721149736079210109145428134277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229919 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614960 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229918 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409973 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229917 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614959 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229916 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747131 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229915 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614958 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229914 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445983 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229913 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614957 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229912 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409971 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229911 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614956 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229910 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660583 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229909 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614955 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229908 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 109 926577729079947226034739959522659085591828666873303135812875392283526070672925524395112201 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229907 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614954 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229906 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409969 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229905 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614953 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229904 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445981 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229903 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614952 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229902 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747129 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229901 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614951 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229900 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409967 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229899 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614950 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229898 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479223 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229897 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614949 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229896 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13121 7697353286313104766236312444780873434152071083697129929395885813497777738232519027442057 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229895 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614948 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229894 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409965 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229893 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614947 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229892 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 163 619613328035056733974151261275888590978584814044110685911677409563830317198459399748878711 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229891 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614946 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229890 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966517 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229889 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614945 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229888 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409963 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229887 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614944 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229886 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656509 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229885 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614943 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229884 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445977 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229883 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614942 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229882 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409961 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229881 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614941 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229880 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012099 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229879 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614940 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229878 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229879 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229877 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614939 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229876 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409959 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229875 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614938 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229874 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445975 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229873 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614937 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229872 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479221 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229871 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614936 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229870 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409957 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229869 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614935 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229868 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 127 795251751730033445966824059747794018342593107788897966957507226448065682703534505189505747 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229867 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614934 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229866 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 179 564228896478850545462495282614356649885526953570894088288287250049744925717032861223839273 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229865 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614933 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229864 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409955 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229863 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614932 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229862 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492699 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229861 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614931 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229860 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747123 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614930 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229858 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409953 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap0_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229788 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229858 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229857 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614929 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229856 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 83 1216830993611015031780562115517708919632642466134819780766306238059088454257215447699605179 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229855 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614928 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229854 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445971 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229853 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614927 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229852 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409951 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229851 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614926 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229850 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229851 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229849 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614925 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229848 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 89 1134797443479935366716703995370447644151790165047079121388802446729262266329762720888395841 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229847 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614924 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229846 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409949 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229845 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614923 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229844 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445969 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229843 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614922 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229842 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660579 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229841 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614921 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229840 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409947 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229839 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614920 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229838 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566349 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229837 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614919 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229836 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352753 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229835 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614918 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229834 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409945 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229833 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614917 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229832 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747119 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229831 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614916 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229830 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 59 1711813092707021146403163654033387124228971604901526132264464707778039689887269189136732709 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229829 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614915 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229828 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409943 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229827 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614914 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229826 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 151 668854122315988394952229507205098280327876322444967164262274289794068488101648226218988277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229825 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614913 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229824 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445965 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229823 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614912 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229822 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409941 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229821 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614911 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229820 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479217 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229819 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614910 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229818 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747117 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229817 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614909 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229816 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409939 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229815 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614908 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229814 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445963 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229813 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614907 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229812 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 139 726596924242548544156738529409854966399347659634460732400024588193556415132006346468109567 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229811 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614906 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229810 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409937 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229809 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614905 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229808 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660577 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229807 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614904 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229806 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 67 1507417499547973845340099337133878213873273502823731967217961459088124503035057942672645221 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229805 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614903 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229804 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409935 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229803 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614902 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229802 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 71 1422492569995975318842065571661547046894497530833662560614132644491610446526040593789679293 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229801 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614901 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229800 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656507 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229799 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614900 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229798 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409933 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229797 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614899 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229796 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494251 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229795 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614898 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229794 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445959 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229793 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614897 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229792 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409931 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229791 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614896 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229790 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747113 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614895 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229788 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229859 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492697 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap0_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229788 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229787 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614894 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229786 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409929 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229785 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614893 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229784 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445957 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229783 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614892 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229782 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 103 980553130773924734347443258135629517762226453293107201976732211251498463139309535524924561 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229781 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614891 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229780 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409927 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229779 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614890 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229778 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352751 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229777 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614889 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229776 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747111 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229775 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614888 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229774 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409925 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229773 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614887 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229772 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566343 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229771 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614886 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229770 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688531 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229769 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614885 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229768 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409923 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229767 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614884 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229766 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012093 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229765 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614883 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229764 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445953 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229763 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614882 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229762 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409921 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229761 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614881 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229760 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 73 1383520170818003392298447336821504662048072940947808791830183804916497831552724413137907257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229759 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614880 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229758 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717089 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229757 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614879 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229756 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409919 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229755 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614878 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229754 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445951 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229753 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614877 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229752 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966511 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229751 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614876 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229750 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409917 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229749 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614875 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229748 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747107 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229747 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614874 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229746 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 137 737204178611052902465596026189560878317586311599927312435061443495652129221524687292461531 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229745 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614873 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229744 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409915 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229743 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614872 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229742 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479211 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229741 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614871 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229740 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660573 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229739 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614870 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229738 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409913 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229737 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614869 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229736 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 61 1655688073274004059635846812917538366057529912937541668911531438670562978743424297689626717 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229735 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614868 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229734 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445947 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229733 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614867 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229732 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409911 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229731 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614866 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229730 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229729 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614865 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229728 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566339 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229727 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614864 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229726 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409909 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229725 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614863 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229724 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445945 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229723 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614862 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229722 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229723 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229721 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614861 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229720 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409907 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229789 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614860 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap0 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229858 : ℕ) m with hc0 | hc0
  · exact gap0_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229788 : ℕ) m with hc1 | hc1
  · exact gap0_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 : ℕ) m with hc2 | hc2
  · exact gap0_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 1 * 210` and `P + 2 * 210`. -/
theorem gap1_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230068 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230138 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230137 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615069 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230136 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 191 528779960574420144700453694177852567170205888425078752898447213397404930384025561042236807 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230135 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615068 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230134 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410045 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230133 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615067 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230132 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479241 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230131 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615066 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230130 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717101 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230129 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615065 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230128 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410043 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230127 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615064 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230126 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747161 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230125 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615063 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230124 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446025 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230123 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615062 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230122 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410041 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230121 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615061 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230120 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966527 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230119 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615060 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230118 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 223 452901221837283621694110563174752647217530603987399290599118465286566554723537588157252153 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230117 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615059 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230116 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410039 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230115 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615058 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230114 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446023 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230113 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615057 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230112 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747159 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230111 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615056 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230110 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410037 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230109 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615055 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230108 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012111 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230107 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615054 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230106 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479239 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230105 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615053 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230104 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410035 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230103 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615052 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230102 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566373 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230101 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615051 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230100 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 113 893778517431099536617581022902387967517781634417610989412419626184994174365919311142187877 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230099 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615050 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230098 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410033 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230097 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615049 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230096 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 181 557994323037095290816500859602043316737620578393315148086206727949747744217397139000371437 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230095 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615048 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230094 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446019 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230093 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615047 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230092 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410031 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230091 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615046 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230090 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 139 726596924242548544156738529409854966399347659634460732400024588193556415132006346468109569 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230089 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615045 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230088 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 97 1041205901749631418946254181319276704427931182362783936119622863493859192818029712980074537 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230087 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615044 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230086 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410029 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230085 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615043 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230084 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446017 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230083 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615042 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230082 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 563 179390714866277526887720525023037016571064519874227427715103761561108955068115243621789041 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230081 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615041 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230080 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410027 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230079 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615040 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230078 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230077 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615039 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230076 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 157 643292818278434698329851309477514906557384233689108546519766992094932112760183962796606561 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230075 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615038 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230074 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410025 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230073 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615037 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230072 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230073 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230071 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615036 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230070 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747153 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615035 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230068 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410023 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap1_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229998 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230068 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230067 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615034 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230066 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 59 1711813092707021146403163654033387124228971604901526132264464707778039689887269189136732713 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230065 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615033 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230064 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446013 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230063 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615032 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230062 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410021 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230061 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615031 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230060 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 167 604772290237809866094530871784250540895265417300539172476667172209008034151789713527348683 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230059 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615030 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230058 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566369 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230057 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615029 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230056 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410019 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230055 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615028 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230054 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446011 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230053 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615027 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230052 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 73 1383520170818003392298447336821504662048072940947808791830183804916497831552724413137907261 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230051 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615026 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230050 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410017 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230049 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615025 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230048 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891133 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230047 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615024 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230046 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660591 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230045 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615023 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230044 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410015 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230043 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615022 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230042 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747149 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230041 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615021 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230040 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230041 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230039 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615020 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230038 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410013 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230037 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615019 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230036 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566367 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230035 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615018 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230034 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446007 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230033 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615017 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230032 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410011 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230031 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615016 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230030 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 251 402378376373363536405524524254859921631511253741792995233479752027507337463541363183534781 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230029 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615015 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230028 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747147 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230027 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615014 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230026 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410009 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230025 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615013 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230024 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446005 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230023 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615012 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230022 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 83 1216830993611015031780562115517708919632642466134819780766306238059088454257215447699605181 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230021 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615011 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230020 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410007 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230019 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615010 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230018 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230019 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230017 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615009 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230016 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688537 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230015 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615008 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230014 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410005 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230013 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615007 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230012 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660589 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230011 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615006 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230010 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352759 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230009 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615005 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230008 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410003 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230007 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615004 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230006 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717097 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230005 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615003 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230004 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446001 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230003 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615002 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230002 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410001 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230001 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615001 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230000 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747143 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615000 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229998 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230069 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 79 1278442689490053767566919690986960004171004109989747364602574908340561287384163065304648481 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap1_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229998 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229997 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614999 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229996 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409999 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229995 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614998 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229994 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445999 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229993 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614997 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229992 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566363 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229991 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614996 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229990 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409997 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229989 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614995 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229988 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 103 980553130773924734347443258135629517762226453293107201976732211251498463139309535524924563 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229987 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614994 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229986 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747141 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229985 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614993 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229984 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409995 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229983 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614992 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229982 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966521 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229981 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614991 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229980 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 61 1655688073274004059635846812917538366057529912937541668911531438670562978743424297689626721 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229979 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614990 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229978 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409993 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229977 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614989 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229976 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479229 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229975 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614988 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229974 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445995 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229973 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614987 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229972 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409991 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229971 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614986 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229970 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566361 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229969 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614985 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229968 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 263 384018906728951511930747739878212320644522147107186470736134668284807382902467232543981863 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229967 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614984 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229966 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409989 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229965 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614983 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229964 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445993 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229963 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614982 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229962 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 601 168048207104349829680177463540715208534957279016955144431952442194516375546337574307932163 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229961 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614981 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229960 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409987 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229959 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614980 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229958 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747137 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229957 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614979 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229956 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012103 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229955 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614978 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229954 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409985 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229953 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614977 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229952 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352757 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229951 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614976 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229950 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479227 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229949 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614975 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229948 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409983 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229947 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614974 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229946 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 4271 23647148787102375939542649400133420821706702104703826224210587159659176235857851125981557 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229945 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614973 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229944 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445989 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229943 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614972 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229942 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409981 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229941 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614971 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229940 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 67 1507417499547973845340099337133878213873273502823731967217961459088124503035057942672645223 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229939 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614970 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229938 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229939 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229937 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614969 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229936 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409979 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229935 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614968 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229934 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813445987 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229933 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614967 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229932 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229933 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229931 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614966 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229930 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022409977 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229999 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533614965 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap1 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230068 : ℕ) m with hc0 | hc0
  · exact gap1_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229998 : ℕ) m with hc1 | hc1
  · exact gap1_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229929 : ℕ) m with hc2 | hc2
  · exact gap1_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 2 * 210` and `P + 3 * 210`. -/
theorem gap2_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230278 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230348 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230347 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615174 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230346 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 61 1655688073274004059635846812917538366057529912937541668911531438670562978743424297689626727 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230345 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615173 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230344 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410115 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230343 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615172 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230342 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 67 1507417499547973845340099337133878213873273502823731967217961459088124503035057942672645229 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230341 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615171 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230340 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230339 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615170 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230338 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410113 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230337 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615169 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230336 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747191 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230335 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615168 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230334 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446067 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230333 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615167 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230332 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410111 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230331 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615166 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230330 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230331 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230329 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615165 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230328 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 613 164758519526450648675019014009738728106866761320049007836220909884020133284419057355737733 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230327 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615164 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230326 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410109 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230325 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615163 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230324 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446065 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230323 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615162 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230322 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747189 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230321 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615161 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230320 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410107 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230319 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615160 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230318 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660607 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230317 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615159 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230316 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717107 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230315 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615158 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230314 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410105 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230313 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615157 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230312 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230313 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230311 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615156 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230310 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 193 523300375490747397086977490093107980981913599425855138878774185279297107271237731394130727 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230309 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615155 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230308 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410103 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230307 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615154 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230306 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492711 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230305 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615153 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230304 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446061 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230303 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615152 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230302 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410101 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230301 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615151 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230300 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566391 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230299 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615150 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230298 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012121 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230297 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615149 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230296 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410099 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230295 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615148 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230294 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446059 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230293 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615147 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230292 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230293 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230291 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615146 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230290 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410097 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230289 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615145 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230288 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479253 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230287 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615144 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230286 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230287 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230285 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615143 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230284 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410095 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230283 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615142 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230282 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 97 1041205901749631418946254181319276704427931182362783936119622863493859192818029712980074539 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230281 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615141 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230280 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747183 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615140 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230278 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410093 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap2_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230208 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230278 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230277 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615139 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230276 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230275 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615138 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230274 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446055 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230273 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615137 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230272 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410091 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230271 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615136 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230270 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 739 136667080473226316153973823529052557956034268862232803523144002380114129503855050282905589 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230269 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615135 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230268 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 241 419074574563129658248077409078713030412901762195809302089640737588814695864518183232644109 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230267 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615134 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230266 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410089 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230265 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615133 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230264 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446053 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230263 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615132 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230262 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479251 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230261 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615131 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230260 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410087 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230259 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615130 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230258 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966533 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230257 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615129 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230256 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566387 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230255 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615128 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230254 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410085 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230253 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230252 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747179 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230251 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615126 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230250 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660603 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230249 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615125 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230248 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410083 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230247 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615124 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230246 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 107 943896938969292033998006126990372339528124529805514409379471194008451791620083010832404021 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230245 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615123 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230244 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446049 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230243 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615122 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230242 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410081 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230241 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615121 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230240 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11597 8708887856317517257720673931876333562948118020970082073260620656972004975713450216354853 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230239 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615120 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230238 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747177 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230237 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615119 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230236 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410079 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230235 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615118 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230234 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446047 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230233 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615117 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230232 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492709 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230231 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615116 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230230 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410077 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230229 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615115 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230228 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 71 1422492569995975318842065571661547046894497530833662560614132644491610446526040593789679299 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230227 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615114 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230226 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230227 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230225 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615113 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230224 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410075 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230223 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615112 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230222 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012117 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230221 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615111 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230220 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 149 677832029998082198911319836160871411607445132142215045661767904422176789955361625228639129 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230219 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615110 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230218 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410073 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230217 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615109 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230216 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660601 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230215 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615108 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230214 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446043 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230213 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615107 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230212 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410071 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230211 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615106 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230210 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747173 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615105 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230208 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230279 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 67 1507417499547973845340099337133878213873273502823731967217961459088124503035057942672645227 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap2_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230208 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230207 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615104 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230206 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410069 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230205 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615103 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230204 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446041 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230203 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615102 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230202 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3329 30338531832296259428593167794523833081859214385458108081587088542776912497251091066106107 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230201 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615101 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230200 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410067 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230199 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615100 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230198 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 73 1383520170818003392298447336821504662048072940947808791830183804916497831552724413137907263 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230197 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615099 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230196 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747171 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230195 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615098 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230194 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410065 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230193 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615097 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230192 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717103 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230191 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615096 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230190 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566381 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230189 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615095 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230188 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410063 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230187 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615094 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230186 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230187 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230185 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615093 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230184 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446037 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230183 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615092 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230182 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410061 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230181 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615091 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230180 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688541 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230179 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615090 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230178 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2741 36846761207484220225387324183863495195005226081426501934915511769027486940295104764344119 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230177 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615089 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230176 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410059 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230175 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615088 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230174 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446035 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230173 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615087 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230172 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494259 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230171 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615086 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230170 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410057 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230169 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615085 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230168 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747167 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230167 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615084 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230166 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966529 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230165 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615083 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230164 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410055 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230163 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615082 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230162 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230163 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230161 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615081 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230160 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 487 207385980430624738475947958086180370286466785809425137173723650428961687275870394577140103 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230159 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615080 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230158 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410053 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230157 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615079 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230156 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 79 1278442689490053767566919690986960004171004109989747364602574908340561287384163065304648483 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230155 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615078 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230154 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446031 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230153 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615077 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230152 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410051 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230151 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615076 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230150 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230151 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230149 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615075 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230148 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660597 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230147 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615074 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230146 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410049 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230145 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615073 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230144 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446029 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230143 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615072 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230142 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 367 275196110271700947241925492065312916429180721223951067584750457108731176303402948662308529 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230141 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615071 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230140 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410047 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230209 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615070 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap2 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230278 : ℕ) m with hc0 | hc0
  · exact gap2_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230208 : ℕ) m with hc1 | hc1
  · exact gap2_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230139 : ℕ) m with hc2 | hc2
  · exact gap2_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 3 * 210` and `P + 4 * 210`. -/
theorem gap3_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230488 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230558 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230557 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615279 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230556 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660621 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230555 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615278 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230554 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410185 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230553 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230552 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 113 893778517431099536617581022902387967517781634417610989412419626184994174365919311142187881 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230551 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615276 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230550 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230551 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230549 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615275 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230548 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410183 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230547 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615274 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230546 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747221 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230545 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615273 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230544 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446109 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230543 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615272 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230542 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410181 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230541 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615271 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230540 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230541 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230539 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615270 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230538 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 59 1711813092707021146403163654033387124228971604901526132264464707778039689887269189136732721 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230537 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615269 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230536 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410179 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230535 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615268 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230534 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446107 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230533 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615267 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230532 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747219 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230531 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615266 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230530 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410177 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230529 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615265 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230528 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492717 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230527 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615264 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230526 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012133 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230525 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615263 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230524 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410175 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230523 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615262 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230522 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479271 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230521 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615261 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230520 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566411 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230519 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615260 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230518 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410173 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230517 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615259 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230516 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230517 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230515 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615258 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230514 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446103 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230513 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230512 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410171 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230511 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615256 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230510 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 131 770969255494001890364783630442517865110758203734275128271781814953468257277472382893642981 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230509 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615255 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230508 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688549 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230507 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615254 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230506 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410169 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230505 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615253 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230504 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446101 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230503 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615252 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230502 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717113 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230501 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615251 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230500 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410167 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230499 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615250 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230498 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566409 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230497 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615249 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230496 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479269 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230495 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615248 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230494 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410165 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230493 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615247 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230492 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 20963 4817868266455862597805021017410191305133297938710587311148376556738269412934641137197311 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230491 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615246 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230490 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747213 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615245 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230488 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410163 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap3_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230418 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230488 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230487 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615244 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230486 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230487 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230485 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615243 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230484 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446097 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230483 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615242 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230482 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410161 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230481 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615241 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230480 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230481 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230479 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615240 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230478 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 281 359419830853075614369347528782810819677969127007793743073321771384001216026152605548281959 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230477 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615239 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230476 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410159 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230475 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615238 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230474 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446095 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230473 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615237 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230472 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891141 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230471 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615236 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230470 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410157 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230469 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615235 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230468 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 61 1655688073274004059635846812917538366057529912937541668911531438670562978743424297689626729 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230467 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615234 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230466 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2347 43032370033964315141792354319544030817856550783634444739498686731531462165892152602925961 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230465 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615233 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230464 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410155 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230463 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615232 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230462 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747209 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230461 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615231 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230460 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 107 943896938969292033998006126990372339528124529805514409379471194008451791620083010832404023 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230459 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615230 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230458 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410153 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230457 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615229 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230456 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230457 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230455 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615228 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230454 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446091 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230453 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615227 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230452 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410151 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230451 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615226 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230450 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012129 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230449 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615225 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230448 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747207 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230447 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615224 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230446 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410149 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230445 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615223 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230444 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446089 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230443 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615222 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230442 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966541 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230441 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615221 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230440 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410147 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230439 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615220 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230438 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 313 322674033449566286382704969929616103289167171530958600011512516801611315346162562808521503 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230437 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615219 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230436 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 4679 21585161887094303833679558792043137492949203823293447703270659918551900342669134891871603 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230435 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615218 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230434 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410145 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230433 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615217 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230432 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566403 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230431 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615216 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230430 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 151 668854122315988394952229507205098280327876322444967164262274289794068488101648226218988281 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230429 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615215 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230428 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410143 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230427 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615214 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230426 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688547 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230425 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615213 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230424 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446085 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230423 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615212 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230422 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410141 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230421 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615211 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230420 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747203 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615210 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230418 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230489 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479263 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap3_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230418 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230417 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615209 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230416 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410139 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230415 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615208 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230414 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446083 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230413 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615207 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230412 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230411 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615206 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230410 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410137 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230409 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615205 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230408 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230409 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230407 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615204 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230406 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747201 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230405 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615203 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230404 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410135 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230403 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615202 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230402 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656521 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230401 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615201 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230400 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 103 980553130773924734347443258135629517762226453293107201976732211251498463139309535524924567 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230399 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615200 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230398 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410133 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230397 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615199 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230396 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966539 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230395 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615198 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230394 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446079 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230393 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615197 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230392 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410131 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230391 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615196 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230390 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 157 643292818278434698329851309477514906557384233689108546519766992094932112760183962796606563 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230389 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615195 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230388 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566399 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230387 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615194 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230386 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410129 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230385 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615193 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230384 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446077 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230383 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615192 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230382 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 89 1134797443479935366716703995370447644151790165047079121388802446729262266329762720888395847 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230381 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615191 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230380 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230379 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615190 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230378 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747197 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230377 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615189 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230376 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 127 795251751730033445966824059747794018342593107788897966957507226448065682703534505189505751 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230375 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615188 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230374 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410125 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230373 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615187 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230372 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 32183 3138208758341803052474494471863090461719209666258274300208290642851951082973895601996931 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230371 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615186 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230370 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 71 1422492569995975318842065571661547046894497530833662560614132644491610446526040593789679301 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230369 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615185 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230368 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410123 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230367 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615184 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230366 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566397 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230365 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615183 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230364 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446073 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230363 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615182 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230362 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410121 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230361 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615181 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230360 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494263 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230359 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615180 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230358 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352771 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230357 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615179 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230356 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410119 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230355 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615178 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230354 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446071 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230353 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615177 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230352 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660609 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230351 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615176 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230350 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410117 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230419 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615175 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap3 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230488 : ℕ) m with hc0 | hc0
  · exact gap3_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230418 : ℕ) m with hc1 | hc1
  · exact gap3_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230349 : ℕ) m with hc2 | hc2
  · exact gap3_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 4 * 210` and `P + 5 * 210`. -/
theorem gap4_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230698 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230768 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230767 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615384 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230766 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 431 234331722667550458556349548928004269906054117608329563349427883431332579358118056053520257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230765 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615383 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230764 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410255 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230763 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615382 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230762 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566433 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230761 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615381 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230760 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660633 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230759 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615380 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230758 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410253 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230757 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615379 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230756 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747251 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230755 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615378 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230754 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446151 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230753 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615377 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230752 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410251 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230751 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615376 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230750 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717121 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230749 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615375 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230748 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 27259 3705087217789142948669674441027544676235713881257200990630742791698314013843093369495111 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230747 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615374 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230746 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410249 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230745 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615373 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230744 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446149 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230743 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615372 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230742 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747249 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230741 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615371 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230740 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410247 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230739 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615370 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230738 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 89 1134797443479935366716703995370447644151790165047079121388802446729262266329762720888395851 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230737 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615369 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230736 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494271 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230735 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615368 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230734 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410245 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230733 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615367 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230732 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 151 668854122315988394952229507205098280327876322444967164262274289794068488101648226218988283 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230731 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615366 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230730 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479287 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230729 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615365 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230728 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410243 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230727 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615364 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230726 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660631 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230725 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615363 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230724 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446145 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230723 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615362 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230722 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410241 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230721 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615361 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230720 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 101 999970024452616313245412431564057825044646779100891503005974433256478630726226556030368621 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230719 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615360 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230718 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566429 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230717 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615359 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230716 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410239 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230715 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615358 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230714 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446143 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230713 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615357 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230712 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 61 1655688073274004059635846812917538366057529912937541668911531438670562978743424297689626733 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230711 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615356 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230710 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410237 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230709 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615355 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230708 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 397 254400434432529591027170417098160806875338349343047964240814654304544941318259149015282697 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230707 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615354 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230706 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352783 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230705 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615353 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230704 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410235 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230703 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615352 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230702 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230703 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230701 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615351 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230700 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747243 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615350 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230698 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410233 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap4_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230628 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230698 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230697 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615349 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230696 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566427 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230695 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615348 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230694 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446139 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230693 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615347 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230692 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410231 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230691 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615346 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230690 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2699 37420145413010095456756819410140733727124610851867373769397338925122023602574613619513609 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230689 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615345 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230688 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717119 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230687 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615344 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230686 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410229 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230685 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615343 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230684 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446137 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230683 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615342 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230682 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 4871 20734340478282539034651335575440328542293024982383502731185263346110519750225596830028173 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230681 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615341 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230680 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410227 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230679 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615340 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230678 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479283 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230677 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615339 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230676 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492721 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230675 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615338 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230674 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410225 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230673 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615337 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230672 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747239 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230671 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615336 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230670 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 97 1041205901749631418946254181319276704427931182362783936119622863493859192818029712980074543 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230669 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615335 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230668 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410223 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230667 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615334 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230666 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230667 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230665 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615333 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230664 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446133 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230663 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615332 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230662 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410221 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230661 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615331 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230660 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656527 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230659 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615330 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230658 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747237 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230657 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615329 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230656 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410219 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230655 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615328 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230654 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446131 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230653 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615327 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230652 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566423 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230651 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615326 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230650 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410217 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230649 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615325 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230648 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352781 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230647 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615324 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230646 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 139 726596924242548544156738529409854966399347659634460732400024588193556415132006346468109573 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230645 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615323 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230644 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410215 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230643 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615322 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230642 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494269 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230641 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615321 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230640 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012139 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230639 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615320 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230638 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410213 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230637 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615319 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230636 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 73 1383520170818003392298447336821504662048072940947808791830183804916497831552724413137907269 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230635 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615318 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230634 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230633 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615317 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230632 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410211 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230631 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615316 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230630 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747233 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615315 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230628 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230699 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 269 375453429255443299768723626721077473343900835275799411909306385720833984027319264531848441 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap4_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230628 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230627 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615314 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230626 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410209 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230625 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615313 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230624 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446125 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230623 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615312 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230622 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 1009 100096107502194497163316804348830367026272868869365750053125290147576156296678773200264847 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230621 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615311 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230620 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410207 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230619 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615310 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230618 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3499 28864524855591382577246829262066259025295605798568174279395089385225590655429803417852881 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230617 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615309 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230616 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747231 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230615 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615308 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230614 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410205 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230613 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615307 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230612 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 173 583797528726671951663506679699247631962481645602254576899441721149736079210109145428134281 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230611 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615306 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230610 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 67 1507417499547973845340099337133878213873273502823731967217961459088124503035057942672645233 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230609 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615305 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230608 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410203 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230607 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615304 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230606 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 103 980553130773924734347443258135629517762226453293107201976732211251498463139309535524924569 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230605 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615303 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230604 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446121 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230603 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615302 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230602 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410201 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230601 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615301 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230600 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230599 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615300 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230598 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230599 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230597 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615299 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230596 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410199 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230595 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615298 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230594 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446119 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230593 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615297 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230592 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230593 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230591 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615296 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230590 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410197 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230589 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615295 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230588 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747227 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230587 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615294 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230586 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566417 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230585 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615293 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230584 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410195 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230583 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615292 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230582 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 179 564228896478850545462495282614356649885526953570894088288287250049744925717032861223839277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230581 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615291 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230580 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966547 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230579 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615290 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230578 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410193 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230577 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615289 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230576 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 227 444920583567023117347077777920571983830437553696872430852878492329975073583034723167697051 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230575 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615288 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230574 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446115 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230573 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615287 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230572 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410191 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230571 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615286 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230570 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 937 107787590682725984672130902441803458195847731792091826898189346594348283568141816605194483 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230569 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615285 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230568 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 137 737204178611052902465596026189560878317586311599927312435061443495652129221524687292461537 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230567 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615284 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230566 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410189 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230565 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615283 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230564 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446113 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230563 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615282 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230562 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 109 926577729079947226034739959522659085591828666873303135812875392283526070672925524395112207 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230561 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615281 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230560 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410187 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230629 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615280 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap4 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230698 : ℕ) m with hc0 | hc0
  · exact gap4_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230628 : ℕ) m with hc1 | hc1
  · exact gap4_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230559 : ℕ) m with hc2 | hc2
  · exact gap4_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 5 * 210` and `P + 6 * 210`. -/
theorem gap5_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230908 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230978 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230977 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615489 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230976 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230977 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230975 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615488 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230974 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410325 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230973 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615487 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230972 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492729 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230971 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615486 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230970 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11801 8558340180468964294363753545290216111304916929852558410609560016854871765388431671813171 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230969 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615485 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230968 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410323 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230967 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615484 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230966 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747281 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230965 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615483 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230964 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446193 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230963 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615482 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230962 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410321 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230961 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615481 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230960 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566451 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230959 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615480 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230958 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 173 583797528726671951663506679699247631962481645602254576899441721149736079210109145428134283 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230957 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615479 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230956 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410319 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230955 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615478 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230954 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446191 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230953 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615477 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230952 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747279 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230951 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615476 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230950 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410317 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230949 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615475 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230948 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966563 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230947 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615474 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230946 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 79 1278442689490053767566919690986960004171004109989747364602574908340561287384163065304648493 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230945 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615473 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230944 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410315 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230943 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615472 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230942 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 1949 51819893519607104996298951045648968870964250738424854696564093257518902874986599363297707 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230941 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615471 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230940 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 179 564228896478850545462495282614356649885526953570894088288287250049744925717032861223839279 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230939 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615470 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230938 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410313 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230937 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615469 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230936 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230935 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615468 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230934 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446187 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230933 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615467 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230932 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410311 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230931 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615466 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230930 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660643 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230929 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615465 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230928 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 73 1383520170818003392298447336821504662048072940947808791830183804916497831552724413137907273 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230927 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615464 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230926 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410309 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230925 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615463 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230924 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446185 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230923 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615462 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230922 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 101 999970024452616313245412431564057825044646779100891503005974433256478630726226556030368623 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230921 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615461 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230920 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410307 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230919 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615460 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230918 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688559 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230917 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615459 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230916 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566447 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230915 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615458 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230914 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410305 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230913 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615457 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230912 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479301 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230911 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615456 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230910 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747273 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615455 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230908 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410303 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap5_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230838 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230908 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230907 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615454 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230906 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012153 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230905 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615453 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230904 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446181 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230903 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615452 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230902 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410301 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230901 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615451 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230900 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 191 528779960574420144700453694177852567170205888425078752898447213397404930384025561042236811 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230899 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615450 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230898 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492727 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230897 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615449 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230896 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410299 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230895 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615448 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230894 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446179 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230893 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615447 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230892 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 59 1711813092707021146403163654033387124228971604901526132264464707778039689887269189136732727 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230891 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615446 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230890 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410297 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230889 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615445 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230888 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 107 943896938969292033998006126990372339528124529805514409379471194008451791620083010832404027 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230887 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615444 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230886 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479299 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230885 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615443 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230884 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410295 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230883 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615442 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230882 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747269 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230881 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615441 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230880 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352789 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230879 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615440 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230878 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410293 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230877 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615439 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230876 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 367 275196110271700947241925492065312916429180721223951067584750457108731176303402948662308531 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230875 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615438 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230874 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446175 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230873 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615437 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230872 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410291 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230871 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615436 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230870 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 163 619613328035056733974151261275888590978584814044110685911677409563830317198459399748878717 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230869 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615435 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230868 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747267 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230867 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615434 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230866 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410289 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230865 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615433 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230864 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446173 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230863 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615432 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230862 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660639 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230861 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615431 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230860 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410287 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230859 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615430 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230858 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2693 37503517441408929683544989078340081815636585476862250948237436969515165875732967753088463 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230857 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615429 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230856 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966559 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230855 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615428 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230854 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410285 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230853 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615427 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230852 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 83 1216830993611015031780562115517708919632642466134819780766306238059088454257215447699605191 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230851 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615426 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230850 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566441 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230849 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615425 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230848 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410283 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230847 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615424 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230846 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 331 305126805044453920355850923226494985889756267943172331732940839150768403937609915888420637 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230845 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615423 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230844 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446169 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230843 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615422 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230842 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410281 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230841 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615421 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230840 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747263 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615420 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230838 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230909 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3253 31047332453032354023297465597285533455121218779339084476976150556072653459375617017850363 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap5_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230838 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230837 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615419 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230836 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410279 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230835 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615418 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230834 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446167 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230833 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615417 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230832 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656531 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230831 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615416 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230830 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230829 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615415 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230828 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566439 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230827 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615414 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230826 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747261 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230825 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615413 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230824 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410275 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230823 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615412 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230822 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352787 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230821 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615411 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230820 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 181 557994323037095290816500859602043316737620578393315148086206727949747744217397139000371441 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230819 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615410 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230818 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410273 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230817 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615409 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230816 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 149 677832029998082198911319836160871411607445132142215045661767904422176789955361625228639133 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230815 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615408 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230814 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446163 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230813 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615407 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230812 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410271 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230811 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615406 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230810 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966557 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230809 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615405 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230808 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479293 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230807 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615404 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230806 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410269 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230805 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615403 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230804 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446161 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230803 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615402 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230802 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230803 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230801 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615401 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230800 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410267 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230799 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615400 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230798 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230797 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615399 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230796 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 71 1422492569995975318842065571661547046894497530833662560614132644491610446526040593789679307 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230795 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615398 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230794 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410265 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230793 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615397 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230792 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012147 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230791 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615396 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230790 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891147 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230789 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615395 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230788 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410263 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230787 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615394 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230786 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230787 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230785 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615393 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230784 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446157 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230783 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615392 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230782 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410261 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230781 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615391 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230780 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 109 926577729079947226034739959522659085591828666873303135812875392283526070672925524395112209 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230779 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615390 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230778 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 113 893778517431099536617581022902387967517781634417610989412419626184994174365919311142187883 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230777 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615389 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230776 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410259 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230775 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615388 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230774 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446155 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230773 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615387 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230772 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 131 770969255494001890364783630442517865110758203734275128271781814953468257277472382893642983 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230771 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615386 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230770 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230839 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615385 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap5 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230908 : ℕ) m with hc0 | hc0
  · exact gap5_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230838 : ℕ) m with hc1 | hc1
  · exact gap5_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230769 : ℕ) m with hc2 | hc2
  · exact gap5_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 6 * 210` and `P + 7 * 210`. -/
theorem gap6_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231118 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231188 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231187 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615594 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231186 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 503 200789209681340452560212038942285964869799850276719765017104210256271057064311892960372229 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231185 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615593 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231184 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410395 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231183 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615592 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231182 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 181 557994323037095290816500859602043316737620578393315148086206727949747744217397139000371443 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231181 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615591 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231180 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566471 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231179 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615590 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231178 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410393 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231177 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615589 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231176 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747311 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231175 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615588 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231174 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446235 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231173 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615587 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231172 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410391 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231171 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615586 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231170 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352799 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231169 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615585 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231168 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660657 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231167 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615584 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231166 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410389 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231165 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615583 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231164 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446233 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231163 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615582 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231162 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747309 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231161 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615581 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231160 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410387 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231159 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615580 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231158 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566469 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231157 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615579 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231156 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 257 392984328675930924660648465322839845640114103848988489508184504898460473553886701008043701 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231155 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615578 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231154 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410385 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231153 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615577 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231152 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 631 160058593454380741105842560361283423660078169079540478294141708017281048658239115941469463 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231151 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615576 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231150 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231151 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231149 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615575 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231148 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410383 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231147 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615574 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231146 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479319 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231145 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615573 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231144 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446229 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231143 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615572 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231142 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410381 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231141 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615571 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231140 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231141 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231139 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615570 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231138 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 127 795251751730033445966824059747794018342593107788897966957507226448065682703534505189505757 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231137 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615569 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231136 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410379 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231135 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615568 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231134 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446227 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231133 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615567 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231132 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966571 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231131 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615566 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231130 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410377 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231129 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615565 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231128 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 59 1711813092707021146403163654033387124228971604901526132264464707778039689887269189136732731 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231127 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615564 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231126 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231127 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231125 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615563 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231124 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410375 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231123 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615562 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231122 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717133 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231121 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615561 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231120 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747303 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615560 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231118 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410373 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap6_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231048 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231118 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231117 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615559 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231116 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 137 737204178611052902465596026189560878317586311599927312435061443495652129221524687292461541 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231115 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615558 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231114 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446223 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231113 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615557 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231112 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410371 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231111 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615556 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231110 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231111 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231109 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615555 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231108 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891153 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231107 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615554 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231106 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410369 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231105 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615553 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231104 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446221 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231103 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615552 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231102 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 107 943896938969292033998006126990372339528124529805514409379471194008451791620083010832404029 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231101 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615551 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231100 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410367 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231099 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615550 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231098 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2389 42275836111224046729923254745906170083511647002591059775472338953078418461008322377173391 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231097 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615549 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231096 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012163 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231095 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615548 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231094 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410365 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231093 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615547 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231092 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747299 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231091 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615546 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231090 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656537 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231089 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615545 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231088 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410363 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231087 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615544 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231086 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966569 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231085 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615543 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231084 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446217 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231083 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615542 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231082 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410361 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231081 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615541 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231080 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 71 1422492569995975318842065571661547046894497530833662560614132644491610446526040593789679311 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231079 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615540 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231078 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747297 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231077 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615539 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231076 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410359 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231075 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615538 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231074 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446215 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231073 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615537 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231072 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 239 422581474768678860409149186560543264977026463134686367379093798154411471562129214054674607 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231071 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615536 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231070 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410357 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231069 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615535 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231068 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479313 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231067 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615534 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231066 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660651 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231065 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615533 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231064 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410355 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231063 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615532 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231062 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 167 604772290237809866094530871784250540895265417300539172476667172209008034151789713527348689 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231061 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615531 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231060 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717131 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231059 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615530 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231058 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410353 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231057 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615529 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231056 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 10771 9376749834714905546169033106301164267896140069556219645678527319552905180888393107331467 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231055 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615528 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231054 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446211 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231053 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615527 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231052 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410351 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231051 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615526 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231050 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747293 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615525 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231048 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231119 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566459 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap6_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231048 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231047 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615524 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231046 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410349 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231045 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615523 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231044 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446209 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231043 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615522 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231042 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479311 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231041 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615521 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231040 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410347 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231039 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615520 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231038 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231039 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231037 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615519 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231036 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747291 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231035 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615518 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231034 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410345 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231033 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615517 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231032 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660649 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231031 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615516 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231030 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 227 444920583567023117347077777920571983830437553696872430852878492329975073583034723167697053 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231029 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615515 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231028 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410343 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231027 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615514 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231026 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566457 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231025 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615513 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231024 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446205 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231023 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615512 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231022 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410341 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231021 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615511 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231020 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012159 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231019 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615510 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231018 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231017 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615509 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231016 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410339 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231015 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615508 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231014 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446203 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231013 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615507 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231012 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 67 1507417499547973845340099337133878213873273502823731967217961459088124503035057942672645239 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231011 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615506 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231010 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410337 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231009 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615505 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231008 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747287 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231007 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615504 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231006 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 26891 3755790876862677016019733575842097368246228280435463233185951350225143791727674023244477 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231005 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615503 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231004 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410335 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231003 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615502 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231002 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891151 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231001 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615501 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231000 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688561 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230999 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615500 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230998 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410333 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230997 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615499 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230996 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352793 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230995 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615498 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230994 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446199 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230993 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615497 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230992 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410331 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230991 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615496 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230990 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479307 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230989 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615495 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230988 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230989 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230987 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615494 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230986 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410329 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230985 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615493 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230984 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446197 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230983 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615492 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230982 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566453 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230981 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615491 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230980 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410327 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231049 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615490 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap6 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231118 : ℕ) m with hc0 | hc0
  · exact gap6_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231048 : ℕ) m with hc1 | hc1
  · exact gap6_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067230979 : ℕ) m with hc2 | hc2
  · exact gap6_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 7 * 210` and `P + 8 * 210`. -/
theorem gap7_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231328 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231398 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231397 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615699 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231396 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 167 604772290237809866094530871784250540895265417300539172476667172209008034151789713527348691 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231395 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615698 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231394 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410465 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231393 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615697 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231392 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 127 795251751730033445966824059747794018342593107788897966957507226448065682703534505189505759 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231391 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615696 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231390 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 137 737204178611052902465596026189560878317586311599927312435061443495652129221524687292461543 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231389 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615695 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231388 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410463 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231387 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615694 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231386 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747341 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231385 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615693 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231384 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446277 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231383 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615692 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231382 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410461 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231381 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615691 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231380 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479337 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231379 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615690 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231378 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566489 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231377 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615689 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231376 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410459 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231375 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615688 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231374 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446275 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231373 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615687 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231372 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747339 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231371 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615686 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231370 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410457 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231369 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615685 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231368 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231369 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231367 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615684 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231366 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 73 1383520170818003392298447336821504662048072940947808791830183804916497831552724413137907279 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231365 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615683 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231364 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410455 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231363 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615682 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231362 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012177 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231361 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615681 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231360 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231361 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231359 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615680 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231358 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410453 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231357 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615679 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231356 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566487 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231355 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615678 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231354 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446271 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231353 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615677 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231352 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410451 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231351 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615676 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231350 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 83 1216830993611015031780562115517708919632642466134819780766306238059088454257215447699605197 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231349 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615675 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231348 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656543 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231347 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615674 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231346 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410449 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231345 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615673 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231344 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446269 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231343 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615672 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231342 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492739 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231341 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615671 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231340 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410447 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231339 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615670 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231338 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660667 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231337 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615669 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231336 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 151 668854122315988394952229507205098280327876322444967164262274289794068488101648226218988287 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231335 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615668 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231334 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410445 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231333 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615667 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231332 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 157 643292818278434698329851309477514906557384233689108546519766992094932112760183962796606569 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231331 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615666 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231330 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747333 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615665 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231328 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410443 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap7_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231258 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231328 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231327 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615664 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231326 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 101 999970024452616313245412431564057825044646779100891503005974433256478630726226556030368627 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231325 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615663 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231324 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446265 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231323 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615662 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231322 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410441 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231321 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615661 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231320 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891157 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231319 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615660 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231318 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231319 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231317 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615659 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231316 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410439 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231315 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615658 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231314 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446263 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231313 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615657 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231312 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566483 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231311 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615656 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231310 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410437 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231309 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615655 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231308 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 31 3257966853861749923799569535095801300951913699651291671083981218029172313011254263195717139 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231307 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615654 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231306 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 42013 2403945742263448162182816166138334332932885647042345031385604878463912162981669534645639 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231305 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615653 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231304 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410435 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231303 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615652 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231302 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747329 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231301 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615651 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231300 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494283 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231299 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615650 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231298 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410433 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231297 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615649 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231296 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 131 770969255494001890364783630442517865110758203734275128271781814953468257277472382893642987 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231295 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615648 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231294 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446259 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231293 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615647 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231292 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410431 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231291 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615646 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231290 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566481 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231289 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615645 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231288 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747327 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231287 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615644 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231286 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410429 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231285 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615643 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231284 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446257 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231283 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615642 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231282 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 191 528779960574420144700453694177852567170205888425078752898447213397404930384025561042236813 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231281 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615641 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231280 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410427 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231279 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615640 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231278 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231279 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231277 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615639 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231276 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479329 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231275 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615638 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231274 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410425 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231273 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615637 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231272 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 89 1134797443479935366716703995370447644151790165047079121388802446729262266329762720888395857 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231271 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615636 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231270 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660663 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231269 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615635 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231268 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410423 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231267 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615634 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231266 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 317 318602436812978699172828566523564165077316481669369217046067563908215588969554833309360351 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231265 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615633 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231264 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446253 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231263 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615632 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231262 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410421 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231261 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615631 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231260 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747323 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615630 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231258 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231329 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 311 324749107619659960250117863626912669869804902537588558854030282182972159817842064820151869 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap7_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231258 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231257 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615629 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231256 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410419 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231255 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615628 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231254 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446251 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231253 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615627 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231252 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 97 1041205901749631418946254181319276704427931182362783936119622863493859192818029712980074549 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231251 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615626 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231250 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410417 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231249 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615625 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231248 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012171 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231247 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615624 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231246 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747321 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231245 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615623 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231244 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410415 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231243 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615622 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231242 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 26783 3770935760359715029600367979239436968581164346383528424881582263335113381747708701753621 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231241 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615621 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231240 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 10169 9931848998890180709783327326971171239011635823501823365483667790235454981153395826439889 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231239 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615620 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231238 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410413 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231237 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615619 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231236 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660661 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231235 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615618 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231234 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446247 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231233 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615617 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231232 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410411 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231231 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615616 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231230 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 113 893778517431099536617581022902387967517781634417610989412419626184994174365919311142187887 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231229 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615615 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231228 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352801 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231227 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615614 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231226 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410409 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231225 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615613 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231224 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446245 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231223 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615612 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231222 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 71 1422492569995975318842065571661547046894497530833662560614132644491610446526040593789679313 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231221 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615611 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231220 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410407 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231219 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615610 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231218 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747317 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231217 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615609 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231216 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 109 926577729079947226034739959522659085591828666873303135812875392283526070672925524395112213 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231215 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615608 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231214 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410405 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231213 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615607 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231212 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231213 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231211 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615606 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231210 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012169 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231209 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615605 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231208 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410403 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231207 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615604 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231206 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 47 2148871754674771226335886289105741283606581376365745570289434420402220036241465577852494281 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231205 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615603 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231204 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446241 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231203 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615602 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231202 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410401 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231201 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615601 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231200 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 61 1655688073274004059635846812917538366057529912937541668911531438670562978743424297689626741 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231199 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615600 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231198 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479323 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231197 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615599 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231196 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410399 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231195 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615598 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231194 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446239 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231193 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615597 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231192 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 4603 21941553871326145478554563456000399810886231737820995395090901099045044906223958757129531 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231191 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615596 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231190 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410397 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231259 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615595 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap7 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231328 : ℕ) m with hc0 | hc0
  · exact gap7_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231258 : ℕ) m with hc1 | hc1
  · exact gap7_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231189 : ℕ) m with hc2 | hc2
  · exact gap7_p2 m hc2 (by omega)
  · omega


/-- No primes strictly between `P + 8 * 210` and `P + 9 * 210`. -/
theorem gap8_p0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231538 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231608 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231607 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615804 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231606 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 43 2348766801621261572971782688092321868128123829981163762874498087416380039612764701373656549 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231605 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615803 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231604 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410535 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231603 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615802 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231602 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 281 359419830853075614369347528782810819677969127007793743073321771384001216026152605548281963 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231601 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615801 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231600 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 59 1711813092707021146403163654033387124228971604901526132264464707778039689887269189136732739 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231599 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615800 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231598 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410533 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231597 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615799 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231596 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747371 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231595 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615798 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231594 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446319 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231593 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615797 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231592 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410531 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231591 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615796 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231590 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012189 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231589 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615795 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231588 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479353 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231587 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615794 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231586 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410529 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231585 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615793 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231584 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446317 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231583 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615792 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231582 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747369 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231581 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615791 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231580 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410527 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231579 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615790 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231578 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 79 1278442689490053767566919690986960004171004109989747364602574908340561287384163065304648501 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231577 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615789 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231576 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566507 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231575 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615788 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231574 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410525 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231573 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615787 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231572 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 521 193852154452426578959283408038329827887733828578099888298662989940315435131187873625848813 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231571 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615786 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231570 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5779 17476548273008175746285976049138231584964409878731621699879463187213071760399529703939649 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231569 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615785 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231568 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410523 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231567 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615784 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231566 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 61 1655688073274004059635846812917538366057529912937541668911531438670562978743424297689626747 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231565 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615783 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231564 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446313 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231563 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615782 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231562 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410521 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231561 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615781 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231560 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 1933 52248821763949429714323153434024749265136743243243684326747758799226250234531237537023917 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231559 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615780 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231558 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 131 770969255494001890364783630442517865110758203734275128271781814953468257277472382893642989 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231557 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615779 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231556 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410519 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231555 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615778 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231554 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446311 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231553 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615777 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231552 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012187 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231551 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615776 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231550 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410517 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231549 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615775 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231548 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 67 1507417499547973845340099337133878213873273502823731967217961459088124503035057942672645247 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231547 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615774 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231546 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966589 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231545 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615773 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231544 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410515 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231543 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615772 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231542 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660679 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231541 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615771 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231540 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747363 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615770 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231538 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410513 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap8_p1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231468 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime := by
  have h70 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231538 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime := gap_nil _
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231537 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615769 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h70
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231536 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479349 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231535 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615768 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231534 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446307 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231533 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615767 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231532 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410511 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231531 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615766 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231530 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 107 943896938969292033998006126990372339528124529805514409379471194008451791620083010832404033 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231529 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615765 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231528 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 101 999970024452616313245412431564057825044646779100891503005974433256478630726226556030368629 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231527 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615764 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231526 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410509 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231525 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615763 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231524 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446305 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231523 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615762 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231522 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 163 619613328035056733974151261275888590978584814044110685911677409563830317198459399748878721 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231521 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615761 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231520 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410507 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231519 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615760 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231518 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352811 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231517 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615759 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231516 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 83 1216830993611015031780562115517708919632642466134819780766306238059088454257215447699605199 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231515 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615758 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231514 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410505 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231513 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615757 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231512 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747359 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231511 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615756 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231510 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566501 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231509 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615755 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231508 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410503 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231507 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615754 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231506 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 71 1422492569995975318842065571661547046894497530833662560614132644491610446526040593789679317 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231505 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615753 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231504 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446301 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231503 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615752 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231502 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410501 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231501 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615751 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231500 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966587 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231499 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615750 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231498 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747357 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231497 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615749 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231496 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410499 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231495 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615748 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231494 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446299 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231493 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615747 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231492 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688573 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231491 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615746 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231490 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410497 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231489 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615745 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231488 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566499 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231487 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615744 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231486 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 38333 2634726540310287419137209599769646005517682536957452894466997567602440239567706210290539 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231485 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615743 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231484 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410495 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231483 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615742 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231482 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 59 1711813092707021146403163654033387124228971604901526132264464707778039689887269189136732737 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231481 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615741 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231480 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 139 726596924242548544156738529409854966399347659634460732400024588193556415132006346468109579 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231479 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615740 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231478 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410493 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231477 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615739 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231476 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012183 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231475 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615738 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231474 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446295 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231473 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615737 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231472 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410491 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231471 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615736 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231470 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747353 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615735 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231468 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231539 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 193 523300375490747397086977490093107980981913599425855138878774185279297107271237731394130733 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap8_p2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime := by
  have h69 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231468 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime := gap_nil _
  have h68 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231467 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615734 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h69
  have h67 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231466 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410489 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h68
  have h66 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231465 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615733 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h67
  have h65 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231464 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446293 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h66
  have h64 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231463 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615732 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h65
  have h63 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231462 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_fermat 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231463 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h64
  have h62 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231461 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615731 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h63
  have h61 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231460 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410487 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h62
  have h60 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231459 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615730 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h61
  have h59 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231458 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479343 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h60
  have h58 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231457 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615729 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h59
  have h57 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231456 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747351 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h58
  have h56 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231455 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615728 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h57
  have h55 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231454 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410485 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h56
  have h54 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231453 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615727 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h55
  have h53 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231452 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 907 111352781113246138520161693040760573681928693152359472771337836558880200334453012303271479 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h54
  have h52 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231451 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615726 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h53
  have h51 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231450 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 89 1134797443479935366716703995370447644151790165047079121388802446729262266329762720888395859 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h52
  have h50 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231449 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615725 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h51
  have h49 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231448 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410483 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h50
  have h48 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231447 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615724 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h49
  have h47 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231446 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 97 1041205901749631418946254181319276704427931182362783936119622863493859192818029712980074551 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h48
  have h46 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231445 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615723 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h47
  have h45 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231444 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446289 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h46
  have h44 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231443 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615722 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h45
  have h43 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231442 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410481 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h44
  have h42 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231441 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615721 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h43
  have h41 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231440 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 17 5940998380571426331634509152233520019382901452305296576682553985817902453138169538768660673 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h42
  have h40 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231439 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615720 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h41
  have h39 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231438 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 19 5315630129984960401988771346735254754184701299431054831768600934679175879123625376793012181 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h40
  have h38 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231437 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615719 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h39
  have h37 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231436 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410479 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h38
  have h36 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231435 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615718 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h37
  have h35 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231434 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446287 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h36
  have h34 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231433 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615717 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h35
  have h33 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231432 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 13 7768997882285711356752819660613064640731486514553080138738724442992641669488375550697479341 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h34
  have h32 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231431 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615716 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h33
  have h31 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231430 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410477 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h32
  have h30 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231429 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615715 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h31
  have h29 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231428 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 7 14428138924244892519683807941138548618501332098455720257657631108414905957621268879866747347 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h30
  have h28 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231427 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615714 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h29
  have h27 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231426 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 53 1905603254145551842222389728074902647726591031871510222709498448281213994402809097340891159 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h28
  have h26 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231425 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615713 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h27
  have h25 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231424 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410475 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h26
  have h24 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231423 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615712 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h25
  have h23 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231422 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 11 9181542951792204330707877780724530939046302244471821982145765250809485609395352923551566493 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h24
  have h22 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231421 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615711 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h23
  have h21 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231420 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 79 1278442689490053767566919690986960004171004109989747364602574908340561287384163065304648499 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h22
  have h20 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231419 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615710 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h21
  have h19 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231418 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410473 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h20
  have h18 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231417 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615709 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h19
  have h17 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231416 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 37 2729647904586871557778017718593779468365116883491622751448741020510928154144564382677492741 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h18
  have h16 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231415 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615708 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h17
  have h15 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231414 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446283 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h16
  have h14 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231413 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615707 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h15
  have h13 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231412 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410471 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h14
  have h12 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231411 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615706 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h13
  have h11 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231410 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 41 2463340791944249942385040380194386349500227431443659556185449213631813212276802003879688571 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h12
  have h10 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231409 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615705 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h11
  have h9 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231408 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 23 4391172716074532505990724155998688709978666290834349643634931206908884421884734006915966583 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h10
  have h8 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231407 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615704 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h9
  have h7 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231406 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410469 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h8
  have h6 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231405 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615703 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h7
  have h5 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231404 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 5 20199394493942849527557331117593968065901864937838008360720683551780868340669776431813446281 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h6
  have h4 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231403 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615702 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h5
  have h3 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231402 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 29 3482654223093594746130574330619649666534804299627242820813910957203597989770651108933352807 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h4
  have h2 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231401 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615701 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h3
  have h1 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231400 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 3 33665657489904749212595551862656613443169774896396680601201139252968113901116294053022410467 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h2
  have h0 : ∀ m, (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) < m → m < (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231469 : ℕ) → ¬ m.Prime :=
    gap_cons (not_prime_of_factor 2 50498486234857123818893327793984920164754662344595020901801708879452170851674441079533615700 (by decide +kernel) (by decide +kernel) (by decide +kernel)) h1
  exact h0

theorem gap8 : ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231609 → ¬ m.Prime := by
  intro m h1 h2
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231538 : ℕ) m with hc0 | hc0
  · exact gap8_p0 m hc0 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231468 : ℕ) m with hc1 | hc1
  · exact gap8_p1 m hc1 (by omega)
  rcases Nat.lt_or_ge (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067231399 : ℕ) m with hc2 | hc2
  · exact gap8_p2 m hc2 (by omega)
  · omega


/-- The ten members of the Toplic CPAP-10 are prime. -/
theorem cpap_primes : ∀ i, i < 10 → (100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + i * 210).Prime := by
  intro i hi
  interval_cases i
  exacts [pc136, pc137, pc138, pc139, pc140, pc141, pc142, pc143, pc144, pc145]

/-- The gaps of the Toplic CPAP-10 contain no primes. -/
theorem cpap_gaps : ∀ i, i + 1 < 10 →
    ∀ m, 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + i * 210 < m → m < 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 + (i + 1) * 210 → ¬ m.Prime := by
  intro i hi m
  have hi' : i < 9 := by omega
  clear hi
  interval_cases i
  exacts [gap0 m, gap1 m, gap2 m, gap3 m, gap4 m, gap5 m, gap6 m, gap7 m, gap8 m]

/--
The existence of such progressions has been verified for $k≤10$.

This is `erdos_141.variants.first_cases` from `FormalConjectures.ErdosProblems.«141»`:
for every `3 ≤ k ≤ 10` there is a set of `k` consecutive primes in arithmetic
progression, namely the first `k` primes of the CPAP-10 found by Manfred Toplic's
CP10 project in 1998.
-/
theorem erdos_141.variants.first_cases :
    (∀ k ≥ 3, k ≤ 10 → ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength k) := by
  intro k hk3 hk10
  apply exists_witness 100996972469714247637786655587969840329509324689190041803603417758904341703348882159067229719 210 k (by norm_num)
  · intro i hi
    exact cpap_primes i (by omega)
  · intro i hi
    exact cpap_gaps i (by omega)

end Contribution.Erdos141FirstCases
