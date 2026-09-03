import Mathlib
import FormalConjectures.ErdosProblems.«242»

/-!
# Erdős 242: improving the residual prime class from `1 mod 12` to `1 mod 24`

The published parent contribution listed in `sources.md` reduces Erdős 242 to
prime denominators congruent to `1` modulo `12`. This standalone follow-up
formalizes the additional classical family `n ≡ 5 (mod 8)` and proves that it
discharges exactly the `13 mod 24` half of that residual class. Consequently,
the parent's prime obligation may be replaced by primes congruent to `1`
modulo `24`.

No declaration from the parent is imported: contribution artifacts elaborate
independently. The theorem `use_with_mod_twelve_prime_reduction` states the
composition point explicitly.
-/

namespace Contribution.Erdos242ModTwentyFour

/-- The exact ordered, positive, three-term Egyptian-fraction conclusion of
`Erdos242.erdos_242` for a fixed denominator `n`. -/
def Decomp (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z

/-- The explicit `n ≡ 5 (mod 8)` family. If `n = 8k + 5`, the witnesses are
`2(k+1)`, `n(k+1)`, and `2n(k+1)`. -/
theorem mod_eight_five_family
    (n : ℕ) (hn : 2 < n) (hmod : n % 8 = 5) : Decomp n := by
  let k := n / 8
  have hnrep : n = 8 * k + 5 := by
    have h := Nat.mod_add_div n 8
    omega
  refine ⟨2 * (k + 1), n * (k + 1), 2 * n * (k + 1), by omega, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · rw [hnrep]
    push_cast
    field_simp
    ring

/-- Inside residue class `1 mod 12`, the part not congruent to `1 mod 24`
lies in residue class `5 mod 8` (equivalently, it is `13 mod 24`). -/
theorem mod_eight_five_of_mod_twelve_one_of_mod_twenty_four_ne_one
    (n : ℕ) (h12 : n % 12 = 1) (h24 : n % 24 ≠ 1) : n % 8 = 5 := by
  omega

/-- Any hypothesis solving primes `1 mod 24` already solves primes `1 mod 12`:
the only additional case is handled by `mod_eight_five_family`. This is the
exact bridge needed by the published parent reduction. -/
theorem primes_mod_twelve_of_primes_mod_twenty_four
    (h24 : ∀ p : ℕ, p.Prime → p % 24 = 1 → Decomp p) :
    ∀ p : ℕ, p.Prime → p % 12 = 1 → Decomp p := by
  intro p hp hp12
  by_cases hp24 : p % 24 = 1
  · exact h24 p hp hp24
  · exact mod_eight_five_family p (by have := hp.two_le; omega)
      (mod_eight_five_of_mod_twelve_one_of_mod_twenty_four_ne_one p hp12 hp24)

/-- The residual prime obligations `1 mod 12` and `1 mod 24` are equivalent
after adding the `5 mod 8` family. The reverse direction is restriction. -/
theorem primes_mod_twelve_iff_primes_mod_twenty_four :
    (∀ p : ℕ, p.Prime → p % 12 = 1 → Decomp p) ↔
      (∀ p : ℕ, p.Prime → p % 24 = 1 → Decomp p) := by
  constructor
  · intro h12 p hp hp24
    exact h12 p hp (by omega)
  · exact primes_mod_twelve_of_primes_mod_twenty_four

/-- A concrete use of the new family: for `n = 13` the generated witnesses
are `4 < 26 < 52`. -/
theorem decomp_thirteen : Decomp 13 := by
  refine ⟨4, 26, 52, by norm_num, by norm_num, by norm_num, ?_⟩
  norm_num

/-- Minimal integration site for a standalone contribution artifact. Given a
previous reduction from all denominators to primes `1 mod 12`, the bridge above
replaces its remaining assumption by primes `1 mod 24`. -/
theorem use_with_mod_twelve_prime_reduction
    (reduce12 :
      (∀ p : ℕ, p.Prime → p % 12 = 1 → Decomp p) →
        ∀ n : ℕ, 2 < n → Decomp n)
    (h24 : ∀ p : ℕ, p.Prime → p % 24 = 1 → Decomp p) :
    ∀ n : ℕ, 2 < n → Decomp n :=
  reduce12 (primes_mod_twelve_of_primes_mod_twenty_four h24)

end Contribution.Erdos242ModTwentyFour
