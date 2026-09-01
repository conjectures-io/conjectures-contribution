import Mathlib
import FormalConjectures.ErdosProblems.«723»

/-!
Erdős Problem 723, variant `prime_power_is_projplane_order`:
for every prime power `n` there exists a finite projective plane of order `n`.

Witness: the classical plane `PG(2, 𝔽_q)`, realized via Mathlib's
`Configuration.ofField` instance on `ℙ K (Fin 3 → K)` with `K = GaloisField p k`.
The order is computed from `Configuration.ProjectivePlane.card_points` together
with the cardinality formula `Projectivization.card_of_finrank`.
-/

open Configuration
open scoped LinearAlgebra.Projectivization

namespace Contribution.PrimePowerIsProjplaneOrder

private lemma sq_add_self_inj {a b : ℕ} (h : a ^ 2 + a + 1 = b ^ 2 + b + 1) : a = b := by
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    have h1 : a ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hlt.le 2
    omega
  · exact heq
  · exfalso
    have h1 : b ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left hgt.le 2
    omega

theorem prime_power_is_projplane_order :
    ∀ n, IsPrimePow n → ∃ (P L : Type) (_ : Membership P L) (_ : Fintype P) (_ : Fintype L)
      (pp : ProjectivePlane P L), pp.order = n := by
  intro n hn
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : DecidableEq (GaloisField p k) := Classical.decEq _
  haveI instF : Fintype (ℙ (GaloisField p k) (Fin 3 → GaloisField p k)) := Fintype.ofFinite _
  have hfinrank : Module.finrank (GaloisField p k) (Fin 3 → GaloisField p k) = 3 :=
    Module.finrank_fin_fun (GaloisField p k)
  have hcardP : Nat.card (ℙ (GaloisField p k) (Fin 3 → GaloisField p k))
      = (p ^ k) ^ 2 + p ^ k + 1 := by
    rw [Projectivization.card_of_finrank (GaloisField p k) (Fin 3 → GaloisField p k) hfinrank]
    simp only [GaloisField.card p k hk.ne']
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  refine ⟨ℙ (GaloisField p k) (Fin 3 → GaloisField p k),
    ℙ (GaloisField p k) (Fin 3 → GaloisField p k),
    inferInstance, instF, instF, inferInstance, ?_⟩
  have hcp := Configuration.ProjectivePlane.card_points
    (ℙ (GaloisField p k) (Fin 3 → GaloisField p k))
    (ℙ (GaloisField p k) (Fin 3 → GaloisField p k))
  rw [← Nat.card_eq_fintype_card, hcardP] at hcp
  exact sq_add_self_inj hcp.symm

end Contribution.PrimePowerIsProjplaneOrder
