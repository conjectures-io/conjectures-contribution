import FormalConjectures.ErdosProblems.«357»

namespace Contribution.Subb

theorem distinctSums_injective {ι α : Type*} [LinearOrder ι] [AddCommMonoid α]
    {a : ι → α} (ha : Erdos357.HasDistinctSums a) : Function.Injective a := by
  intro i j hij
  have heq : ({i} : Finset ι) = {j} := ha
    (by simpa using (Set.ordConnected_singleton : Set.OrdConnected ({i} : Set ι)))
    (by simpa using (Set.ordConnected_singleton : Set.OrdConnected ({j} : Set ι)))
    (by simpa using hij)
  simpa using heq

theorem distinctSums_strictMono {ι α : Type*} [LinearOrder ι]
    [LinearOrder α] [AddCommMonoid α] {a : ι → α}
    (ha : Erdos357.HasDistinctSums a) (hm : Monotone a) : StrictMono a := by
  intro i j hij
  exact lt_of_le_of_ne (hm hij.le) (fun h => hij.ne (distinctSums_injective ha h))

theorem monotone_extremal_eq (n : ℕ) : Erdos357.h n = Erdos357.f n := by
  unfold Erdos357.h Erdos357.f
  congr 1
  ext k
  constructor
  · rintro ⟨a, hr, hm, hd⟩
    exact ⟨a, hr, distinctSums_strictMono hd hm, hd⟩
  · rintro ⟨a, hr, hm, hd⟩
    exact ⟨a, hr, hm.monotone, hd⟩

end Contribution.Subb
