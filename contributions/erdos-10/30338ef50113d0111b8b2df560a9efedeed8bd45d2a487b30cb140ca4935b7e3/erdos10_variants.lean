import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Erdős Problem 10: Solved Variants and Lower Threshold Disproofs

Self-contained Lean 4 proofs of both unproved `[research solved]` variants of Erdős Problem 10:
1. `erdos_10_two_pows`: Erdős's 1950 covering-system proof that infinitely many even integers
   cannot be written as a prime plus at most `2` powers of `2`.
2. `erdos_10_grechuk_example`: Bogdan Grechuk's explicit witness `1117175146 ∉ sumPrimeAndTwoPows 3`,
   verified by `512`-adic parity congruence (ruling out `p = 2`) and explicit composite factor
   witnesses for all remaining `492` odd candidates.
-/

namespace Contribution.Erdos10

/--
The set of natural numbers that can be written as a sum
of a prime and at most `k` powers of `2`.
Matches `Erdos10.sumPrimeAndTwoPows` definitionally.
-/
abbrev sumPrimeAndTwoPows (k : ℕ) : Set ℕ :=
  { p + (pows.map (2 ^ ·)).sum | (p : ℕ) (pows : Multiset ℕ) (_ : p.Prime)
    (_ : pows.card ≤ k)}

private lemma pow2_mod_16 (a : ℕ) :
    2 ^ a % 16 = 1 ∨ 2 ^ a % 16 = 2 ∨ 2 ^ a % 16 = 4 ∨ 2 ^ a % 16 = 8 ∨ 2 ^ a % 16 = 0 := by
  rcases a with _ | _ | _ | _ | b
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · right; right; right; right
    have hmul : 2 ^ (b + 4) = 16 * 2 ^ b := by
      rw [Nat.pow_add]
      ring
    rw [hmul, Nat.mul_mod_right]

private lemma two_pow_sum_card_le_two_mod_16 (pows : Multiset ℕ) (hc : pows.card ≤ 2) :
    (pows.map (2 ^ ·)).sum % 16 ≠ 14 := by
  have hcard : pows.card = 0 ∨ pows.card = 1 ∨ pows.card = 2 := by omega
  rcases hcard with h0 | h1 | h2
  · rw [Multiset.card_eq_zero.mp h0]
    norm_num
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
    simp only [Multiset.map_singleton, Multiset.sum_singleton]
    rcases pow2_mod_16 a with h | h | h | h | h <;> omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h2
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    rw [Nat.add_mod]
    rcases pow2_mod_16 a with ha | ha | ha | ha | ha <;>
      rcases pow2_mod_16 b with hb | hb | hb | hb | hb <;>
      omega

private lemma pow2_mod_two_of_ne_zero {x : ℕ} (hx : x ≠ 0) : 2 ^ x % 2 = 0 := by
  have heq : 2 ^ x = 2 * 2 ^ (x - 1) := by
    conv_lhs => rw [show x = (x - 1) + 1 by omega, Nat.pow_succ']
  rw [heq, Nat.mul_mod_right]

private lemma covering_exhaust_24 {c : ℕ}
    (h2 : c % 2 ≠ 0) (h3 : c % 3 ≠ 0) (h5 : c % 4 ≠ 1)
    (h17 : c % 8 ≠ 3) (h13 : c % 12 ≠ 7) : c % 24 = 23 := by
  omega

private lemma pow2_mod_period {q d : ℕ} (hq : 1 < q) (h : 2 ^ d % q = 1) (a : ℕ) :
    2 ^ a % q = 2 ^ (a % d) % q := by
  conv_lhs =>
    rw [← Nat.div_add_mod a d, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, h]
  simp [Nat.mod_eq_of_lt hq]

/-- `m(t) = 399097567 + 984263280 * t` covers all `15 + 16k` odd residue classes via primes
`{3, 5, 7, 13, 17, 241}` and `11 ∣ m(t)`. -/
private def erdosM (t : ℕ) : ℕ :=
  399097567 + 984263280 * t

/-- Even sequence `n(t) = m(t) + 1 ≡ 0 (mod 16)` witnessing `Erdos10.erdos_10.variants.two_pows`. -/
private def erdosN (t : ℕ) : ℕ :=
  erdosM t + 1

private lemma erdosM_mod_16 (t : ℕ) : erdosM t % 16 = 15 := by
  unfold erdosM
  omega

private lemma not_prime_of_covering {p b t q d : ℕ} (hq : q.Prime) (hq16 : q % 16 ≠ 15)
    (hqle : q ≤ 241) (hd : 2 ^ d % q = 1) (hsum : p + 2 ^ b = erdosM t)
    (hc : erdosM t % q = 2 ^ (b % d) % q) : ¬ p.Prime := by
  intro hp
  have hmod : erdosM t % q = 2 ^ b % q := by
    rw [pow2_mod_period hq.one_lt hd b, hc]
  have hsub : p = erdosM t - 2 ^ b := by omega
  have hmeq : 2 ^ b ≡ erdosM t [MOD q] := hmod.symm
  have hdvd : q ∣ p := by
    rw [hsub]
    exact (Nat.modEq_iff_dvd' (by omega)).mp hmeq
  have hpq : p = q := (hp.dvd_iff_eq hq.ne_one).mp hdvd
  subst hpq
  have hge16 : 16 ≤ 2 ^ b := by
    unfold erdosM at hsum
    omega
  have hb4 : 4 ≤ b := by
    by_contra hlt
    have hble : b ≤ 3 := by omega
    have hle8 : 2 ^ b ≤ 8 :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hble).trans (by norm_num)
    omega
  have hpow16 : 2 ^ b % 16 = 0 := by
    have heq : 2 ^ b = 16 * 2 ^ (b - 4) := by
      conv_lhs => rw [show b = (b - 4) + 4 by omega, Nat.pow_add]
      ring
    rw [heq, Nat.mul_mod_right]
  have hm16 : erdosM t % 16 = 15 := erdosM_mod_16 t
  omega

private lemma erdosN_not_mem_two_pows (t : ℕ) : erdosN t ∉ sumPrimeAndTwoPows 2 := by
  rintro ⟨p, pows, hp, hcard, hsum⟩
  unfold erdosN at hsum
  have hm16 : erdosM t % 16 = 15 := erdosM_mod_16 t
  rcases eq_or_ne p 2 with rfl | hpne
  · have hsmod : (pows.map (2 ^ ·)).sum % 16 = 14 := by omega
    exact two_pow_sum_card_le_two_mod_16 pows hcard hsmod
  · have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hpne
    have hsodd : (pows.map (2 ^ ·)).sum % 2 = 1 := by omega
    have hcards : pows.card = 0 ∨ pows.card = 1 ∨ pows.card = 2 := by omega
    rcases hcards with h0 | h1 | h2
    · rw [Multiset.card_eq_zero.mp h0] at hsodd
      norm_num at hsodd
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
      simp only [Multiset.map_singleton, Multiset.sum_singleton] at hsum hsodd
      have ha0 : a = 0 := by
        by_contra hane
        have := pow2_mod_two_of_ne_zero hane
        omega
      subst ha0
      have hpeq : p = erdosM t := by omega
      have h11 : 11 ∣ erdosM t := by
        unfold erdosM
        exact ⟨36281597 + 89478480 * t, by ring⟩
      have hp11 : p = 11 := (hp.dvd_iff_eq (by decide)).mp (hpeq ▸ h11)
      unfold erdosM at hpeq
      omega
    · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h2
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton] at hsum hsodd
      have hab0 : a = 0 ∨ b = 0 := by
        by_contra hneither
        have hae := pow2_mod_two_of_ne_zero (fun h => hneither (Or.inl h))
        have hbe := pow2_mod_two_of_ne_zero (fun h => hneither (Or.inr h))
        omega
      have hex : ∃ c : ℕ, p + 2 ^ c = erdosM t := by
        rcases hab0 with rfl | rfl
        · exact ⟨b, by omega⟩
        · exact ⟨a, by omega⟩
      obtain ⟨c, hpc⟩ := hex
      by_cases h2 : c % 2 = 0
      · have hmod : erdosM t % 3 = 2 ^ (c % 2) % 3 := by
          rw [h2]; unfold erdosM; omega
        exact not_prime_of_covering (by decide : Nat.Prime 3) (by decide) (by decide)
          (by decide : 2 ^ 2 % 3 = 1) hpc hmod hp
      · by_cases h3 : c % 3 = 0
        · have hmod : erdosM t % 7 = 2 ^ (c % 3) % 7 := by
            rw [h3]; unfold erdosM; omega
          exact not_prime_of_covering (by decide : Nat.Prime 7) (by decide) (by decide)
            (by decide : 2 ^ 3 % 7 = 1) hpc hmod hp
        · by_cases h5 : c % 4 = 1
          · have hmod : erdosM t % 5 = 2 ^ (c % 4) % 5 := by
              rw [h5]; unfold erdosM; omega
            exact not_prime_of_covering (by decide : Nat.Prime 5) (by decide) (by decide)
              (by decide : 2 ^ 4 % 5 = 1) hpc hmod hp
          · by_cases h17 : c % 8 = 3
            · have hmod : erdosM t % 17 = 2 ^ (c % 8) % 17 := by
                rw [h17]; unfold erdosM; omega
              exact not_prime_of_covering (by decide : Nat.Prime 17) (by decide) (by decide)
                (by decide : 2 ^ 8 % 17 = 1) hpc hmod hp
            · by_cases h13 : c % 12 = 7
              · have hmod : erdosM t % 13 = 2 ^ (c % 12) % 13 := by
                  rw [h13]; unfold erdosM; omega
                exact not_prime_of_covering (by decide : Nat.Prime 13) (by decide) (by decide)
                  (by decide : 2 ^ 12 % 13 = 1) hpc hmod hp
              · have h241 : c % 24 = 23 := covering_exhaust_24 h2 h3 h5 h17 h13
                have hmod : erdosM t % 241 = 2 ^ (c % 24) % 241 := by
                  rw [h241]
                  have he1 : erdosM t % 241 = 121 := by unfold erdosM; omega
                  have he2 : 2 ^ 23 % 241 = 121 := by norm_num
                  rw [he1, he2]
                exact not_prime_of_covering (by norm_num : Nat.Prime 241) (by decide) (by decide)
                  (by norm_num : 2 ^ 24 % 241 = 1) hpc hmod hp

/--
There are infinitely many even integers not the sum of a prime and `2` powers of `2`.
Matches `Erdos10.erdos_10.variants.two_pows` definitionally.
-/
theorem erdos_10_two_pows :
    Set.Infinite <| {n : ℕ | Even n} \ sumPrimeAndTwoPows 2 := by
  apply Set.infinite_of_injective_forall_mem (f := erdosN)
  · intro t₁ t₂ ht
    unfold erdosN erdosM at ht
    omega
  · intro t
    refine ⟨?_, erdosN_not_mem_two_pows t⟩
    unfold erdosN erdosM
    refine ⟨199548784 + 492131640 * t, by ring⟩

/-! ### Part 2: Grechuk's Explicit Witness `1117175146 ∉ sumPrimeAndTwoPows 3` -/

private def pow2Mod512Val : Fin 10 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 8
  | ⟨4, _⟩ => 16
  | ⟨5, _⟩ => 32
  | ⟨6, _⟩ => 64
  | ⟨7, _⟩ => 128
  | ⟨8, _⟩ => 256
  | ⟨9, _⟩ => 0

private lemma no_triple_mod_512 :
    ∀ i j k : Fin 10, (pow2Mod512Val i + pow2Mod512Val j + pow2Mod512Val k) % 512 ≠ 360 := by
  decide

private lemma pow2_mod_512_exists (a : ℕ) :
    ∃ i : Fin 10, 2 ^ a % 512 = pow2Mod512Val i := by
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | _ | b
  · exact ⟨⟨0, by decide⟩, rfl⟩
  · exact ⟨⟨1, by decide⟩, rfl⟩
  · exact ⟨⟨2, by decide⟩, rfl⟩
  · exact ⟨⟨3, by decide⟩, rfl⟩
  · exact ⟨⟨4, by decide⟩, rfl⟩
  · exact ⟨⟨5, by decide⟩, rfl⟩
  · exact ⟨⟨6, by decide⟩, rfl⟩
  · exact ⟨⟨7, by decide⟩, rfl⟩
  · exact ⟨⟨8, by decide⟩, rfl⟩
  · refine ⟨⟨9, by decide⟩, ?_⟩
    have h : 2 ^ (b + 9) = 512 * 2 ^ b := by
      rw [Nat.pow_add]
      ring
    rw [h, Nat.mul_mod_right]
    rfl

private lemma two_pow_sum_card_le_three_mod_512 (pows : Multiset ℕ) (hc : pows.card ≤ 3) :
    (pows.map (2 ^ ·)).sum % 512 ≠ 360 := by
  have hcard : pows.card = 0 ∨ pows.card = 1 ∨ pows.card = 2 ∨ pows.card = 3 := by omega
  rcases hcard with h0 | h1 | h2 | h3
  · rw [Multiset.card_eq_zero.mp h0]
    norm_num
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
    simp only [Multiset.map_singleton, Multiset.sum_singleton]
    obtain ⟨i, hi⟩ := pow2_mod_512_exists a
    have hbad := no_triple_mod_512 i ⟨9, by decide⟩ ⟨9, by decide⟩
    have h9 : pow2Mod512Val ⟨9, by decide⟩ = 0 := rfl
    omega
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h2
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    obtain ⟨i, hi⟩ := pow2_mod_512_exists a
    obtain ⟨j, hj⟩ := pow2_mod_512_exists b
    have hbad := no_triple_mod_512 i j ⟨9, by decide⟩
    have h9 : pow2Mod512Val ⟨9, by decide⟩ = 0 := rfl
    rw [Nat.add_mod, hi, hj]
    omega
  · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp h3
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
      Multiset.sum_cons, Multiset.sum_singleton]
    obtain ⟨i, hi⟩ := pow2_mod_512_exists a
    obtain ⟨j, hj⟩ := pow2_mod_512_exists b
    obtain ⟨k, hk⟩ := pow2_mod_512_exists c
    have hbad := no_triple_mod_512 i j k
    rw [Nat.add_mod, Nat.add_mod (2 ^ b), hi, hj, hk, Nat.add_mod_mod, ← add_assoc]
    exact hbad

private lemma exp_le_30 {a : ℕ} (h : 2 ^ a ≤ 1117175146) : a ≤ 30 := by
  by_contra hgt
  have hge31 : 31 ≤ a := by omega
  have hbig : 2 ^ 31 ≤ 2 ^ a := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hge31
  norm_num at hbig
  omega

private def wit2 : List (ℕ × ℕ) :=
  [ (7, 159596449), (1381, 808961), (13, 85936549), (7, 159596447), (23, 48572831),
    (11, 101561371), (7, 159596431), (379, 2947691), (37, 30193909), (7, 159596303),
    (1481, 754337), (73, 15303713), (7, 159595279), (1699, 657539), (13, 85934029),
    (7, 159587087), (89, 12551057), (163, 6852227), (7, 159521551), (19391, 57559),
    (59, 18899627), (7, 158997263), (107, 10362491), (101, 10895029), (7, 154802959),
    (11, 95460571), (13, 75612109), (7, 121248527), (2099, 276467), (73, 594977) ]

private def wit3 : List (List (ℕ × ℕ)) :=
  [ [(1381, 808961), (3, 372391713), (5, 223435027), (3, 372391709), (13, 85936547), (3, 372391693), (5, 223435003), (3, 372391629), (47, 23769673), (3, 372391373), (5, 223434619), (3, 372390349), (17, 65715703), (3, 372386253), (5, 223428475), (3, 372369869), (11, 101549461), (3, 372304333), (5, 223330171), (3, 372042189), (17, 65592823), (3, 370993613), (5, 221757307), (3, 366799309), (19, 57032669), (3, 350022093), (5, 196591483), (3, 282913229), (13, 44638787), (3, 14477773)]
  , [(13, 85936549), (3, 372391711), (5, 223435025), (3, 372391703), (17, 65716181), (3, 372391671), (5, 223434977), (3, 372391543), (257, 4346981), (3, 372391031), (5, 223434209), (3, 372388983), (11, 101559887), (3, 372380791), (5, 223421921), (3, 372348023), (877, 1273561), (3, 372216951), (5, 223225313), (3, 371692663), (17, 65469461), (3, 369595511), (5, 220079585), (3, 361206903), (13, 80774329), (3, 327652471), (5, 169747937), (3, 193434743), (17, 2554901)]
  , [(7, 159596447), (3, 372391707), (5, 223435021), (3, 372391691), (17, 65716177), (3, 372391627), (5, 223434925), (3, 372391371), (23, 48572743), (3, 372390347), (5, 223433389), (3, 372386251), (7, 159591767), (3, 372369867), (5, 223408813), (3, 372304331), (101, 11055949), (3, 372042187), (5, 223015597), (3, 370993611), (17, 65222737), (3, 366799307), (5, 216724141), (3, 350022091), (7, 140422487), (3, 282913227), (5, 116060845), (3, 14477771)]
  , [(23, 48572831), (3, 372391699), (5, 223435013), (3, 372391667), (17, 65716169), (3, 372391539), (5, 223434821), (3, 372391027), (11, 101561003), (3, 372388979), (5, 223431749), (3, 372380787), (17, 65712329), (3, 372348019), (5, 223382597), (3, 372216947), (659, 1693667), (3, 371692659), (5, 222596165), (3, 369595507), (17, 64729289), (3, 361206899), (5, 210013253), (3, 327652467), (103, 8240191), (3, 193434739), (5, 8686661)]
  , [(11, 101561371), (3, 372391683), (5, 223434997), (3, 372391619), (17, 65716153), (3, 372391363), (5, 223434613), (3, 372390339), (13, 85935917), (3, 372386243), (5, 223428469), (3, 372369859), (17, 65708473), (3, 372304323), (5, 223330165), (3, 372042179), (47, 23725063), (3, 370993603), (5, 221757301), (3, 366799299), (11, 98510971), (3, 350022083), (5, 196591477), (3, 282913219), (41, 14153761), (3, 14477763)]
  , [(7, 159596431), (3, 372391651), (5, 223434965), (3, 372391523), (17, 65716121), (3, 372391011), (5, 223434197), (3, 372388963), (61, 18314077), (3, 372380771), (5, 223421909), (3, 372348003), (7, 159558991), (3, 372216931), (5, 223225301), (3, 371692643), (7283, 152819), (3, 369595491), (5, 220079573), (3, 361206883), (17, 61768601), (3, 327652451), (5, 169747925), (3, 193434723), (7, 6204751)]
  , [(379, 2947691), (3, 372391587), (5, 223434901), (3, 372391331), (11, 101561179), (3, 372390307), (5, 223433365), (3, 372386211), (257, 4346857), (3, 372369827), (5, 223408789), (3, 372304291), (17, 65685337), (3, 372042147), (5, 223015573), (3, 370993571), (79, 14035271), (3, 366799267), (5, 216724117), (3, 350022051), (17, 57821017), (3, 282913187), (5, 116060821), (3, 14477731)]
  , [(37, 30193909), (3, 372391459), (5, 223434773), (3, 372390947), (17, 65715929), (3, 372388899), (5, 223431701), (3, 372380707), (257, 4346729), (3, 372347939), (5, 223382549), (3, 372216867), (17, 65654489), (3, 371692579), (5, 222596117), (3, 369595427), (19, 57915667), (3, 361206819), (5, 210013205), (3, 327652387), (17, 49925849), (3, 193434659), (5, 8686613)]
  , [(7, 159596303), (3, 372391203), (5, 223434517), (3, 372390179), (17, 65715673), (3, 372386083), (5, 223428373), (3, 372369699), (97, 11515913), (3, 372304163), (5, 223330069), (3, 372042019), (7, 159296783), (3, 370993443), (5, 221757205), (3, 366799139), (41, 26429761), (3, 350021923), (5, 196591381), (3, 282913059), (17, 34135513), (3, 14477603)]
  , [(1481, 754337), (3, 372390691), (5, 223434005), (3, 372388643), (17, 65715161), (3, 372380451), (5, 223421717), (3, 372347683), (199, 5612623), (3, 372216611), (5, 223225109), (3, 371692323), (17, 65469401), (3, 369595171), (5, 220079381), (3, 361206563), (7703, 136319), (3, 327652131), (5, 169747733), (3, 193434403), (17, 2554841)]
  , [(73, 15303713), (3, 372389667), (5, 223432981), (3, 372385571), (17, 65714137), (3, 372369187), (5, 223408405), (3, 372303651), (59, 18926251), (3, 372041507), (5, 223015189), (3, 370992931), (17, 65222617), (3, 366798627), (5, 216723733), (3, 350021411), (11, 89359579), (3, 282912547), (5, 116060437), (3, 14477091)]
  , [(7, 159595279), (3, 372387619), (5, 223430933), (3, 372379427), (17, 65712089), (3, 372346659), (5, 223381781), (3, 372215587), (257, 4342889), (3, 371691299), (5, 222595349), (3, 369594147), (7, 157199119), (3, 361205539), (5, 210012437), (3, 327651107), (547, 1551619), (3, 193433379), (5, 8685845)]
  , [(1699, 657539), (3, 372383523), (5, 223426837), (3, 372367139), (13, 85925837), (3, 372301603), (5, 223328533), (3, 372039459), (211, 5284691), (3, 370990883), (5, 221755669), (3, 366796579), (17, 63741913), (3, 350019363), (5, 196589845), (3, 282910499), (13, 44638157), (3, 14475043)]
  , [(13, 85934029), (3, 372375331), (5, 223418645), (3, 372342563), (17, 65699801), (3, 372211491), (5, 223222037), (3, 371687203), (11, 101178587), (3, 369590051), (5, 220076309), (3, 361201443), (13, 80773069), (3, 327647011), (5, 169744661), (3, 193429283), (131, 331427)]
  , [(7, 159587087), (3, 372358947), (5, 223402261), (3, 372293411), (17, 65683417), (3, 372031267), (5, 223009045), (3, 370982691), (257, 4314217), (3, 366788387), (5, 216717589), (3, 350011171), (7, 140417807), (3, 282902307), (5, 116054293), (3, 14466851)]
  , [(89, 12551057), (3, 372326179), (5, 223369493), (3, 372195107), (17, 65650649), (3, 371670819), (5, 222583061), (3, 369573667), (257, 4281449), (3, 361185059), (5, 210000149), (3, 327630627), (17, 49922009), (3, 193412899), (5, 8673557)]
  , [(163, 6852227), (3, 372260643), (5, 223303957), (3, 371998499), (11, 101358811), (3, 370949923), (5, 221731093), (3, 366755619), (13, 83345357), (3, 349978403), (5, 196565269), (3, 282869539), (17, 34127833), (3, 14434083)]
  , [(7, 159521551), (3, 372129571), (5, 223172885), (3, 371605283), (17, 65454041), (3, 369508131), (5, 220027157), (3, 361119523), (257, 4084841), (3, 327565091), (5, 169695509), (3, 193347363), (7, 6167311)]
  , [(19391, 57559), (3, 371867427), (5, 222910741), (3, 370818851), (17, 65191897), (3, 366624547), (5, 216619285), (3, 349847331), (229, 4290101), (3, 282738467), (5, 115955989), (3, 14303011)]
  , [(59, 18899627), (3, 371343139), (5, 222386453), (3, 369245987), (17, 64667609), (3, 360857379), (5, 209803541), (3, 327302947), (41, 20675393), (3, 193085219), (5, 8476949)]
  , [(7, 158997263), (3, 370294563), (5, 221337877), (3, 366100259), (17, 63619033), (3, 349323043), (5, 196172053), (3, 282214179), (257, 2249833), (3, 13778723)]
  , [(107, 10362491), (3, 368197411), (5, 219240725), (3, 359808803), (17, 61521881), (3, 326254371), (5, 168909077), (3, 192036643), (257, 152681)]
  , [(101, 10895029), (3, 364003107), (5, 215046421), (3, 347225891), (17, 57327577), (3, 280117027), (5, 114383125), (3, 11681571)]
  , [(7, 154802959), (3, 355614499), (5, 206657813), (3, 322060067), (17, 48938969), (3, 187842339), (5, 5331221)]
  , [(11, 95460571), (3, 338837283), (5, 189880597), (3, 271728419), (13, 42057677), (3, 3292963)]
  , [(13, 75612109), (3, 305282851), (5, 156326165), (3, 171065123), (0, 0)]
  , [(7, 121248527), (3, 238173987), (5, 89217301), (0, 0)]
  , [(2099, 276467), (3, 103956259), (0, 0)]
  , [(73, 594977), (0, 0)]
  , [(0, 0)]
  ]

private def checkWit2Aux : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | b, (d, q) :: rest =>
    decide (1 < d ∧ 1 < q ∧ d * q + 2 ^ b = 1117175145) && checkWit2Aux (b + 1) rest

private def checkWit3Row (b c : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | (d, q) :: rest =>
    (if 1117175145 ≤ 2 ^ b + 2 ^ c then true
     else decide (1 < d ∧ 1 < q ∧ d * q + 2 ^ b + 2 ^ c = 1117175145)) &&
    checkWit3Row b (c + 1) rest

private def checkWit3All : ℕ → List (List (ℕ × ℕ)) → Bool
  | _, [] => true
  | b, row :: rows =>
    (row.length == 31 - b) && checkWit3Row b b row && checkWit3All (b + 1) rows

private lemma checkWit2_eq_true : wit2.length == 30 && checkWit2Aux 1 wit2 = true := by
  decide

private lemma checkWit3_eq_true : wit3.length == 30 && checkWit3All 1 wit3 = true := by
  decide

private lemma checkWit2Aux_sound :
    ∀ (L : List (ℕ × ℕ)) (b₀ i : ℕ) (hi : i < L.length),
      checkWit2Aux b₀ L = true →
      1 < L[i].1 ∧ 1 < L[i].2 ∧ L[i].1 * L[i].2 + 2 ^ (b₀ + i) = 1117175145
  | [], _, _, hi, _ => (Nat.not_lt_zero _ hi).elim
  | (d, q) :: rest, b₀, 0, _, h => by
    simp only [checkWit2Aux, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa using h.1
  | (d, q) :: rest, b₀, i + 1, hi, h => by
    simp only [checkWit2Aux, Bool.and_eq_true, decide_eq_true_eq] at h
    have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
    have hrec := checkWit2Aux_sound rest (b₀ + 1) i hi' h.2
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using hrec

private lemma checkWit3Row_sound :
    ∀ (row : List (ℕ × ℕ)) (b c₀ j : ℕ) (hj : j < row.length),
      checkWit3Row b c₀ row = true →
      2 ^ b + 2 ^ (c₀ + j) < 1117175145 →
      1 < row[j].1 ∧ 1 < row[j].2 ∧ row[j].1 * row[j].2 + 2 ^ b + 2 ^ (c₀ + j) = 1117175145
  | [], _, _, _, hj, _, _ => (Nat.not_lt_zero _ hj).elim
  | (d, q) :: rest, b, c₀, 0, _, h, hlt => by
    simp only [checkWit3Row, Bool.and_eq_true] at h
    have hle : ¬ (1117175145 ≤ 2 ^ b + 2 ^ c₀) := by simpa using hlt
    have h1 := h.1
    rw [if_neg hle, decide_eq_true_eq] at h1
    simpa using h1
  | (d, q) :: rest, b, c₀, j + 1, hj, h, hlt => by
    simp only [checkWit3Row, Bool.and_eq_true] at h
    have hj' : j < rest.length := Nat.lt_of_succ_lt_succ hj
    have hrec := checkWit3Row_sound rest b (c₀ + 1) j hj' h.2 (by
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using hlt)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using hrec

private lemma checkWit3All_sound :
    ∀ (rows : List (List (ℕ × ℕ))) (b₀ i : ℕ) (hi : i < rows.length),
      checkWit3All b₀ rows = true →
      rows[i].length = 31 - (b₀ + i) ∧ checkWit3Row (b₀ + i) (b₀ + i) rows[i] = true
  | [], _, _, hi, _ => (Nat.not_lt_zero _ hi).elim
  | row :: rest, b₀, 0, _, h => by
    simp only [checkWit3All, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.1.1, h.1.2⟩
  | row :: rest, b₀, i + 1, hi, h => by
    simp only [checkWit3All, Bool.and_eq_true] at h
    have hi' : i < rest.length := Nat.lt_of_succ_lt_succ hi
    have hrec := checkWit3All_sound rest (b₀ + 1) i hi' h.2
    simpa [Nat.add_assoc, Nat.add_comm 1 i] using hrec

private lemma not_prime_wit2 {p b : ℕ} (hb1 : 1 ≤ b) (hb30 : b ≤ 30)
    (hsum : p + 2 ^ b = 1117175145) : ¬ p.Prime := by
  have hchk := checkWit2_eq_true
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hi : b - 1 < wit2.length := by rw [hchk.1]; omega
  obtain ⟨h1, h2, hmul⟩ := checkWit2Aux_sound wit2 1 (b - 1) hi hchk.2
  rw [show 1 + (b - 1) = b by omega] at hmul
  have hpeq : p = wit2[b - 1].1 * wit2[b - 1].2 := by omega
  rw [hpeq]
  exact Nat.not_prime_mul (by omega) (by omega)

private lemma not_prime_wit3 {p b c : ℕ} (hb1 : 1 ≤ b) (hbc : b ≤ c) (hc30 : c ≤ 30)
    (hp3 : 3 ≤ p) (hsum : p + 2 ^ b + 2 ^ c = 1117175145) : ¬ p.Prime := by
  have hchk := checkWit3_eq_true
  simp only [Bool.and_eq_true, beq_iff_eq] at hchk
  have hi : b - 1 < wit3.length := by rw [hchk.1]; omega
  obtain ⟨hlen, hrow⟩ := checkWit3All_sound wit3 1 (b - 1) hi hchk.2
  rw [show 1 + (b - 1) = b by omega] at hlen hrow
  have hj : c - b < wit3[b - 1].length := by rw [hlen]; omega
  have hlt : 2 ^ b + 2 ^ (b + (c - b)) < 1117175145 := by
    rw [show b + (c - b) = c by omega]
    omega
  obtain ⟨h1, h2, hmul⟩ := checkWit3Row_sound wit3[b - 1] b b (c - b) hj hrow hlt
  rw [show b + (c - b) = c by omega] at hmul
  have hpeq : p = wit3[b - 1][c - b].1 * wit3[b - 1][c - b].2 := by omega
  rw [hpeq]
  exact Nat.not_prime_mul (by omega) (by omega)

/--
Bogdan Grechuk observed that `1117175146` is not the sum of a prime and at most `3` powers of `2`.
Matches `Erdos10.erdos_10.variants.grechuk_example` definitionally.
-/
theorem erdos_10_grechuk_example :
    1117175146 ∉ sumPrimeAndTwoPows 3 := by
  rintro ⟨p, pows, hp, hcard, hsum⟩
  rcases eq_or_ne p 2 with rfl | hpne
  · have hsmod : (pows.map (2 ^ ·)).sum % 512 = 360 := by omega
    exact two_pow_sum_card_le_three_mod_512 pows hcard hsmod
  · have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hpne
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hsodd : (pows.map (2 ^ ·)).sum % 2 = 1 := by omega
    have hcards : pows.card = 0 ∨ pows.card = 1 ∨ pows.card = 2 ∨ pows.card = 3 := by omega
    rcases hcards with h0 | h1 | h2 | h3
    · rw [Multiset.card_eq_zero.mp h0] at hsodd
      norm_num at hsodd
    · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
      simp only [Multiset.map_singleton, Multiset.sum_singleton] at hsum hsodd
      have ha0 : a = 0 := by
        by_contra hane
        have := pow2_mod_two_of_ne_zero hane
        omega
      subst ha0
      have hpeq : p = 3 * 372391715 := by omega
      rw [hpeq] at hp
      exact Nat.not_prime_mul (by decide) (by decide) hp
    · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h2
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton] at hsum hsodd
      have ha0b1 : (a = 0 ∧ 1 ≤ b) ∨ (b = 0 ∧ 1 ≤ a) := by
        by_cases ha : a = 0 <;> by_cases hb : b = 0
        · subst ha; subst hb; norm_num at hsodd
        · exact Or.inl ⟨ha, by omega⟩
        · exact Or.inr ⟨hb, by omega⟩
        · have hae := pow2_mod_two_of_ne_zero ha
          have hbe := pow2_mod_two_of_ne_zero hb
          omega
      have hex : ∃ c, 1 ≤ c ∧ p + 2 ^ c = 1117175145 := by
        rcases ha0b1 with ⟨rfl, hb⟩ | ⟨rfl, ha⟩
        · exact ⟨b, hb, by omega⟩
        · exact ⟨a, ha, by omega⟩
      obtain ⟨c, hc1, hpc⟩ := hex
      have hc30 : c ≤ 30 := exp_le_30 (by omega)
      exact not_prime_wit2 hc1 hc30 hpc hp
    · obtain ⟨a, b, c, rfl⟩ := Multiset.card_eq_three.mp h3
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton] at hsum hsodd
      have hcase :
          (a = 0 ∧ b = 0 ∧ c = 0) ∨
          (∃ x y, 1 ≤ x ∧ x ≤ y ∧ p + 2 ^ x + 2 ^ y = 1117175145) := by
        by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> by_cases hc : c = 0
        · exact Or.inl ⟨ha, hb, hc⟩
        · subst ha; subst hb
          have hce := pow2_mod_two_of_ne_zero hc
          norm_num at hsodd
          omega
        · subst ha; subst hc
          have hbe := pow2_mod_two_of_ne_zero hb
          norm_num at hsodd
          omega
        · subst ha
          rcases le_total b c with hbc | hcb
          · exact Or.inr ⟨b, c, by omega, hbc, by omega⟩
          · exact Or.inr ⟨c, b, by omega, hcb, by omega⟩
        · subst hb; subst hc
          have hae := pow2_mod_two_of_ne_zero ha
          norm_num at hsodd
          omega
        · subst hb
          rcases le_total a c with hac | hca
          · exact Or.inr ⟨a, c, by omega, hac, by omega⟩
          · exact Or.inr ⟨c, a, by omega, hca, by omega⟩
        · subst hc
          rcases le_total a b with hab | hba
          · exact Or.inr ⟨a, b, by omega, hab, by omega⟩
          · exact Or.inr ⟨b, a, by omega, hba, by omega⟩
        · have hae := pow2_mod_two_of_ne_zero ha
          have hbe := pow2_mod_two_of_ne_zero hb
          have hce := pow2_mod_two_of_ne_zero hc
          omega
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨x, y, hx1, hxy, hpxy⟩
      · have hpeq : p = 7 * 159596449 := by omega
        rw [hpeq] at hp
        exact Nat.not_prime_mul (by decide) (by decide) hp
      · have hy_le : 2 ^ y ≤ 1117175146 :=
          le_trans (Nat.le_add_left (2 ^ y) (p + 2 ^ x)) (by rw [hpxy]; decide)
        have hy30 : y ≤ 30 := exp_le_30 hy_le
        exact not_prime_wit3 hx1 hxy hy30 hp3 hpxy hp

/-- Monotonicity of `sumPrimeAndTwoPows` in the bound `k`. -/
theorem sumPrimeAndTwoPows_mono {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) :
    sumPrimeAndTwoPows k₁ ⊆ sumPrimeAndTwoPows k₂ := by
  rintro n ⟨p, pows, hp, hcard, hsum⟩
  exact ⟨p, pows, hp, hcard.trans h, hsum⟩

/-- Direct corollary towards `Erdos10.erdos_10`: `k ≤ 3` cannot represent all integers `≥ 2`. -/
theorem erdos_10_false_for_k_le_three (k : ℕ) (hk : k ≤ 3) :
    sumPrimeAndTwoPows k ≠ Set.univ \ {0, 1} := by
  intro heq
  have hmem : (1117175146 : ℕ) ∈ Set.univ \ {0, 1} := by simp
  rw [← heq] at hmem
  exact erdos_10_grechuk_example (sumPrimeAndTwoPows_mono hk hmem)

end Contribution.Erdos10
