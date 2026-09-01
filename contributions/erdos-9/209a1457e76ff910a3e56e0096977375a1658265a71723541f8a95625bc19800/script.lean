/-
A full proof that the set of odd numbers that are not the sum of a prime and two
powers of 2 (Erdős Problem 9) is infinite.

The argument is a formalization-friendly variant of Crocker's theorem
[R. Crocker, "On the sum of a prime and of two powers of two",
Pacific J. Math. 36 (1971), 103-107], using the Schinzel/Crocker Fermat-number
divisibility trick for distinct powers of two, combined with an explicit
covering system (with free residue classes obtained via a CRT-chosen
multiplier `w`) for the equal-powers case.

Witnesses: `N k = w * ((2 ^ 2 ^ (12 * k) - 1) / G)` where `G` is the huge
cofactor of the Fermat number `F₁₀ = 2 ^ 1024 + 1 = 45592577 * G`.  Dividing
by `G` makes `N < 2 ^ 2 ^ (12 * k)`, so all exponents in a representation
`N = p + 2 ^ a + 2 ^ b` are `< 2 ^ (12 * k)`:
* if `b < a`, with `r = v₂(a - b)`, the Fermat number `F_r = 2 ^ 2 ^ r + 1`
  divides `2 ^ a + 2 ^ b = 2 ^ b * (2 ^ (a - b) + 1)`, and (using the prime
  factor `D = 45592577` instead when `r = 10`) it also divides the witness
  `N`; hence it divides `p`, forcing `p = F_r` (resp. `p = D`), which is
  impossible: mod 16 we have `N ≡ 15`, `F_r ≡ 1` for `r ≥ 2`, `D ≡ 1`, but
  `2 ^ a + 2 ^ b ≢ 14 (mod 16)`, while `r ∈ {0, 1}` forces `N = 15`, which is
  far too small;
* if `a = b` then `N = p + 2 ^ (a + 1)` and an explicit 21-prime covering
  system (all residues mod 720 are covered) produces a prime `q ≤ 18837001`
  dividing `p`, while `p ≥ 2 ^ S` for a huge `S`, a contradiction.
-/
import Mathlib
import FormalConjectures.ErdosProblems.«9»

/-!
# Erdős Problem 9: the set is infinite

A complete, self-contained proof that `Erdos9.Erdos9A` is infinite, following
a Crocker-style argument (see the header comment above for an outline).
-/


namespace Contribution.Erdos9VariantsInfinite

/-- The known prime factor `45592577 = 11131 * 2 ^ 12 + 1` of `F₁₀ = 2 ^ 1024 + 1`. -/
def D : ℕ := 45592577

/-- The cofactor `(2 ^ 1024 + 1) / D`. -/
def G : ℕ := 3942951359960012586542991835686376608231592127249807732373409846031135195659174148737161255930050543559319182152642816343958573976075461198274610155058226350701077796608546283231637018483208223116080561800334422176622099740983337736621316898600121619871377542107047343253864459964167331555646795960321

/-- A multiplier chosen by CRT so that an explicit covering system handles the
equal-powers case for `N k = w * ((2 ^ 2 ^ (12 * k) - 1) / G)`. -/
def w : ℕ := 204311955294921223928488993521357990611965542169291717527489446980729027800254881797650316036574964115384975588960159879469622440176805236270494726592161852031893916769063092104470505746572286497728262493534945223484295968033

/-- The covering data: entries `(q, m, E, γ)` where `q` is a prime with
`2 ^ m ≡ 1 (mod q)`, where `E = 2 ^ (12 * k) % m` for every `k ≥ 1`, and where
the class `c ≡ γ (mod m)` is killed, i.e. `q` divides `N k - 2 ^ c` for such `c`. -/
def Klass : List (ℕ × ℕ × ℕ × ℕ) :=
  [(7, 3, 1, 0), (31, 5, 1, 4), (73, 9, 1, 7), (13, 12, 4, 11), (11, 10, 6, 6),
   (151, 15, 1, 5), (19, 18, 10, 1), (331, 30, 16, 2), (41, 20, 16, 8),
   (241, 24, 16, 17), (37, 36, 28, 13), (109, 36, 28, 31), (61, 60, 16, 38),
   (673, 48, 16, 29), (97, 48, 16, 5), (18837001, 90, 46, 82), (23311, 45, 1, 22),
   (631, 45, 1, 40), (1321, 60, 16, 58), (54001, 180, 136, 10), (181, 180, 136, 100)]


lemma GD_eq : G * D = 2 ^ 2 ^ 10 + 1 := by
  rw [show (2:ℕ) ^ 10 = 256 * 4 from by norm_num, pow_mul]
  decide

lemma G_pos : 0 < G := by decide

lemma w_pos : 0 < w := by decide

lemma w_mod16 : w % 16 = 1 := by decide

lemma G_mod16 : G % 16 = 1 := by decide

lemma w_lt : w < 2 ^ 250 * (2 ^ 250 * 2 ^ 250) := by decide

lemma wA : 3 * G + 2 ≤ w * 2 ^ 255 := by decide

lemma wB : w * 2 ^ 253 ≤ G := by decide

lemma D_mod16 : D % 16 = 1 := by decide

lemma Klass_facts : ∀ t ∈ Klass,
    1 < t.1 ∧ t.1 ≤ 18837001 ∧ t.2.1 ∣ 720 ∧
    2 ^ t.2.1 % t.1 = 1 ∧ 2 ^ 12 % t.2.1 = t.2.2.1 ∧
    t.2.2.1 * t.2.2.1 % t.2.1 = t.2.2.1 ∧
    (w * 2 ^ t.2.2.1) % t.1 = (2 ^ t.2.2.2 * G + w) % t.1 ∧
    Nat.Coprime t.1 G := by decide

/-- The covering predicate: some entry of `Klass` kills the class of `r`. -/
def covered (r : ℕ) : Prop := ∃ t ∈ Klass, r % t.2.1 = t.2.2.2

instance : DecidablePred covered := fun r => by unfold covered; infer_instance

lemma covered_chunk0 : ∀ r < 120, covered r := by decide
lemma covered_chunk1 : ∀ r < 120, covered (120 + r) := by decide
lemma covered_chunk2 : ∀ r < 120, covered (240 + r) := by decide
lemma covered_chunk3 : ∀ r < 120, covered (360 + r) := by decide
lemma covered_chunk4 : ∀ r < 120, covered (480 + r) := by decide
lemma covered_chunk5 : ∀ r < 120, covered (600 + r) := by decide

lemma Klass_cover : ∀ r < 720, ∃ t ∈ Klass, r % t.2.1 = t.2.2.2 := by
  intro r hr
  have h : covered r := by
    rcases Nat.lt_or_ge r 120 with h0 | h0
    · exact covered_chunk0 r h0
    · rcases Nat.lt_or_ge r 240 with h1 | h1
      · have := covered_chunk1 (r - 120) (by omega)
        rwa [show 120 + (r - 120) = r from by omega] at this
      · rcases Nat.lt_or_ge r 360 with h2 | h2
        · have := covered_chunk2 (r - 240) (by omega)
          rwa [show 240 + (r - 240) = r from by omega] at this
        · rcases Nat.lt_or_ge r 480 with h3 | h3
          · have := covered_chunk3 (r - 360) (by omega)
            rwa [show 360 + (r - 360) = r from by omega] at this
          · rcases Nat.lt_or_ge r 600 with h4 | h4
            · have := covered_chunk4 (r - 480) (by omega)
              rwa [show 480 + (r - 480) = r from by omega] at this
            · have := covered_chunk5 (r - 600) (by omega)
              rwa [show 600 + (r - 600) = r from by omega] at this
  exact h

/-- `2 ^ x` mod `q` only depends on `x` mod `m` whenever `2 ^ m ≡ 1 (mod q)`. -/
lemma pow_mod_cycle {q m : ℕ} (h : 2 ^ m % q = 1 % q) (x : ℕ) :
    2 ^ x % q = 2 ^ (x % m) % q := by
  conv_lhs => rw [← Nat.div_add_mod x m, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, h, ← Nat.pow_mod, one_pow, ← Nat.mul_mod, one_mul]

/-- If `E` is a fixed point of multiplication by itself mod `m` (with
`2 ^ 12 % m = E`), then `2 ^ (12 * k) % m = E` for all `k ≥ 1`. -/
lemma pow12_mod (m E : ℕ) (hbase : 2 ^ 12 % m = E) (hstep : E * E % m = E) :
    ∀ k, 1 ≤ k → 2 ^ (12 * k) % m = E := by
  intro k hk
  induction k with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_or_ge t 1 with ht | ht
    · have ht0 : t = 0 := by omega
      subst ht0
      simpa using hbase
    · have h : 2 ^ (12 * (t + 1)) = 2 ^ (12 * t) * 2 ^ 12 := by
        rw [show 12 * (t + 1) = 12 * t + 12 from by ring, pow_add]
      rw [h, Nat.mul_mod, ih ht, hbase, hstep]

/-- The covering-case killer: if `c % m = γ` for a covering entry, then the
corresponding prime divides `p` whenever `(p + 2 ^ c) * G + w = w * 2 ^ 2 ^ (12 * k)`. -/
lemma killer {q m E γ : ℕ} (hq1 : 1 < q) (hcyc : 2 ^ m % q = 1)
    (hbase : 2 ^ 12 % m = E) (hstep : E * E % m = E)
    (htar : (w * 2 ^ E) % q = (2 ^ γ * G + w) % q)
    (hqG : Nat.Coprime q G)
    {k c p : ℕ} (hk : 1 ≤ k) (hc : c % m = γ)
    (heq : (p + 2 ^ c) * G + w = w * 2 ^ 2 ^ (12 * k)) :
    q ∣ p := by
  have hcyc' : 2 ^ m % q = 1 % q := by
    rw [hcyc, Nat.mod_eq_of_lt hq1]
  have h1 : (2:ℕ) ^ 2 ^ (12 * k) ≡ 2 ^ E [MOD q] := by
    show 2 ^ 2 ^ (12 * k) % q = 2 ^ E % q
    rw [pow_mod_cycle hcyc' (2 ^ (12 * k)), pow12_mod m E hbase hstep k hk]
  have h2 : (2:ℕ) ^ c ≡ 2 ^ γ [MOD q] := by
    show 2 ^ c % q = 2 ^ γ % q
    rw [pow_mod_cycle hcyc' c, hc]
  have htar' : (w * 2 ^ E) ≡ 2 ^ γ * G + w [MOD q] := htar
  have e1 : p * G + (2 ^ c * G + w) = w * 2 ^ 2 ^ (12 * k) := by
    rw [← heq]; ring
  have key : p * G + (2 ^ c * G + w) ≡ 0 + (2 ^ c * G + w) [MOD q] := by
    calc p * G + (2 ^ c * G + w) = w * 2 ^ 2 ^ (12 * k) := e1
    _ ≡ w * 2 ^ E [MOD q] := Nat.ModEq.mul_left w h1
    _ ≡ 2 ^ γ * G + w [MOD q] := htar'
    _ ≡ 2 ^ c * G + w [MOD q] := Nat.ModEq.add_right w (Nat.ModEq.mul_right G h2.symm)
    _ = 0 + (2 ^ c * G + w) := (zero_add _).symm
  have hdvd : q ∣ p * G :=
    Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_right_cancel' _ key)
  exact hqG.dvd_of_dvd_mul_right hdvd

/-- `2 ^ a - 1 ∣ 2 ^ (a * t) - 1`. -/
lemma pow_sub_one_dvd (a t : ℕ) : (2:ℕ) ^ a - 1 ∣ 2 ^ (a * t) - 1 := by
  have h := Nat.sub_dvd_pow_sub_pow (2 ^ a) 1 t
  rwa [one_pow, ← pow_mul] at h

/-- For odd `u`, `x + 1 ∣ x ^ u + 1`. -/
lemma pow_add_one_dvd (x u : ℕ) (hu : Odd u) : x + 1 ∣ x ^ u + 1 := by
  have h1 := sub_dvd_pow_sub_pow (x:ℤ) (-1) u
  rw [hu.neg_one_pow, sub_neg_eq_add, sub_neg_eq_add] at h1
  have h3 : (((x + 1 : ℕ)):ℤ) ∣ (((x ^ u + 1 : ℕ)):ℤ) := by
    push_cast
    exact h1
  exact_mod_cast h3

/-- `F_r = 2 ^ 2 ^ r + 1` divides `2 ^ 2 ^ (r + 1) - 1`. -/
lemma fermat_dvd_next (r : ℕ) : (2:ℕ) ^ 2 ^ r + 1 ∣ 2 ^ 2 ^ (r + 1) - 1 := by
  set x : ℕ := 2 ^ 2 ^ r with hx
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  obtain ⟨y, hy⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have h1 : (2:ℕ) ^ 2 ^ (r + 1) = x * x := by
    rw [hx, ← pow_add]
    congr 1
    rw [pow_succ]
    ring
  refine ⟨y, ?_⟩
  have h2 : (y + 1) * (y + 1) = y * y + 2 * y + 1 := by ring
  have h3 : (y + 1 + 1) * y = y * y + 2 * y := by ring
  rw [h1, hy, h2, h3]
  omega

/-- `2 ^ 2 ^ i - 1 ∣ 2 ^ 2 ^ M - 1` for `i ≤ M`. -/
lemma pow2_sub_one_dvd {i M : ℕ} (hiM : i ≤ M) : (2:ℕ) ^ 2 ^ i - 1 ∣ 2 ^ 2 ^ M - 1 := by
  have h1 : 2 ^ M = 2 ^ i * 2 ^ (M - i) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h1]
  exact pow_sub_one_dvd (2 ^ i) (2 ^ (M - i))

/-- The Fermat cofactor `G` is coprime to every Fermat number `F_r` with `r ≠ 10`. -/
lemma coprime_F {r : ℕ} (hr : r ≠ 10) : Nat.Coprime (2 ^ 2 ^ r + 1) G := by
  set x : ℕ := 2 ^ 2 ^ r with hx
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hGF : G ∣ 2 ^ 2 ^ 10 + 1 := ⟨D, GD_eq.symm⟩
  set g : ℕ := Nat.gcd (x + 1) G with hg
  have hg1 : g ∣ x + 1 := Nat.gcd_dvd_left _ _
  have hg2 : g ∣ G := Nat.gcd_dvd_right _ _
  have h2x : 2 ∣ x := by
    rw [hx]
    exact dvd_pow_self 2 (Nat.pow_pos (by norm_num)).ne'
  have hg2' : g ∣ 2 := by
    rcases Nat.lt_or_ge r 10 with hr10 | hr10
    · have h1 : x + 1 ∣ 2 ^ 2 ^ (r + 1) - 1 := fermat_dvd_next r
      have h2 : (2:ℕ) ^ 2 ^ (r + 1) - 1 ∣ 2 ^ 2 ^ 10 - 1 := pow2_sub_one_dvd (by omega)
      have h3 : g ∣ 2 ^ 2 ^ 10 - 1 := (hg1.trans h1).trans h2
      have h4 : g ∣ 2 ^ 2 ^ 10 + 1 := hg2.trans hGF
      have h5 := Nat.dvd_sub h4 h3
      have h6 : (1:ℕ) ≤ 2 ^ 2 ^ 10 := Nat.one_le_two_pow
      have he : (2:ℕ) ^ 2 ^ 10 + 1 - (2 ^ 2 ^ 10 - 1) = 2 := by omega
      rwa [he] at h5
    · have hr11 : 11 ≤ r := by omega
      have h1 : (2:ℕ) ^ 2 ^ 10 + 1 ∣ 2 ^ 2 ^ (10 + 1) - 1 := fermat_dvd_next 10
      have h2 : (2:ℕ) ^ 2 ^ (10 + 1) - 1 ∣ 2 ^ 2 ^ r - 1 := pow2_sub_one_dvd (by omega)
      have h4 : g ∣ x - 1 := by
        rw [hx]
        exact hg2.trans (hGF.trans (h1.trans h2))
      have h5 := Nat.dvd_sub hg1 h4
      have he : x + 1 - (x - 1) = 2 := by omega
      rwa [he] at h5
  refine Nat.coprime_iff_gcd_eq_one.mpr ?_
  rw [← hg]
  rcases (Nat.dvd_prime Nat.prime_two).mp hg2' with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hg1
    omega

/- ### The witnesses -/

/-- The witness quotient `Q k = (2 ^ 2 ^ (12 * k) - 1) / G`. -/
def Q (k : ℕ) : ℕ := (2 ^ 2 ^ (12 * k) - 1) / G

/-- The witness numbers. -/
def N (k : ℕ) : ℕ := w * Q k

lemma G_dvd {k : ℕ} (hk : 1 ≤ k) : G ∣ 2 ^ 2 ^ (12 * k) - 1 := by
  have h1 : G ∣ 2 ^ 2 ^ 10 + 1 := ⟨D, GD_eq.symm⟩
  have h2 : (2:ℕ) ^ 2 ^ 10 + 1 ∣ 2 ^ 2 ^ (10 + 1) - 1 := fermat_dvd_next 10
  have h3 : (2:ℕ) ^ 2 ^ (10 + 1) - 1 ∣ 2 ^ 2 ^ (12 * k) - 1 := pow2_sub_one_dvd (by omega)
  exact h1.trans (h2.trans h3)

lemma QG {k : ℕ} (hk : 1 ≤ k) : G * Q k + 1 = 2 ^ 2 ^ (12 * k) := by
  unfold Q
  rw [Nat.mul_div_cancel' (G_dvd hk), Nat.sub_add_cancel Nat.one_le_two_pow]

lemma N_eq {k : ℕ} (hk : 1 ≤ k) : N k * G + w = w * 2 ^ 2 ^ (12 * k) := by
  rw [← QG hk]
  unfold N
  ring

lemma N_mod16 {k : ℕ} (hk : 1 ≤ k) : N k % 16 = 15 := by
  have hNeq := N_eq hk
  have h16 : (16:ℕ) ∣ 2 ^ 2 ^ (12 * k) := by
    have h4 : 4 ≤ 2 ^ (12 * k) := by
      calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (12 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc (16:ℕ) = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ 2 ^ (12 * k) := pow_dvd_pow 2 h4
  obtain ⟨e, he⟩ := h16
  have h2 : w * 2 ^ 2 ^ (12 * k) % 16 = 0 := by
    rw [he, show w * (16 * e) = 16 * (w * e) by ring, Nat.mul_mod_right]
  have h1 : N k * G % 16 = N k % 16 := by
    rw [Nat.mul_mod, G_mod16, mul_one, Nat.mod_mod]
  have hw := w_mod16
  omega

/- ### mod 16 helpers -/

lemma pow2_mod16_ge (a : ℕ) (h : 4 ≤ a) : 2 ^ a % 16 = 0 := by
  obtain ⟨e, he⟩ : (16:ℕ) ∣ 2 ^ a := by
    calc (16:ℕ) = 2 ^ 4 := by norm_num
    _ ∣ 2 ^ a := pow_dvd_pow 2 h
  omega

lemma sum_pow_mod16_ne14 (a b : ℕ) : (2 ^ a + 2 ^ b) % 16 ≠ 14 := by
  rcases Nat.lt_or_ge a 4 with ha | ha <;> rcases Nat.lt_or_ge b 4 with hb | hb
  · interval_cases a <;> interval_cases b <;> decide
  · have hb0 := pow2_mod16_ge b hb
    interval_cases a <;> omega
  · have ha0 := pow2_mod16_ge a ha
    interval_cases b <;> omega
  · have ha0 := pow2_mod16_ge a ha
    have hb0 := pow2_mod16_ge b hb
    omega

lemma sum_pow_mod16_eq12 (a b : ℕ) (h : (2 ^ a + 2 ^ b) % 16 = 12) :
    2 ^ a + 2 ^ b = 12 := by
  rcases Nat.lt_or_ge a 4 with ha | ha <;> rcases Nat.lt_or_ge b 4 with hb | hb
  · interval_cases a <;> interval_cases b <;> revert h <;> decide
  · have hb0 := pow2_mod16_ge b hb
    interval_cases a <;> omega
  · have ha0 := pow2_mod16_ge a ha
    interval_cases b <;> omega
  · have ha0 := pow2_mod16_ge a ha
    have hb0 := pow2_mod16_ge b hb
    omega

lemma sum_pow_mod16_eq10 (a b : ℕ) (h : (2 ^ a + 2 ^ b) % 16 = 10) :
    2 ^ a + 2 ^ b = 10 := by
  rcases Nat.lt_or_ge a 4 with ha | ha <;> rcases Nat.lt_or_ge b 4 with hb | hb
  · interval_cases a <;> interval_cases b <;> revert h <;> decide
  · have hb0 := pow2_mod16_ge b hb
    interval_cases a <;> omega
  · have ha0 := pow2_mod16_ge a ha
    interval_cases b <;> omega
  · have ha0 := pow2_mod16_ge a ha
    have hb0 := pow2_mod16_ge b hb
    omega

/- ### No representation -/

/-- The witnesses have no representation `N k = p + 2 ^ a + 2 ^ b` with `p` prime
and `b ≤ a`. -/
lemma no_rep {k : ℕ} (hk : 1 ≤ k) {p a b : ℕ} (hp : p.Prime) (hba : b ≤ a)
    (heq : N k = p + 2 ^ a + 2 ^ b) : False := by
  have hbig : (2:ℕ) ^ 12 ≤ 2 ^ (12 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4096 : (4096:ℕ) ≤ 2 ^ (12 * k) := by
    calc (4096:ℕ) = 2 ^ 12 := by norm_num
    _ ≤ 2 ^ (12 * k) := hbig
  obtain ⟨S, hS⟩ : ∃ S, S + 255 = 2 ^ (12 * k) := ⟨2 ^ (12 * k) - 255, by omega⟩
  have hSbig : 3841 ≤ S := by omega
  have hNeq := N_eq hk
  have hp2 := hp.two_le
  -- upper bound : N k < 2 ^ (S + 2)
  have hup : N k < 2 ^ (S + 2) := by
    have h1 : N k * G + w = (w * 2 ^ 253) * 2 ^ (S + 2) := by
      rw [hNeq, mul_assoc, ← pow_add]
      congr 2
      omega
    have h3 : (w * 2 ^ 253) * 2 ^ (S + 2) ≤ G * 2 ^ (S + 2) :=
      Nat.mul_le_mul_right _ wB
    have h5 : G * N k < G * 2 ^ (S + 2) := by
      have hw0 := w_pos
      calc G * N k = N k * G := by ring
      _ < N k * G + w := by omega
      _ = (w * 2 ^ 253) * 2 ^ (S + 2) := h1
      _ ≤ G * 2 ^ (S + 2) := h3
    exact lt_of_mul_lt_mul_left h5 (Nat.zero_le G)
  -- lower bound : 3 * 2 ^ S ≤ N k
  have hlow : 3 * 2 ^ S ≤ N k := by
    have h1 : N k * G + w = (w * 2 ^ 255) * 2 ^ S := by
      rw [hNeq, mul_assoc, ← pow_add]
      congr 2
      omega
    have h2 : (3 * G + 2) * 2 ^ S ≤ (w * 2 ^ 255) * 2 ^ S :=
      Nat.mul_le_mul_right _ wA
    have h3 : (3 * G + 2) * 2 ^ S = 3 * G * 2 ^ S + 2 * 2 ^ S := by ring
    have h4 : w ≤ 2 * 2 ^ S := by
      have h41 : w ≤ 2 ^ 250 * (2 ^ 250 * 2 ^ 250) := le_of_lt w_lt
      have h42 : (1:ℕ) ≤ 2 ^ (S + 1 - 750) := Nat.one_le_two_pow
      have h43 : (2:ℕ) ^ 250 * (2 ^ 250 * 2 ^ 250) * 2 ^ (S + 1 - 750) = 2 ^ (S + 1) := by
        rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add, ← pow_add,
          show 250 + (250 + (250 + (S + 1 - 750))) = S + 1 from by omega]
      calc w = w * 1 := by ring
      _ ≤ 2 ^ 250 * (2 ^ 250 * 2 ^ 250) * 2 ^ (S + 1 - 750) := Nat.mul_le_mul h41 h42
      _ = 2 ^ (S + 1) := h43
      _ = 2 * 2 ^ S := by rw [pow_succ]; ring
    have h6 : G * (3 * 2 ^ S) ≤ G * N k := by
      have h5 : 3 * G * 2 ^ S ≤ N k * G := by omega
      calc G * (3 * 2 ^ S) = 3 * G * 2 ^ S := by ring
      _ ≤ N k * G := h5
      _ = G * N k := by ring
    exact Nat.le_of_mul_le_mul_left h6 G_pos
  rcases Nat.eq_or_lt_of_le hba with hab | hab
  · -- a = b : single power case, N k = p + 2 ^ (a + 1)
    have heq2 : N k = p + 2 ^ (a + 1) := by
      rw [heq, ← hab, pow_succ]
      ring
    have hcN : 2 ^ (a + 1) < N k := by omega
    have hcS : a + 1 ≤ S + 1 := by
      by_contra hcon
      have h1 : 2 ^ (S + 2) ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨t, htK, htc⟩ := Klass_cover ((a + 1) % 720) (Nat.mod_lt _ (by norm_num))
    obtain ⟨q, m, E, γ⟩ := t
    obtain ⟨hq1, hqmax, hm720, hcyc, hbase, hstep, htar, hqG⟩ := Klass_facts _ htK
    simp only at hq1 hqmax hm720 hcyc hbase hstep htar hqG htc
    have hcm : (a + 1) % m = γ := by
      rw [← Nat.mod_mod_of_dvd (a + 1) hm720]
      exact htc
    have heqG : (p + 2 ^ (a + 1)) * G + w = w * 2 ^ 2 ^ (12 * k) := by
      rw [← heq2]
      exact hNeq
    have hqp : q ∣ p := killer hq1 hcyc hbase hstep htar hqG hk hcm heqG
    rcases (hp.eq_one_or_self_of_dvd q hqp) with h1 | h1
    · omega
    · have hpS : 2 ^ S ≤ p := by
        have h2c : 2 ^ (a + 1) ≤ 2 ^ (S + 1) := Nat.pow_le_pow_right (by norm_num) hcS
        have hsum : (2:ℕ) ^ (S + 1) = 2 * 2 ^ S := by rw [pow_succ]; ring
        omega
      have hqS : (18837001:ℕ) < 2 ^ S := by
        calc (18837001:ℕ) < 2 ^ 25 := by norm_num
        _ ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · -- b < a : distinct powers case
    obtain ⟨d, hd⟩ : ∃ d, a = b + d ∧ 1 ≤ d := ⟨a - b, by omega⟩
    obtain ⟨hd1, hd2⟩ := hd
    obtain ⟨r, u, hu, hdu⟩ := Nat.exists_eq_two_pow_mul_odd (n := d) (by omega)
    have haS : a ≤ S + 1 := by
      by_contra hcon
      have h1 : 2 ^ (S + 2) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hb0 : 0 < 2 ^ b := Nat.pow_pos (by norm_num)
      have h2 : 2 ^ a < N k := by omega
      omega
    have hu1 : 1 ≤ u := by
      rcases hu with ⟨j, hj⟩
      omega
    have h2rd : 2 ^ r ≤ d := by
      calc 2 ^ r = 2 ^ r * 1 := by ring
      _ ≤ 2 ^ r * u := by exact Nat.mul_le_mul_left _ hu1
      _ = d := hdu.symm
    have hdS : d < 2 ^ (12 * k) := by omega
    have hr12k : r + 1 ≤ 12 * k := by
      have h1 : 2 ^ r < 2 ^ (12 * k) := lt_of_le_of_lt h2rd hdS
      have h2 := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp h1
      omega
    -- the Fermat divisor
    set x : ℕ := 2 ^ 2 ^ r with hx
    have hx1 : 1 ≤ x := Nat.one_le_two_pow
    have hxd : x + 1 ∣ 2 ^ d + 1 := by
      rw [hdu, pow_mul]
      exact pow_add_one_dvd x u hu
    have hFQG : x + 1 ∣ G * Q k := by
      have hQG' : G * Q k = 2 ^ 2 ^ (12 * k) - 1 := by
        have h := QG hk
        have h1 : (1:ℕ) ≤ 2 ^ 2 ^ (12 * k) := Nat.one_le_two_pow
        omega
      rw [hQG']
      exact (fermat_dvd_next r).trans (pow2_sub_one_dvd (by omega))
    have hsum_eq : 2 ^ a + 2 ^ b = 2 ^ b * (2 ^ d + 1) := by
      rw [hd1, pow_add]
      ring
    -- B ∣ p in both cases below, with B ≡ 1 mod 16 when r ≥ 2
    by_cases hr10 : r = 10
    · -- use the prime factor D of F₁₀
      have hx10 : x + 1 = G * D := by
        rw [hx, hr10]
        exact GD_eq.symm
      have hDQ : D ∣ Q k := by
        have h7 : G * D ∣ G * Q k := hx10 ▸ hFQG
        exact (Nat.mul_dvd_mul_iff_left G_pos).mp h7
      have hDF : D ∣ x + 1 := ⟨G, by rw [hx10]; ring⟩
      have hDsum : D ∣ 2 ^ a + 2 ^ b := by
        rw [hsum_eq]
        exact Dvd.dvd.mul_left (hDF.trans hxd) _
      have hDN : D ∣ N k := Dvd.dvd.mul_left hDQ w
      have hDp : D ∣ p := by
        have hDN' : D ∣ (2 ^ a + 2 ^ b) + p := by
          have he : (2 ^ a + 2 ^ b) + p = N k := by rw [heq]; ring
          rwa [he]
        exact (Nat.dvd_add_right hDsum).mp hDN'
      rcases hp.eq_one_or_self_of_dvd D hDp with h1 | h1
      · norm_num [D] at h1
      · have hp16 : p % 16 = 1 := by rw [← h1]; exact D_mod16
        have hN16 := N_mod16 hk
        have h14 := sum_pow_mod16_ne14 a b
        omega
    · -- use the Fermat number F_r itself
      have hcop : Nat.Coprime (x + 1) G := by
        rw [hx]
        exact coprime_F hr10
      have hFQ : x + 1 ∣ Q k := hcop.dvd_of_dvd_mul_left hFQG
      have hFsum : x + 1 ∣ 2 ^ a + 2 ^ b := by
        rw [hsum_eq]
        exact Dvd.dvd.mul_left hxd _
      have hFN : x + 1 ∣ N k := Dvd.dvd.mul_left hFQ w
      have hFp : x + 1 ∣ p := by
        have hFN' : x + 1 ∣ (2 ^ a + 2 ^ b) + p := by
          have he : (2 ^ a + 2 ^ b) + p = N k := by rw [heq]; ring
          rwa [he]
        exact (Nat.dvd_add_right hFsum).mp hFN'
      rcases hp.eq_one_or_self_of_dvd _ hFp with h1 | h1
      · omega
      · -- p = 2 ^ 2 ^ r + 1
        rcases Nat.lt_or_ge r 2 with hr2 | hr2
        · interval_cases r
          · -- r = 0 : p = 3
            have hp3 : p = 3 := by
              rw [← h1, hx]
              norm_num
            have hN16 := N_mod16 hk
            have hX : (2 ^ a + 2 ^ b) % 16 = 12 := by omega
            have h12 := sum_pow_mod16_eq12 a b hX
            have h2S : (15:ℕ) < 3 * 2 ^ S := by
              have h8 : (2:ℕ) ^ 3 ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
            omega
          · -- r = 1 : p = 5
            have hp5 : p = 5 := by
              rw [← h1, hx]
              norm_num
            have hN16 := N_mod16 hk
            have hX : (2 ^ a + 2 ^ b) % 16 = 10 := by omega
            have h10 := sum_pow_mod16_eq10 a b hX
            have h2S : (15:ℕ) < 3 * 2 ^ S := by
              have h8 : (2:ℕ) ^ 3 ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) (by omega)
              omega
            omega
        · -- r ≥ 2 : p ≡ 1 (mod 16)
          have hp16 : p % 16 = 1 := by
            rw [← h1, hx]
            have h4 : 4 ≤ 2 ^ r := by
              calc (4:ℕ) = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hr2
            obtain ⟨e, he⟩ : (16:ℕ) ∣ 2 ^ 2 ^ r := by
              calc (16:ℕ) = 2 ^ 4 := by norm_num
              _ ∣ 2 ^ 2 ^ r := pow_dvd_pow 2 h4
            omega
          have hN16 := N_mod16 hk
          have h14 := sum_pow_mod16_ne14 a b
          omega

/- ### Main results -/

theorem N_mem {k : ℕ} (hk : 1 ≤ k) : N k ∈ Erdos9.Erdos9A := by
  simp only [Erdos9.Erdos9A, Set.mem_setOf_eq]
  constructor
  · have := N_mod16 hk
    rw [Nat.odd_iff]
    omega
  · rintro ⟨p, i, j, hp, hpe⟩
    rcases le_total j i with hji | hij
    · exact no_rep hk hp hji hpe
    · exact no_rep hk hp hij (by rw [hpe]; ring)

/-- **Erdős Problem 9, infinitude** (research solved): the set of odd numbers
that cannot be expressed as a prime plus two powers of 2 is infinite. -/
theorem erdos_9.variants.infinite : Erdos9.Erdos9A.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => N (t + 1))
  · -- injectivity via strict monotonicity
    have hsm : StrictMono fun t : ℕ => N (t + 1) := by
      apply strictMono_nat_of_lt_succ
      intro t
      have hQ : Q (t + 1) < Q (t + 2) := by
        have h1 := QG (k := t + 1) (by omega)
        have h2 := QG (k := t + 2) (by omega)
        have h3 : (2:ℕ) ^ 2 ^ (12 * (t + 1)) < 2 ^ 2 ^ (12 * (t + 2)) := by
          have := Nat.pow_lt_pow_right (a := 2) (by norm_num)
            (m := 12 * (t + 1)) (n := 12 * (t + 2)) (by omega)
          exact Nat.pow_lt_pow_right (by norm_num) this
        have h4 : G * Q (t + 1) < G * Q (t + 2) := by omega
        exact lt_of_mul_lt_mul_left h4 (Nat.zero_le G)
      show N (t + 1) < N (t + 1 + 1)
      unfold N
      exact (Nat.mul_lt_mul_left w_pos).mpr hQ
    exact hsm.injective
  · intro t
    exact N_mem (by omega)

end Contribution.Erdos9VariantsInfinite
