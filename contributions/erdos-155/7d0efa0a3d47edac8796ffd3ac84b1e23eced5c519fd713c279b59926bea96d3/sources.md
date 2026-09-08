# sources.md — Contribution to Erdős Problem 155 (`Erdos155.erdos_155`)

## Target

`Erdos155.erdos_155 : answer(sorry) ↔ ∀ k ≥ 1, ∀ᶠ N in atTop, F (N + k) ≤ F N + 1`,
where `F N = Finset.maxSidonSubsetCard (Finset.Icc 1 N)` is the size of a largest Sidon subset of
`{1, …, N}`. File: `FormalConjectures/ErdosProblems/155.lean` (tagged `research open`, AMS 5).

Problem page: <https://www.erdosproblems.com/155>

Note on provenance of the statement: <https://www.erdosproblems.com/155> returned HTTP 403 to the
fetch made while preparing this contribution, so the statement worked with is exactly the one
formalized in the pool file, and no claim is made here about the problem's status in the
literature beyond the `research open` tag carried by the pool file itself.

## The obstacle

`Finset.maxSidonSubsetCard A` is defined in
`FormalConjecturesForMathlib/Combinatorics/Basic.lean` as
`(A.powerset.filter fun B ↦ IsSidon (B : Set α)).sup Finset.card`, and in the pinned environment
that definition has **no** API:

* outside its own definition, `Finset.maxSidonSubsetCard` occurs only in
  `ErdosProblems/30.lean`, `43.lean`, `44.lean`, `155.lean` and `GreensOpenProblems/31.lean`,
  each time merely as the abbreviation naming the counting function;
* `grep -r "Sidon" .lake/packages/mathlib/Mathlib` returns nothing — Mathlib has no Sidon-set
  material whatsoever;
* the one lemma-shaped statement about the quantity, `Erdos44.maxSidonSubsetCard_icc_bound`
  (`maxSidonSubsetCard (Icc 1 N) ≤ 2 * Real.sqrt N`), is itself left unproved in the repository.

So a solver cannot get from a Sidon subset to a lower bound on `F`, nor from a bound on `F` back
to an actual Sidon subset, without redoing the `Finset.sup`-over-`powerset` bookkeeping by hand.

Second, the target is a filter statement about the **values** `F (N + k)` and `F N`, whereas every
combinatorial handle on the problem is about the **increments** of `F`. The conjecture is really
the statement that the positions at which `F` increases are eventually more than `k` apart, and
nothing in the environment converts between the two readings — indeed nothing even records that
`F` moves in unit steps.

## What this contribution adds (the delta)

One self-contained file, `CW_erdos_155.lean`, 19 theorems in namespace
`Contribution.Erdos155SidonJumps`, all proved, no placeholders.

1. **Extraction / monotonicity API for `Finset.maxSidonSubsetCard`** (stated for the general
   `Finset ℕ`, so it also serves `Erdos30.h`, `Erdos43.f`, `Erdos44` and `Green 31`):
   `card_le_maxSidonSubsetCard`, `exists_sidon_subset_card_eq` (the supremum is attained, giving
   the converse direction), `maxSidonSubsetCard_mono`, `maxSidonSubsetCard_insert_le`.
2. **Step structure of `F`**: `F_mono`, `F_succ_le` (`F (N+1) ≤ F N + 1`, for every `N`),
   `lt_F_succ_iff_F_succ_eq` (the jump predicate `F N < F (N+1)` is exactly
   `F (N+1) = F N + 1`), and `lt_F_succ_iff_exists_sidon`, which characterises a jump
   combinatorially: `F` increases at `N` iff some Sidon subset of `{1, …, N+1}` of size `F N + 1`
   actually uses the endpoint `N + 1`.
3. **The counting identity** `F_add_eq_add_card_jumps` :
   `F (N + k) = F N + #{i ∈ Finset.Ico N (N + k) | F i < F (i + 1)}` — the bridge between the
   value reading and the increment reading — together with the trivial consequence
   `F_add_le_add` (`F (N + k) ≤ F N + k`), which exhibits the target as the request to improve
   that `k` to a `1`.
4. **The reformulation**: `F_add_le_add_one_iff` (one instance of the target's inequality holds
   iff the window `[N, N+k)` contains no two distinct jumps) and the headline
   `erdos_155_iff_jump_gap`, an **equivalence** (both directions proved) between the target's
   obligation and "for every `k`, eventually any two jumps `i < j` satisfy `i + k ≤ j`", i.e. the
   gaps between consecutive jumps of `F` tend to infinity. Because it is an `Iff`, the hypothesis
   cannot be refuted at some legal instance of the target's binders while the target survives.
5. **Non-vacuity and the case `k = 1`**: `exists_sidon_finset_card_eq` builds Sidon subsets of
   initial intervals of every size by iterating the repository's own
   `Finset.IsSidon.insert_ge_max'`, whence `exists_le_F`, `tendsto_F_atTop`, `exists_jump_ge` and
   `infinite_setOf_jump` — `F → ∞` and the jump set is infinite, so the reformulation quantifies
   over infinitely many pairs rather than being vacuously true. `erdos_155_iff_two_le` settles
   `k = 1` of the obligation outright and reduces the target to `k ≥ 2`.
6. **Worked use site**: `erdos_155_of_jump_gap` produces the target's obligation verbatim
   (`∀ k ≥ 1, ∀ᶠ N in atTop, Erdos155.F (N + k) ≤ Erdos155.F N + 1`) from the jump-gap hypothesis.

**Not claimed**: nothing here decides Erdős 155. `erdos_155_iff_jump_gap` is a translation; the
arithmetic input it now needs — that two jumps of `F` cannot stay a bounded distance apart forever
— is untouched. The smallest case not settled here is `k = 2`.

## Novelty checks performed

* `grep -rn "Sidon\|maxSidonSubsetCard" .lake/packages/mathlib/Mathlib` — no hits at all.
* `grep -rn "maxSidonSubsetCard"` over `FormalConjectures*` — only the definition and the five
  abbreviation sites listed above, plus the unproved `Erdos44.maxSidonSubsetCard_icc_bound`.
* `exact?` was run against the pinned environment (Mathlib + FormalConjectures, without this
  file's own lemmas) on the statements of `card_le_maxSidonSubsetCard`, `maxSidonSubsetCard_mono`,
  `F_mono`, `F_succ_le`, `F_add_le_add`, `exists_le_F` and `tendsto_F_atTop`: each either reported
  "could not close the goal" or exhausted the default heartbeat budget without a proof.
* `simp [Erdos155.F, Finset.maxSidonSubsetCard]` leaves `card_le_maxSidonSubsetCard`, `F_succ_le`
  and `F_add_eq_add_card_jumps` open (unsolved goals reproduced during development).

## Verification

* Toolchain: `leanprover/lean4:v4.27.0` (repository `lean-toolchain`), Mathlib as pinned in
  `lake-manifest.json`.
* Command: `lake env lean CW_erdos_155.lean` — exit code 0, **zero errors and zero warnings**
  (the repository's own style linters, including the module-docstring, namespace and LaTeX-docstring
  linters, are active and silent).
* Axioms: `#print axioms` was run on all 19 theorems; every one reports exactly
  `[propext, Classical.choice, Quot.sound]`. The `#print axioms` lines were then removed and the
  file recompiled clean.
* The file contains no `sorry`/`admit`, no `axiom`, no `native_decide`, no `#eval`, no `unsafe`,
  no `extern`/`implemented_by`, no `partial`, and no `set_option` of any kind; plain LF, no BOM,
  no unicode control or bidi characters.

## References

* Erdős Problem 155: <https://www.erdosproblems.com/155>
* Formal Conjectures repository (source of the target file and of `Finset.maxSidonSubsetCard`,
  `IsSidon`, `Finset.IsSidon.insert_ge_max'`):
  <https://github.com/google-deepmind/formal-conjectures>
* Mathlib 4: <https://github.com/leanprover-community/mathlib4>
* P. Erdős and P. Turán, *On a problem of Sidon in additive number theory, and on some related
  problems*, J. London Math. Soc. 16 (1941), 212–215:
  <https://doi.org/10.1112/jlms/s1-16.4.212> — background on `F(N) = √N + O(N^{1/4})`; used only
  as context for the write-up, no result of it is asserted or used in the Lean file.
* K. O'Bryant, *A complete annotated bibliography of work related to Sidon sequences*, Electron.
  J. Combin., Dynamic Survey 11: <https://doi.org/10.37236/32> — general background on Sidon sets;
  again not used in any proof.

## AI assistance and originality

This contribution was produced by Claude (Anthropic), an AI assistant, working non-interactively
under the direction of the human account holder, who reviewed and submitted it. The AI read the
target file and the bespoke definitions it depends on, designed the statements, wrote every proof,
and iterated against the Lean compiler until the file elaborated with zero errors and zero
warnings.

All statements and proofs in `CW_erdos_155.lean` were written from scratch against the pinned
environment. No proof, proof script, or statement was copied from another repository, from a
`formal_proof` link, from a solution set, or from any other Lean development; the only external
Lean declarations used are those of Mathlib and of FormalConjectures/FormalConjecturesForMathlib
already present in the pinned environment (notably `Finset.exists_mem_eq_sup`,
`Finset.pred_card_le_card_erase`, `Set.IsSidon.subset`, `Finset.IsSidon.insert_ge_max'`,
`tendsto_atTop_atTop_of_monotone` and `Set.infinite_of_forall_exists_gt`). The underlying
mathematics (that a maximal Sidon subset count is monotone with unit steps, that the increase
across a window counts the jumps in it, and that the conjecture is the assertion that gaps between
consecutive jumps tend to infinity) is elementary and would be regarded as folklore by a
specialist; the contribution is the checked formalization, for which no prior version exists in
Mathlib or in the Formal Conjectures repository.
