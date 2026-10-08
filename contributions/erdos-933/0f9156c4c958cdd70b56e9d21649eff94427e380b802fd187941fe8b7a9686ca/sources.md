# Sources

- Problem statement and background (Mahler's bound; Erdős's remark; Steinerberger's family
  n = 2^{3^r}): https://www.erdosproblems.com/933
- Forum discussion. Woett's record n = 1487503359 (R ≈ 4.99) is reproduced in `records.md`. The
  heuristic arguments of P. Chojecki and N. Sothanaphan motivate the 3-adic form in
  `reduction.md`. https://www.erdosproblems.com/forum/thread/933
- Formal statement `Erdos933.erdos_933`, with `Erdos933.k` and `Erdos933.l`, in Formal
  Conjectures:
  https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/933.lean
- Mathlib declarations used in `script.lean`: `EReal.eq_top_iff_forall_lt`,
  `Filter.le_limsup_of_frequently_le`, `Filter.frequently_atTop`, `padicValNat_dvd_iff_le`,
  `Real.log_pos`, `le_div_iff₀`: https://github.com/leanprover-community/mathlib4

The reduction (`reduction.md`), the Lean file and the record search (`records.py`,
`records.md`) are new; the conjectures.io page listed nothing published on this target as of
2026-10-08. They were produced with
an AI coding agent (Claude Code) under the contributor's direction. The Lean file was elaborated
standalone with the checker's toolchain (Lean v4.35.0-rc2, pinned Mathlib and Formal Conjectures);
its theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. Every record was
re-verified by direct valuation computation.
