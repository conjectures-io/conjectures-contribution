# Sources

**What this is for.** Erdős 263(i) asks whether `2 ^ 2 ^ n` is an irrationality sequence. Suppose a
counterexample `b` has `∑ 1/b n = p/q`. This contribution introduces the integer scaled tails
`tailInt b p q n = q · (b 0 ⋯ b (n-1)) · ∑_{k ≥ n} 1/b k` and proves they are **unbounded** in any
counterexample. The remaining open case is therefore exactly: positive integer tails with
`I (n+1)/I n → 1` and `I n → ∞` along a subsequence (the "shrinking residue" dynamics).

**Declarations (namespace `Contribution.Erdos263Partial`).**
- `sylvester_not_asymp` — a sequence eventually following Sylvester's recursion
  `b (n+1) = b n ^ 2 - b n + 1` never satisfies `2 ^ 2 ^ n / b n → 1`. Elementary proof via
  `r n = (b n - 1/2)/2^(2^n)`: `r > 1` would force doubling of `r - 1`; `r < 1` plus integrality gives
  `1 - r n ≥ 1/(2·2^(2^n))`, after which `1 - r` grows geometrically — both contradict `r → 1`.
- `eventually_sylvester_of_bounded` — abstract step: positive integers `I` with
  `I (n+1) = b n · I n - Q n`, `Q (n+1) = Q n · b n`, `b → ∞`, `b (n+1)/b n ^ 2 → 1`; if `I` is bounded
  then `b` is eventually Sylvester. Key identity eliminating `Q`:
  `b (n+1) I (n+1) = I (n+2) + b n ^ 2 I n - b n I (n+1)`, which gives `I n / I (n+1) → 1`, hence
  eventually constant `I`, hence Sylvester's recursion.
- `tailInt`, `tailInt_eq` — the integer tail and its identification with the real scaled tail.
- `tailInt_unbounded` — main result, stated for the exact hypotheses of the target
  (`b` positive, `2 ^ 2 ^ n / b n → 1`, `∑' 1/b n = p/q`).

**Intended use.** A solver of the formalized mode only needs to rule out the unbounded-tail case;
they can import the recursion, integrality, positivity and the bounded-case contradiction from here.

**Provenance.** Original to this contribution (the bounded-case reduction and the elementary
Sylvester-growth argument). Background: Kovač–Tao (arXiv:2406.17593) settle the
sub-doubly-exponential regime; the erdosproblems.com forum thread for #263 records part (i) as
open. Written with AI assistance (Claude). Compiles against the pinned pool (Lean 4.33.1,
Formal Conjectures `6a786f99`) using only `propext`, `Classical.choice`, `Quot.sound`.
