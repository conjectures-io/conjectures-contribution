# Contribution recognition contract

**Version:** 1.0
**Status:** adopted for paid contribution events on or after 2026-08-31

This contract defines when an admissible submission counts as a real contribution and how a
funded payout event turns recognized contributions into shares. It is an operational review and
allocation policy, not an on-chain smart contract. A payment obligation exists only when the
operator publishes a signed payout event naming its asset, integer unit, budget, scope, eligible
review records, allocations, and payment schedule.

The technical format and CI rules remain in [`guidelines.md`](guidelines.md). If the two documents
appear to conflict, the technical rules decide whether the repository can accept the bytes, while
this contract decides whether the accepted work is recognized for credit and reward.

## 1. Three separate decisions

| Decision | Meaning | Authority |
| --- | --- | --- |
| **Admissible** | The record is authentic, safe, correctly formed, and compiles against the pinned pool. | Automated checks `C001`–`C024` and `L001` |
| **Recognized** | The work makes a novel, material, reusable contribution to its declared target. | A signed immutable record under `reviews/` |
| **Payable** | A recognized contribution has a valid reward destination and is included in a funded payout event. | A signed immutable record under `payouts/` and the subnet operator |

A green pipeline establishes only **admissibility**. A merge is a permanent publication record,
not a promise of recognition or payment. A recognized contribution published with `reward: null`
keeps its attribution but is not payable.

## 2. The real-contribution test

A submission is a real contribution only when every gate below is satisfied. Reviewers decide
from the submitted artifacts, the pinned target, prior contributions, cited sources, and a minimal
use case. Reputation, wallet balance, employer, time spent, generated token count, and lines of
code are not evidence of value.

### G1 — Direct relevance

The submission identifies a concrete obstacle in the declared target and provides Lean that
reduces that obstacle. The connection must be specific enough that a reviewer can state:

> A later solver can use declaration **X** to discharge or simplify obligation **Y** in target
> **Z**.

General-purpose mathematics qualifies only when that use is demonstrated for the target. Work
that belongs to a different target must be filed there.

### G2 — Verified mathematical value

Every claimed result elaborates under the pinned toolchain and says what the contribution claims
it says. Definitions have enough supporting API to be usable; tactics have a reproducible goal
they solve; bounded searches expose a checked theorem describing the established bound. Passing
Lean is necessary but not sufficient: a true theorem that is irrelevant or vacuous does not pass
this gate.

### G3 — Material progress

The work removes meaningful effort or uncertainty for the next solver. At least one of these must
be true:

- it proves a nontrivial lemma or a complete useful special case;
- it introduces a needed definition together with the lemmas or instances required to use it;
- it converts an informal step into a checked interface that later work can build on;
- it provides a tactic or simplification setup that reproducibly closes a recurring goal shape;
- it proves a counterexample, impossibility result, or checked search bound that narrows the
  remaining problem.

Formatting changes, renamed copies, thin wrappers, restatements, unused generated lemmas, and
claims without a checked deliverable do not constitute material progress.

### G4 — Novel or incrementally new

The useful content is not already available in the pinned Mathlib/Formal Conjectures environment
or in a published contribution for the target. A follow-up may qualify when it materially
strengthens, generalizes, repairs, or makes a prior contribution usable. It must list every prior
contribution it substantially builds on in `parents` and explain the delta in `sources.md` and the
pull request.

Credit is for the marginal value added, not for re-signing, reformatting, or incorporating the
parent's work. `C015` catches byte-identical copying; reviewers apply this broader semantic test.

### G5 — Reusable handoff

Another miner can understand and use the result without reconstructing the author's private
context. The submission must provide:

- clearly named declarations in a non-conflicting namespace;
- a short explanation of the obstacle addressed and the intended use;
- enough hypotheses, examples, or a minimal use site to verify the claimed handoff;
- no undeclared dependency on sibling files, local patches, private data, or an unpinned service.

A large artifact is not inherently reusable, and a small lemma can be highly reusable.

### G6 — Provenance and good faith

`sources.md` identifies original work, prior contributions, papers, repositories, and generated
material accurately. The author has the right to submit the work and does not conceal copying,
coordinate duplicate claims, split one logical unit to multiply rewards, or misrepresent tool
output as independent mathematical work. Tool-assisted and generated work is allowed; the signer
remains responsible for correctness, provenance, and value.

## 3. Decisions

Every substantive review records one of these outcomes:

| Decision | Effect |
| --- | --- |
| `recognized` | All six gates pass. The contribution receives a recognition weight and may enter a payout snapshot. |
| `admissible-only` | The bytes may remain useful as a public record, but one or more substantive gates fail. Weight is zero. |
| `deferred` | The evidence is insufficient or the value depends on unresolved upstream work. No weight until reviewed again. |
| `rejected` | The submission is technically invalid, deceptive, plagiarized, malicious, or outside repository scope. |
| `withdrawn` | The author asks to end consideration before a payout snapshot. The immutable publication record, if already merged, remains. |

The review must name each failed or uncertain gate. “Not useful” without an evidence-based reason
is not a valid decision.

## 4. Recognition weight

Recognition is binary; weight measures relative value among recognized work. Reviewers assign an
integer from 1 to 10 using the rubric below. The written rationale must cite specific declarations
or evidence for every nonzero component.

| Component | Range | Anchors |
| --- | ---: | --- |
| **Target impact** | 1–4 | `1`: removes a small local step; `2`: supplies a useful lemma/API; `3`: closes a major subproblem or family of obligations; `4`: changes the tractability of the target without itself being the final submitted solution. |
| **Generality and reuse** | 0–2 | `0`: one narrow use; `1`: several steps or nearby cases; `2`: a clean interface useful across major parts of the target or related targets. |
| **Originality of the delta** | 0–2 | `0`: routine but genuinely missing integration; `1`: non-obvious adaptation or strengthening; `2`: new construction, argument, or substantial formalization insight. |
| **Verification and handoff quality** | 0–2 | `0`: minimum qualifying evidence; `1`: clear documentation and representative use; `2`: strong API/tests/examples that materially reduce integration risk. |

The recognition weight is the sum of the four components. Contribution `kind`, artifact count,
proof length, compute used, and elapsed work time do not directly add points.

### Scoring constraints

- Reviewers score only the submitted, checked delta.
- A dependent follow-up does not absorb its parents' points; each record keeps credit for its own
  contribution.
- Multiple submissions by the same author that have no standalone utility are reviewed as one
  logical unit. Their combined weight cannot exceed what the bundled work would have received.
- A stronger later contribution may receive weight for its improvement, but does not erase an
  earlier contribution's already-recorded credit.
- A final solution belongs in the validator. It must not be repackaged here to obtain both the
  solution reward and contribution shares for the same work.

## 5. Overlap, races, and lineage

Novelty is evaluated against the pinned environment and published contributions visible at the
submission's base commit.

- If two submissions are materially equivalent, the first valid publication is the baseline;
  the later submission is `admissible-only` unless it adds a separately useful delta.
- Independently developed concurrent submissions may both be recognized only when each exposes a
  distinct reusable result or implementation advantage. Coincidental duplication alone is not
  paid twice.
- A contribution that uses another contribution must declare it as a parent even when the author
  controls both records.
- Reviewers may request that obviously inseparable work be republished as one atomic contribution
  before recognition.

## 6. Payout-share interface

The payout tool consumes immutable signed review records rather than inferring value from merged
files. For a funded payout event with integer budget `B` and eligible recognized contributions
`E`, the allocation is:

```text
share(i)  = weight(i) / sum(weight(j) for j in E)
payout(i) = B * share(i)
```

The operator must publish the event asset, integer unit, destination policy (`hotkey` or
`coldkey`), review-time window, targets, budget, eligible review ids, weights, and resulting
amounts before transfer. It must not silently change review weights.
If integer rounding leaves a remainder, allocate units by largest fractional remainder, breaking
ties by lexicographically ascending contribution id.

Eligibility for a snapshot requires all of the following:

1. decision `recognized` under a named contract version;
2. a non-null reward block and valid reward signature;
3. no unresolved appeal, fraud finding, or ownership dispute;
4. inclusion in the payout event's announced target and time window;
5. no prior payout for the same contribution under the same event.

An operator may fund different targets or periods differently, but cannot alter relative shares
inside one announced event without publishing a superseding event before payment.

## 7. Review record

The repository implements the review schema in `conjectures_contribution.recognition`. A review is
canonical JSON stored at
`reviews/<target>/<contribution-id>/<review-id>.json`. `review_id` is the SHA-256 of the canonical
payload. Every public key in `reviewers` must provide an Ed25519 signature over the same
domain-separated payload; unsigned PR comments are not recognition decisions.

```yaml
contract_version: 1.0
contribution_id: <64 lowercase hex characters>
target: <target slug>
decision: recognized | admissible-only | deferred | rejected | withdrawn
gates:
  direct_relevance: pass | fail | uncertain
  verified_value: pass | fail | uncertain
  material_progress: pass | fail | uncertain
  novelty: pass | fail | uncertain
  reusable_handoff: pass | fail | uncertain
  provenance: pass | fail | uncertain
score:
  target_impact: 0
  generality_reuse: 0
  originality_delta: 0
  verification_handoff: 0
weight: 0
reviewers: [<64-character Ed25519 public key>]
reason: <specific evidence and comparison with prior work>
reviewed_at: <UTC timestamp>
conflicts: []
supersedes: null
```

For `recognized`, every gate is `pass`, `target_impact` is at least 1, and `weight` equals the
component sum. All other decisions have weight zero. A machine implementation must reject a
record that violates those invariants.

`contrib-admin review` creates, validates, signs, and writes a record. `contrib-admin
audit-rewards` verifies all signatures, contribution bindings, reviewer independence,
supersessions, and payout records. A reviewer public key equal to the contribution author key is
rejected. High-weight and conflicted reviews require two signing keys.

## 7.1 Funding-round record

Before an earning window opens, the operator publishes canonical JSON at
`funding/<round-id>.json`. The operator signature commits to the network, asset, indivisible unit,
positive integer budget, destination policy, inclusive UTC review window, funded targets, and
payment deadline. A modified term is a new round; funding records are immutable.

`contrib-admin fund ROUND.json --operator-key KEY` validates, signs, and writes the commitment.
A paid launch requires at least one real funding record and corresponding funded transfer wallet;
documentation or an unsigned budget statement does not create a funded round.

## 7.2 Payout event record

A payout event is canonical JSON stored at `payouts/<event-id>.json`. It must reference a
previously published funding round and repeat its financial and scope terms exactly. Its signed
event input names:

- contract and event schema versions;
- an event name, network, asset, indivisible unit, and positive integer budget;
- `hotkey` or `coldkey` as the destination policy;
- inclusive UTC review-window bounds and a non-empty target set;
- the exact active review ids admitted to the event;
- the operator public key, snapshot timestamp, and payment deadline.

`contrib-admin payout EVENT.json --funding-file funding/<round-id>.json --operator-key KEY`
rejects missing or altered funding terms and unknown, superseded,
non-recognized, out-of-scope, unsigned-reward, or self-reviewed contributions. It calculates
integer amounts by largest remainder, signs the complete allocation, and refuses to overwrite a
different record. An event file allocates funds; the operator must publish the chain transaction
identifiers after executing those transfers.

## 8. Reviewer independence and conflicts

At least one accountable maintainer whose signing key is not the contribution author key must
sign off on recognition. Reviewers must also disclose when they are the reward recipient or have
another financial or organizational conflict. A second independent maintainer is required when:

- the proposed weight is 8–10;
- authorship, novelty, or licensing is disputed;
- the only available reviewer has a financial or organizational conflict;
- an appeal would change a previous decision or weight.

Conflicts must be disclosed in the review record. A conflicted reviewer may supply technical
analysis but cannot be the only approval.

## 9. Appeals and corrections

An author may appeal with concrete new evidence: a use site, a missing citation, proof of
independent authorship, or a specific rubric error. Appeals should be filed before the next payout
snapshot or within 14 days of the decision, whichever is later. A different reviewer decides the
appeal and publishes a record that names the decision it supersedes.

Fraud, plagiarism, signature compromise, or a material correctness defect may reopen a decision
at any time. Ordinary policy changes apply prospectively: contract version 1.1 cannot silently
rescore a decision made under version 1.0.

## 10. Examples

| Submission | Likely decision | Reason |
| --- | --- | --- |
| A checked lemma used to remove the target's main finiteness obligation, with a short use example | `recognized` | Direct, material, novel, reusable |
| A theorem identical in meaning to an existing Mathlib lemma but under a new name | `admissible-only` | Fails novelty and material-progress gates |
| A definition required by the target with no lemmas showing how to use it | `deferred` | Reusable handoff is not yet demonstrated |
| A complete checked special case that narrows the open parameter range | `recognized` | Complete, useful progress even though it does not solve the target |
| A copied contribution with renamed declarations and a new wallet | `rejected` | Fails novelty, provenance, and good faith |
| A full solution to the reward target | Validator submission | Valuable work, but outside this repository's contribution scope |

The governing question is always concrete: **what checked, attributable work can the next solver
reuse that they did not already have?**
