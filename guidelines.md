# Contribution guidelines

This repository is a shared workbench for the open conjecture pool. A
contribution is **not** a solution: it is a piece of Lean that makes a target
easier for whoever tries next — a lemma, a definition, an API for a structure the
statement needs, a worked special case, a counterexample search, a tactic.

Submissions that solve a target belong in the validator, not here.

## What earns a reward

Reward decisions are made by the subnet operator, not by CI; a green pipeline
means "admissible", not "recognized" or "paid". The normative six-gate test,
review outcomes, 1–10 weighting rubric, lineage rules, and payout-share interface
are in the [`Contribution recognition contract`](contribution-contract.md). In
practice the contributions that pass that contract are the ones another miner can
pick up and use:

| Rewarded | Not rewarded |
| --- | --- |
| A lemma Mathlib is missing that the statement needs | A restatement of the target under a different name |
| A definition plus its basic API (`simp` lemmas, instances) | A wall of generated lemmas nobody will import |
| A special case proved in full | A special case proved with `sorry` |
| A counterexample search with the bound it establishes | A search script with no theorem attached |
| A tactic or `simp` set that closes a recurring goal shape | A copy of an existing contribution under a new id |

Say what your contribution is *for* in `title` and `sources.md`. That one line is
what everyone else sees in the index.

## Layout

One pull request adds exactly one directory:

```
contributions/<target>/<contribution-id>/
    metadata.json    # written by `contrib promote`; never edit it
    script.lean      # at least one .lean file
    sources.md       # required: where this came from
```

* `<target>` is a problem slug from the pinned pool,
  [`conjectures-io/conjectures-tasks`](https://github.com/conjectures-io/conjectures-tasks/tree/main/pool/tier-1),
  with the `-formalized` / `-counterexample` suffix dropped. Both modes live under
  the same target; `mode` in the payload says which side you are helping.
* `<contribution-id>` is the sha256 of your canonical payload. You do not choose
  it — `contrib promote` computes it and creates the directory.
* The directory is flat: at most 32 artifacts, 1 MiB each, 4 MiB in total, no
  subdirectories, no symlinks, and every file declared in `metadata.json`.
* `index.md` and `index.json` are written by the bot. Never edit them.
* **Contributions are immutable.** To correct one, submit a new contribution that
  lists the old one in `parents` and says so in `sources.md`. A PR that edits an
  existing directory is rejected by `C012`.

## metadata.json

`contrib promote` writes this. It is shown here so you can read one, not write one.

```json
{
  "contribution_id": "d31a8f…0fa2",
  "payload": {
    "artifacts": [{"name": "script.lean", "sha256": "de7ac2…", "size": 326}],
    "author": "8f2c…a91b",
    "kind": "lemma",
    "mode": "either",
    "parents": [],
    "reward": {
      "coldkey": "5D7uCkVbwyf8UxmGyRNFdPW1mukzPyWY1Bp1qeFXSWY35KLX",
      "hotkey": "5DqGyg1p4Q3bWjKk8HXWFUycQ6pfHensHuYotLCFFZ3GXfm4"
    },
    "reward_target_id": "fc-target:Erdos89.erdos_89",
    "schema_version": 1,
    "target": "erdos-89",
    "tasks_commit": "379fc0298dc146df549e7061c3ede0353a5bb51f",
    "title": "Counting helpers for distance sets in the plane"
  },
  "reward_signature": "1b0d…4e77",
  "signature": "0626…7288"
}
```

| Field | Rule |
| --- | --- |
| `target` | a problem slug that is open in the pinned pool |
| `mode` | `formalized`, `counterexample` or `either` |
| `kind` | `idea`, `lemma`, `partial-proof` or `refutation` |
| `title` | one line, at most 120 characters — this is your index entry |
| `author` | your ed25519 authoring key; it signs the payload |
| `reward` | Bittensor `hotkey` and `coldkey`, which must differ — or `null` |
| `reward_signature` | the hotkey's signature over the contribution id — or `null` |
| `parents` | contribution ids this builds on; each must already be published |
| `artifacts` | every file in the directory, with its sha256 and size |
| `tasks_commit` | the Formal Conjectures commit the pinned pool records |

### What is hashed, and what is signed

The payload is serialized as canonical JSON — `indent=2`, sorted keys, one
trailing newline — and its sha256 **is** the contribution id and the directory
name. The payload names every artifact by digest, so changing one byte of any
file changes the id.

Two signatures, because they prove different things. `signature` is your author
key over the canonical payload bytes: this is the record I wrote. `reward_signature`
is your Bittensor hotkey over the contribution id: this content is mine, pay it
here. The reward addresses live inside the payload, so the id already commits to
them and the countersignature cannot be lifted onto anyone else's work.

`reward` and `reward_signature` are both `null` or both set (`C016`). Publishing
with `--no-reward` is permanent — the keys are hashed into the id — and `C018`
warns that the contribution is not eligible for a reward.

`metadata.json` on disk must be byte-identical to that canonical form (`C013`).
That is not tidiness: `json.loads` keeps the last of a duplicated key, so without
byte equality a reviewer could read one target in the diff while the parser takes
another.

Editing anything after `promote` invalidates the id and the signature. Re-promote
instead; the old directory can simply be deleted before it is committed.

## Writing the Lean

Each `.lean` file is elaborated **on its own**: a contribution is not a Lake
package, so one file cannot import another in the same directory.

Imports are limited to `Mathlib`, `Std`, `Init`, `Batteries`, `Aesop`, `Qq`,
`Plausible`, `ProofWidgets`, `ImportGraph`, `FormalConjectures` and
`TaskSupport`. `import Lean` is allowed but sends the PR to a human.

Wrap your declarations in a namespace of your own — `Contribution.<Something>` is
the convention — so two contributions to the same target cannot collide.

### Rejected outright (`C019`, `C020`)

`sorry`, `admit`, `axiom`, `native_decide`, `Lean.ofReduceBool`,
`set_option debug.*`, `maxHeartbeats 0`, `#eval`, `#exit`, `run_cmd`, `run_elab`,
top-level `initialize`, `unsafe`, `@[extern]`, `@[implemented_by]`, `@[init]`,
anything reaching `IO.FS` / `IO.Process` / the environment, the reserved `Bounty`
namespace, and imports outside the allowlist.

Most of these are not style rules. Elaborating Lean runs code, and this pipeline
runs it on someone's hardware.

### Sent to a human instead

Metaprogramming (`macro`, `elab`, `syntax`, `notation`), global `attribute`
changes, `open Lean`, `import Lean`, declarations left in the root namespace, and
elaboration budgets over one million heartbeats. These are allowed — a tactic is a
perfectly good contribution — but they turn off auto-merge.

### And for every artifact

Valid UTF-8, no control or bidirectional characters (`C014`) — a Lean file must
not render as something other than what the kernel sees — LF line endings, no
byte-order mark, a trailing newline (`C022`), and a `sources.md` that actually
attributes something with `https` links (`C023`).

And the two rules that ask whether there is a contribution here at all: at least one
`.lean` artifact (`C007`), because prose and attribution pass every structural rule while
providing nothing; and no surviving scaffolding from `contrib new` (`C024`) — the draft it
writes is deliberately valid so you can see the shape, which means an unedited draft would
otherwise be an admissible submission.

## Submitting

```bash
uv sync --all-groups

# 1. scaffold into drafts/ (gitignored)
uv run contrib new erdos-89 --title "One line on what this gives the next miner." \
  --kind lemma --mode either

# 2. write the Lean and fill in sources.md

# 3. hash, sign, and publish into contributions/
uv run contrib promote erdos-89 --wallet my-wallet --hotkey my-hotkey

# 4. run exactly what CI runs
uv run contrib check

# 5. branch, commit, open the PR
uv run contrib submit contributions/erdos-89/<id> --pr
```

Signing needs two keys. `contrib key generate` writes your author key once.
`--wallet/--hotkey` points at a Bittensor wallet for the reward countersignature
— set it once through `CONJECTURES_WALLET_NAME` or the config file instead of
passing it every time. The hotkey must be unencrypted sr25519; this tool never
prompts for a passphrase, and it never reads your coldkey's private half.

## What CI does

| Stage | Where | Rules |
| --- | --- | --- |
| static rules | GitHub-hosted | `C001`–`C024`, plus yamllint and a secret scan |
| Lean elaboration | self-hosted (`Default`) | `L001`: each file compiles in a read-only container, under a timeout, a memory cap and no network |
| index preview | GitHub-hosted | shows the index rows the merge will produce |
| merge | GitHub-hosted | labels the PR and rebase-merges it onto `main` |

`uv run contrib checks` lists every rule by id. Nothing you submit runs anywhere
until the static rules have passed, and every finding is annotated on the exact
file in the diff.

## After the merge

`main` regenerates `contributions/<target>/index.md` and `index.json`, and the
root `contributions/index.md`. Your row carries your title, kind, mode, the Lean
declarations your file provides, and your reward hotkey. That index is what the next
miner — and the next coding agent — reads first.
