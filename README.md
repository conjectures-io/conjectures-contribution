# conjectures-contribution

Tools for creating, validating, and submitting contributions to the pinned conjecture pool.

A contribution is Lean that helps someone *else* finish a target — a lemma, a definition, an
API, a special case, a tactic. Solutions do not go here; they go to the validator. The rules
in full are in [`guidelines.md`](guidelines.md). The separate
[`contribution-contract.md`](contribution-contract.md) defines when admissible work is recognized
as a real contribution and how funded paid events convert recognition weights to shares.

> [!IMPORTANT]
> **Choose and read targets in
> [`conjectures-io/conjectures-tasks`](https://github.com/conjectures-io/conjectures-tasks), but
> submit partial contributions as pull requests to this repository,
> [`conjectures-io/conjectures-contribution`](https://github.com/conjectures-io/conjectures-contribution).**
> Do not open a contribution pull request against `conjectures-tasks`; it is the pinned task source,
> not the contribution destination.

## Which repository does what?

| Repository | Contributor use |
| --- | --- |
| [`conjectures-tasks`](https://github.com/conjectures-io/conjectures-tasks/tree/main/pool/tier-1) | Choose an open target and read its exact `Challenge.lean`, metadata, and references. The recursive clone below pins this repository at `conjectures/`; treat those task files as read-only. |
| [`conjectures-contribution`](https://github.com/conjectures-io/conjectures-contribution) | Create, validate, and submit partial Lean work. `contrib submit` opens the pull request here. |
| Validator | Submit a complete proof or refutation. Full solutions do not belong in either repository above as partial contributions. |

## Repository map

```
conjectures/                     # read-only pinned submodule: the immutable task pool
  pool/tier-1/<slug>-<mode>/     #   Challenge.lean, manifest.json, source-metadata.json
  allowlist.json                 #   which task ids are open for submission
contributions/
  index.md                       # bot: every target that has contributions
  <target>/                      #   one directory per problem, both modes together
    index.md                     #   bot: one row per contribution, with declaration names
    index.json                   #   bot: the same, machine-readable
    <contribution-id>/           #   content-addressed, immutable
      metadata.json              #     payload, id, author signature, reward signature
      script.lean                #     the contribution itself; at least one .lean required
      sources.md                 #     attribution, required
drafts/                          # gitignored scratch space; `contrib new` writes here
src/conjectures_contribution/    # the `contrib` CLI: the same code CI runs
```

A **target** is a problem (`erdos-89`), not a task bundle. Both bundles —
`erdos-89-formalized` and `erdos-89-counterexample` — sit under it, and the payload's `mode`
says which side a contribution helps: `formalized`, `counterexample`, or `either`.

## For coding agents

Start here; it will save you a lot of reading.

1. **Find the target.** The full listing is the pinned pool,
   [`conjectures-tasks/pool/`](https://github.com/conjectures-io/conjectures-tasks/tree/main/pool);
   locally the same bytes are under `conjectures/pool/tier-1/`. Statement, docstring and
   references are in `source-metadata.json`; the exact goal is `Challenge.lean`. Every
   `contributions/<target>/index.md` links back to both bundles at the pinned commit.
2. **Read what already exists.** `contrib ls contributions --target <slug>` lists every
   contribution there, and `contrib ls contributions --declares '*Name*'` searches every
   declaration name in the repository. Ask before you write: duplicating an existing
   contribution earns nothing, and `C015` rejects a byte-identical resubmission outright.
   `contributions/<target>/index.md` is the one-file version, with the statements alongside.
3. **Check the pool, not just the directory.** A target directory can exist while the target
   is retired. `conjectures/allowlist.json` is the authority.
4. **Write at least one self-contained `.lean` file** — `C007` requires it. Each is
   elaborated alone against Mathlib and Formal Conjectures; it cannot import its siblings.
5. **Namespace everything** under `Contribution.<Something>`.
6. **No `sorry`.** A contribution with a hole fails `C019`, and so do `#eval`, `axiom`,
   `native_decide`, `unsafe`, `IO`, and anything else that runs code or forges a proof.
7. **Verify before you push:** `contrib check` runs every rule CI runs, except the Lean build.
   `contrib checks` lists the rules by id.

## Install

From a clone of this repository, run:

```sh
./install.sh
```

The installer puts `contrib` on your user PATH, installs shell completion, and pins this
checkout so commands work from any directory. If it reports that the binary directory is not
on PATH, add the directory it prints and restart your shell.

Completion suggests target slugs, drafts, Bittensor wallets, hotkeys, and enum-valued options.
To install it again for the current shell, run:

```sh
contrib --install-completion
```

## Configure the reward wallet

This tool owns `~/.config/conjectures/contribution.toml`; it does not read the miner's
`config.toml`. Configure the Bittensor wallet once:

```sh
contrib config set wallet_name my-wallet
contrib config set wallet_hotkey my-hotkey
contrib config show
contrib wallet show
```

`wallet_path` defaults to `~/.bittensor/wallets` and can be overridden with:

```sh
contrib config set wallet_path /path/to/wallets
```

The equivalent `CONJECTURES_WALLET_NAME`, `CONJECTURES_WALLET_HOTKEY`, and
`CONJECTURES_WALLET_PATH` environment variables take precedence over the file.

## Contribute

Choose a target in `conjectures-tasks`, then create the draft from your
`conjectures-contribution` checkout. For a task directory such as
`erdos-100-formalized` or `erdos-100-counterexample`, pass the shared target slug
`erdos-100`:

```sh
contrib new erdos-100
```

Edit the files in `drafts/erdos-100/`. `draft.json` contains the selected metadata; every
other file becomes an artifact. `sources.md` and at least one `.lean` file are required, and
both are scaffolded for you — `C024` rejects a draft promoted with that scaffolding still in
it, so replace the placeholder text.

Promote the finished draft into a hashed and signed contribution:

```sh
contrib promote erdos-100
```

If you deliberately do not want a reward destination, use `--no-reward`. That choice is
permanent because the destination is part of the contribution ID.

Validate the contribution or the current changeset:

```sh
contrib check
contrib check --base main
```

Finally, update `main`, create a contribution branch, commit, push, and open a pull request against
**`conjectures-io/conjectures-contribution`**:

```sh
contrib submit contributions/erdos-100/<contribution-id>
```

The repository must be on `main` with no staged or tracked changes and no unrelated
untracked files. Submission fast-forwards from the canonical
`conjectures-io/conjectures-contribution` main branch, updates its submodules, and validates
against that exact revision. By default, [GitHub CLI](https://github.com/cli/cli) creates or
reuses your personal fork, records the canonical repository as `contribution-upstream`,
pushes to the fork remote, and opens a pull request using the repository template.
It never opens a contribution pull request against `conjectures-tasks`.

`gh` must be installed and authenticated:

```sh
gh auth login
```

Installation instructions for every platform are at
[github.com/cli/cli](https://github.com/cli/cli#installation).

Use `--no-pr` to push to your existing `origin` without opening a pull request. Use both
`--no-push --no-pr` to keep the branch and commit local.

## Explore the corpus

`contrib ls` joins `contributions/*/index.json` with the pinned pool and prints rows. One
command, three nouns, generic flags — everything local, no network and no Lean build:

```sh
contrib ls                                        # targets, the default
contrib ls targets --is empty                     # nothing contributed here yet
contrib ls targets --sort contributions --desc    # the crowded ones
contrib ls contributions --since 30d              # what arrived recently
contrib ls contributions --declares '*Sidon*'     # is this declaration already taken
contrib ls contributions --mine                   # what I have contributed
contrib ls authors --is shared_coldkey            # distinct authors paying into one coldkey
```

`--mine` matches on authorship, and reads the public half of your key from the config —
`contrib key show` caches it, and nothing here opens the private key. Filters bind to
columns, so a filter applies to exactly the grains that have the column and says which
those are when it does not.

Zero rows is exit 0. Exit 3 means the answer is incomplete because some source did not
parse; the rows printed are still true, and `contrib doctor` says what is wrong and which
command fixes it. A `?` is an unreadable field and a `—` is an absent one; in `--json` both
are `null`, never `0` or `false`.

Anything the flags do not cover is one pipe:

```sh
# contributions per kind
contrib ls contributions --all --json | jq -r 'group_by(.kind)[] | "\(.[0].kind)\t\(length)"'

# contributions per month
contrib ls contributions --all --json | jq -r 'group_by(.added[:7])[] | "\(.[0].added[:7])\t\(length)"'

# every declaration name in the repository, sorted
contrib ls contributions --all --json | jq -r '.[].declarations[]' | sort -u
```

`--json` emits the joined rows with full ids and stable field names, ties broken by id, so
repeated runs diff cleanly. Fields are added over time, never renamed or retyped.

## Repository location

The installer pins the checkout in the contribution config, allowing `contrib` to run from
anywhere. Inspect the resolution with:

```sh
contrib repo show
```

If the checkout moves, enter the moved repository and update the pin:

```sh
contrib repo pin
```

An explicit `--repo PATH` or `CONJECTURES_CONTRIBUTION_ROOT` overrides discovery. When run
inside a checkout, walking up from the current directory takes precedence over the saved pin.

## The pipeline

| Workflow | Trigger | What it does |
| --- | --- | --- |
| `contribution-pr` | PR adding a contribution directory | unprivileged static feedback and index preview on GitHub-hosted runners |
| `contribution-verify` | `contribution-pr` completed | resolves the PR from its head SHA, repeats every trusted rule, then runs sandboxed Lean on `Default` |
| `contribution-merge` | `contribution-verify` finished green | confirms the verified head and base, labels the PR, rebase-merges |
| `contribution-index` | push to `main` | regenerates the indexes and commits them |
| `ci-selfcheck` | changes to the tooling | ruff, mypy, pyright, pytest, index drift, actionlint, zizmor, shellcheck |

The pull request can rewrite its own `contribution-pr` workflow, so that workflow is only fast
feedback. `contribution-verify` is loaded from the default branch through `workflow_run`. It
uses GitHub's API to bind the triggering head SHA to exactly one open PR, checks out the
validator and pool from the tip of the default branch — never from the pull request's base
commit — and independently repeats every rule. Its
sandbox job has no repository token permissions.

Elaborating Lean is arbitrary code execution. Each source therefore runs in a read-only
container with no network, dropped capabilities, process and memory limits, and no mount of
the runner's home. Only the trusted verifier publishes merge metadata, and the job holding the
write token never checks the contribution out.

Indexes are rebuilt on `main` after the merge, never inside a PR: if every contribution edited
an index, every contribution PR would conflict with every other one.

### Maintainer pull requests

`contribution-pr` triggers on `contributions/*/*/**` — four segments deep, so it fires only on
files inside a contribution directory. A PR that changes tooling, workflows, or the generated
`contributions/index.md` and `contributions/<target>/index.md` never reaches it; those get
`ci-selfcheck` instead.

For the case the path filter cannot see — a PR that legitimately adds a contribution directory
*and* something else — label it **`meta`** and the pipeline skips. Only users with write access
can label a pull request, so an outside contributor cannot apply it to their own submission.

### Repository settings this expects

* **Allow rebase merging** must be on; enable **automatically delete head branches**.
* An environment named `contribution-runner` gates the self-hosted job. Configure at least one
  required reviewer. That maintainer should approve the pull request before authorizing the
  environment job, so the one-review branch rule is already satisfied when the checked commit
  reaches the merge workflow.
* Give this repository access to the `Default` runner group. Its Linux runner needs `git`, `jq`,
  `curl`, `elan`, and Docker. The workflow pulls a digest-pinned Debian image before elaboration.
* Protect `main` from direct pushes and require pull requests. Keep the existing one-review rule
  for maintainer changes; the contribution merge workflow additionally refuses to merge if
  either the checked head or checked base commit has moved.

### The merge identity

`contribution-merge` acts as a GitHub App, not as `github-actions[bot]`. A push made with
`GITHUB_TOKEN` never triggers another workflow, so merging with it left `contribution-index`
unrun and every generated index quietly stale — the same rule the index workflow relies on to
avoid looping is the rule that stopped it from being reached at all.

The app is installed on this repository only and holds **Contents: read and write**,
**Pull requests: read and write** and **Issues: read and write**. It is deliberately not
granted **Actions**, so the one step that reads the verifier's artifact keeps `GITHUB_TOKEN`.
Its credentials live in the repository variable `CONTRIB_APP_ID` and the secret
`CONTRIB_APP_PRIVATE_KEY`. If required approvals or required status checks are ever turned on,
add the app to the ruleset's bypass list, or merging stops.

### Repository variables

| Variable | Default | Meaning |
| --- | --- | --- |
| `CONTRIB_LEAN_WORKSPACE` | unset | Path on the `DEV`-group runner to a clean prebuilt Lake project at the exact commit pinned by the pool. |
| `CONTRIB_LEAN_BOOTSTRAP` | `false` | If no workspace is configured, let CI clone and build Formal Conjectures at the commit the pool pins. Slow once, then cached per commit. |
| `CONTRIB_LEAN_CACHE` | `$RUNNER_TOOL_CACHE/formal-conjectures` | Where bootstrapped workspaces are cached. |
| `CONTRIB_LEAN_TIMEOUT` | `900` | Wall-clock seconds per Lean file. |
| `CONTRIB_LEAN_PIDS_LIMIT` | `1024` | Process ceiling inside the sandbox. Lean takes a thread per elaboration task, so this scales with the size of a contribution, not with the core count. |
| `CONTRIB_LEAN_MEMORY_MB` | `16384` | Memory cap per Lean file. |
| `CONTRIB_AUTOMERGE` | on | Set to `false` to label and leave the PR for a human. |
| `CONTRIB_TAG_CONTRIBUTIONS` | `false` | Also push a `contrib/<target>/<id>` tag per contribution. Off on purpose: labels and `index.json` already carry the provenance without adding a ref per contribution. |

One of `CONTRIB_LEAN_WORKSPACE` or `CONTRIB_LEAN_BOOTSTRAP=true` must be set, or the Lean
stage fails with instructions rather than silently skipping.

Either way the runner account needs `elan` on its own `PATH` — `lean_sandbox.sh` asks `lake`
which toolchain the workspace pins before it can mount that toolchain into the container, so
`elan` is required even when the workspace is prebuilt and no bootstrap happens.

## Maintenance

```sh
# after bumping the pinned pool
git submodule update --remote conjectures
uv run contrib-admin sync

uv run contrib-admin index            # rebuild indexes (CI does this on main)
uv run contrib-admin index --check    # fail if anything is stale
```

## Paid contribution operation

Technical acceptance, recognition, and payment remain separate. A green contribution pipeline
proves admissibility; it does not assign a weight or spend funds.

An independent maintainer creates a signed recognition record with `contrib-admin review`. The
command requires explicit six-gate results, a reason, a canonical UTC review time, and one or two
reviewer key files. Recognized work receives the 1–10 component score defined by the contract.
High-weight or conflicted decisions require two signatures, and an author key cannot review its
own contribution.

Recognition records conditional credit; they do not trigger payment. A contribution payout is
blocked until the target has been formally settled by an accepted validator proof or refutation.
The payout event must bind that accepted result's id and published proof hash for every target it
covers. Payouts always use the coldkey that the contributor signed into the immutable contribution
metadata. No separate address collection or pre-launch funding record is required.

After the review window closes **and the target has been formally solved**, create a payout event
with the actual budget, scope, and accepted-result evidence:

```json
{
  "asset": "TAO",
  "budget": 1000000000,
  "contract_version": "1.0",
  "created_at": "2026-09-08T00:00:00Z",
  "destination": "coldkey",
  "event_version": 1,
  "formal_solves": [
    {
      "accepted_at": "2026-09-07T20:00:00Z",
      "mode": "formalized",
      "proof_sha256": "<64-character published proof digest>",
      "result_id": "<canonical validator result UUID>",
      "target": "<funded target slug>"
    }
  ],
  "name": "launch-week-one",
  "network": "finney",
  "operator": "<64-character Ed25519 public key>",
  "payment_due_at": "2026-09-09T00:00:00Z",
  "period_end": "2026-09-07T23:59:59Z",
  "period_start": "2026-09-01T00:00:00Z",
  "review_ids": ["<eligible signed review id>"],
  "targets": ["<funded target slug>"],
  "unit": "rao"
}
```

The numbers and dates above demonstrate the schema only. Sign and publish the exact allocation
with:

```sh
uv run contrib-admin payout /path/to/event.json \
  --operator-key /secure/operator.key
uv run contrib-admin audit-rewards
```

`payouts/<event-id>.json` binds the accepted formal solve, exact eligible reviews, coldkey
destinations, financial terms, and integer allocations. Publish the payout snapshot before
executing transfers, then publish the resulting chain transaction ids.

## Development

Create the development environment and run all checks:

```sh
uv sync
uv run pytest -q
uv run ruff check .
uv run ruff format --check .
uv run mypy
uv run pyright
```

During development, commands can be run directly as `uv run contrib ...`.

To remove a global installation, run `uv tool uninstall conjectures-contribution`. Use
`contrib repo unpin` first if you also want to remove the saved checkout location.
