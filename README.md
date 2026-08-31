# conjectures-contribution

Tools for creating, validating, and submitting contributions to the pinned conjecture pool.

A contribution is Lean that helps someone *else* finish a target — a lemma, a definition, an
API, a special case, a tactic. Solutions do not go here; they go to the validator. The rules
in full are in [`guidelines.md`](guidelines.md). The separate
[`contribution-contract.md`](contribution-contract.md) defines when admissible work is recognized
as a real contribution and how a future payout system can convert recognition weights to shares.

## Repository map

```
conjectures/                     # pinned submodule: the immutable task pool
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
2. **Read what already exists.** `contributions/<target>/index.json` lists every contribution
   with its title and the fully-qualified Lean declarations it provides. Grep that first:
   duplicating an existing contribution earns nothing, and `C015` rejects a byte-identical
   resubmission outright.
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

Create a draft for an open target:

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

Finally, update `main`, create a contribution branch, commit, push, and open a pull request:

```sh
contrib submit contributions/erdos-100/<contribution-id>
```

The repository must be on `main` with no staged or tracked changes and no unrelated
untracked files. Submission fast-forwards from the canonical
`conjectures-io/conjectures-contribution` main branch, updates its submodules, and validates
against that exact revision. By default, [GitHub CLI](https://github.com/cli/cli) creates or
reuses your personal fork, records the canonical repository as `contribution-upstream`,
pushes to the fork remote, and opens a pull request using the repository template.

`gh` must be installed and authenticated:

```sh
gh auth login
```

Installation instructions for every platform are at
[github.com/cli/cli](https://github.com/cli/cli#installation).

Use `--no-pr` to push to your existing `origin` without opening a pull request. Use both
`--no-push --no-pr` to keep the branch and commit local.

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
* The self-hosted job runs in an environment named `contribution-runner`, created on first use.
  Whether you add a required reviewer to it is the automation decision: with one, a maintainer
  authorizes every submission before its Lean elaborates and nothing merges unattended; with
  none, the pipeline is fully automatic and the container sandbox is the only thing between a
  contributor's Lean and the runner host.
* **Fork pull request workflows from outside collaborators** does the same job with an extra
  click. Left at *require approval for all external contributors*, every submission stalls at
  `action_required` and no check ever reports. Loosen it only together with the decision above,
  so you keep exactly one gate rather than two or none.
* Give this repository access to the `Default` runner group. Its Linux runner needs `git`, `jq`,
  `curl`, `elan`, and Docker. The workflow pulls a digest-pinned Debian image before elaboration.
* Protect `main` from direct pushes and require pull requests, restricted to the rebase merge
  method. Keep **required approvals at zero**: the merge workflow acts as `github-actions[bot]`,
  which cannot approve a pull request, so any non-zero count stops every automatic merge. The
  workflow supplies the safety instead — it merges only the exact head it verified, and refuses
  if either that head or the base has moved since.
* Turn off **require additional approval for unattributed changes** unless contributors are told
  to commit with a GitHub-verified email. An unattributed commit demands an approval that no
  automation can give.

### Repository variables

| Variable | Default | Meaning |
| --- | --- | --- |
| `CONTRIB_LEAN_WORKSPACE` | unset | Path on the Default-group runner to a clean prebuilt Lake project at the exact commit pinned by the pool. |
| `CONTRIB_LEAN_BOOTSTRAP` | `false` | If no workspace is configured, let CI clone and build Formal Conjectures at the commit the pool pins. Slow once, then cached per commit. |
| `CONTRIB_LEAN_CACHE` | `$RUNNER_TOOL_CACHE/formal-conjectures` | Where bootstrapped workspaces are cached. |
| `CONTRIB_LEAN_TIMEOUT` | `900` | Wall-clock seconds per Lean file. |
| `CONTRIB_LEAN_MEMORY_MB` | `8192` | Memory cap per Lean file. |
| `CONTRIB_AUTOMERGE` | on | Set to `false` to label and leave the PR for a human. |
| `CONTRIB_TAG_CONTRIBUTIONS` | `false` | Also push a `contrib/<target>/<id>` tag per contribution. Off on purpose: labels and `index.json` already carry the provenance without adding a ref per contribution. |

One of `CONTRIB_LEAN_WORKSPACE` or `CONTRIB_LEAN_BOOTSTRAP=true` must be set, or the Lean
stage fails with instructions rather than silently skipping.

## Maintenance

```sh
# after bumping the pinned pool
git submodule update --remote conjectures
uv run contrib-admin sync

uv run contrib-admin index            # rebuild indexes (CI does this on main)
uv run contrib-admin index --check    # fail if anything is stale
```

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
