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

## Documentation

| | |
| --- | --- |
| [`docs/querying.md`](docs/querying.md) | `contrib ls` and `contrib doctor`: grains, columns, filters, exit codes |
| [`docs/identity.md`](docs/identity.md) | the author key against the reward wallet, and why they are separate |
| [`docs/pipeline.md`](docs/pipeline.md) | how a pull request becomes a merged contribution, and the settings it needs |
| [`docs/payouts.md`](docs/payouts.md) | recognition records, payout events, and how shares are computed |
| [`guidelines.md`](guidelines.md) | what makes a contribution admissible |
| [`contribution-contract.md`](contribution-contract.md) | recognition weights and paid events |

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
   declaration name in the repository — see [`docs/querying.md`](docs/querying.md), which has a
   section on reading that output without misreporting it. Ask before you write: duplicating an
   existing contribution earns nothing, and `C015` rejects a byte-identical resubmission
   outright. `contributions/<target>/index.md` is the one-file version, with the statements
   alongside.
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

The wallet is where rewards are *sent*. It is not your contribution identity — that is a separate
ed25519 key made by `contrib key generate`. The difference matters when reading contribution
records; [`docs/identity.md`](docs/identity.md) explains it.

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

`contrib ls` joins `contributions/*/index.json` with the pinned pool and prints rows — which
targets are empty or crowded, what already exists on one, who contributed what, whether a
declaration name is taken. Everything local, no network and no Lean build:

```sh
contrib ls                                        # targets, the default
contrib ls targets --is empty                     # nothing contributed here yet
contrib ls contributions --since 30d              # what arrived recently
contrib ls contributions --declares '*Sidon*'     # is this declaration already taken
contrib ls contributions --mine                   # what I have contributed
contrib doctor                                    # what is wrong with the corpus
```

Full reference — every grain, column, filter and exit code, plus the `jq` recipes for anything
past them — in [`docs/querying.md`](docs/querying.md).

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

## The pipeline and maintenance

How a contribution pull request is verified and merged, what the repository must be configured to
allow, and the maintainer commands for reindexing and syncing the pool are in
[`docs/pipeline.md`](docs/pipeline.md). Recognition and payment are in
[`docs/payouts.md`](docs/payouts.md).

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
