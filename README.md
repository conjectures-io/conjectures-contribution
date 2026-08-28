# conjectures-contribution

Tools for creating, validating, and submitting contributions to the pinned conjecture pool.

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
other file becomes an artifact, and `sources.md` is required.

Promote the finished draft into a hashed and signed contribution:

```sh
contrib promote erdos-100
```

If you deliberately do not want a reward destination, use `--no-reward`. That choice is
permanent because the destination is part of the contribution ID.

Validate the contribution or the current changeset:

```sh
contrib check
contrib check --base origin/main
```

Finally, create a local contribution branch and commit:

```sh
contrib submit contributions/erdos-100/<contribution-id>
```

Add `--push` to push the branch to `origin`, or `--pr` to push it and run
`gh pr create --fill`. The latter requires an installed and authenticated GitHub CLI.

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
