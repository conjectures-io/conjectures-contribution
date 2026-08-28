import json
import shutil
from pathlib import Path
from typing import Annotated

import typer

from .. import report
from ..build import Built
from ..checks import run_all
from ..loader import load_context
from ..model import DRAFT_FILENAME, Draft
from ..signing import SigningKey
from ..store import Published
from ..wallet import RewardSigner, WalletError
from . import complete, config
from .errors import guard
from .repo import Workspace, key_path, open_workspace


@guard
def promote(
    ctx: typer.Context,
    target: Annotated[
        str | None,
        typer.Argument(help="Target slug of the draft.", autocompletion=complete.drafts),
    ] = None,
    source: Annotated[
        Path | None, typer.Option("--from", help="Draft directory; default is drafts/<target>.")
    ] = None,
    key: Annotated[Path | None, typer.Option(help="Signing key file.")] = None,
    wallet: Annotated[
        str | None,
        typer.Option(help="Bittensor wallet name.", autocompletion=complete.wallets),
    ] = None,
    hotkey: Annotated[
        str | None,
        typer.Option(help="Hotkey name within that wallet.", autocompletion=complete.hotkeys),
    ] = None,
    wallet_path: Annotated[Path | None, typer.Option(help="Override the wallet directory.")] = None,
    no_reward: Annotated[
        bool, typer.Option("--no-reward", help="Publish without a reward destination.")
    ] = False,
) -> None:
    workspace = open_workspace(ctx)
    directory = _resolve_draft(workspace, target, source)
    draft = Draft.parse(json.loads((directory / DRAFT_FILENAME).read_text(encoding="utf-8")))
    if target is not None and str(draft.target) != target:
        raise typer.BadParameter(f"draft declares target '{draft.target}', not '{target}'")

    reward = _reward(config.resolve(wallet, hotkey, wallet_path), opted_out=no_reward)

    pool = workspace.pool()
    signing_key = SigningKey.load(key_path(key))
    built = Built.from_draft(draft, directory, pool, signing_key, reward)
    destination = built.write(workspace.contributions)

    findings = run_all(
        load_context(
            destination,
            contributions_root=workspace.contributions,
            pool=pool,
            published=Published.scan(workspace.contributions),
        )
    )
    rendered = report.build(workspace.root, [(destination, findings)])
    if not rendered.ok:
        shutil.rmtree(destination)
        typer.echo(rendered.to_text(), err=True)
        raise typer.Exit(code=1)

    typer.echo(str(destination.relative_to(workspace.root)))


def _resolve_draft(workspace: Workspace, target: str | None, source: Path | None) -> Path:
    if source is not None:
        directory = source.resolve()
    elif target is not None:
        directory = workspace.drafts / target
    else:
        candidates = [
            p for p in sorted(workspace.drafts.glob("*")) if (p / DRAFT_FILENAME).is_file()
        ]
        if len(candidates) != 1:
            raise typer.BadParameter(f"expected one draft in drafts/, found {len(candidates)}")
        directory = candidates[0]
    if not (directory / DRAFT_FILENAME).is_file():
        raise typer.BadParameter(f"{directory}: no {DRAFT_FILENAME}")
    return directory


# The reward keys are hashed into the contribution id, so a contribution promoted without
# them can never gain them. Refusing here makes that irreversible choice a deliberate one.
def _reward(settings: config.WalletSettings, *, opted_out: bool) -> RewardSigner | None:
    if opted_out:
        typer.secho(
            "warning: no reward destination; this contribution is not eligible for a reward",
            fg=typer.colors.YELLOW,
            err=True,
        )
        return None
    ref = settings.ref
    try:
        return RewardSigner.open(ref)
    except WalletError as exc:
        typer.secho(f"error: {exc}", fg=typer.colors.RED, err=True)
        typer.secho(
            "\n  Reward keys are part of the contribution id, so they cannot be added\n"
            "  after promotion.\n\n"
            f"  Point at a wallet:    --wallet <name> --hotkey <name>\n"
            f"  Or set it once:       {config.ENV_PREFIX}WALLET_NAME=<name>,"
            f" or {config.config_file()}\n"
            "  Or opt out knowingly: --no-reward",
            err=True,
        )
        raise typer.Exit(code=2) from None
