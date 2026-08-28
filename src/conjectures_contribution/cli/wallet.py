from pathlib import Path
from typing import Annotated

import typer

from .. import wallet as wallet_module
from . import config
from .errors import guard

app = typer.Typer(
    add_completion=False, no_args_is_help=True, help="Inspect the Bittensor reward wallet."
)


@app.command("show")
@guard
def show(
    wallet: Annotated[str | None, typer.Option(help="Bittensor wallet name.")] = None,
    hotkey: Annotated[str | None, typer.Option(help="Hotkey name within that wallet.")] = None,
    wallet_path: Annotated[Path | None, typer.Option(help="Override the wallet directory.")] = None,
) -> None:
    settings = config.resolve(wallet, hotkey, wallet_path)
    for label, setting in (
        ("wallet_name", settings.name),
        ("wallet_hotkey", settings.hotkey),
        ("wallet_path", settings.path),
    ):
        typer.echo(f"{label:<14} {setting.value}  ({setting.source})")

    # Both come from the public keyfiles; nothing here unlocks a key.
    try:
        reward = wallet_module.addresses(settings.ref)
    except wallet_module.WalletError as exc:
        typer.secho(f"\nnot reward-eligible: {exc}", fg=typer.colors.YELLOW, err=True)
        raise typer.Exit(code=1) from None
    typer.echo(f"\ncoldkey        {reward.coldkey}\nhotkey         {reward.hotkey}")
