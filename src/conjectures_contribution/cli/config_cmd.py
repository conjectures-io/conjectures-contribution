from typing import Annotated

import typer

from . import config
from .config import ConfigKey
from .errors import guard

app = typer.Typer(add_completion=False, no_args_is_help=True, help="Read and write settings.")


@app.command("show")
@guard
def show() -> None:
    typer.echo(f"file    {config.config_file()}\n")
    settings = config.resolve()
    for key, setting in (
        (ConfigKey.WALLET_NAME, settings.name),
        (ConfigKey.WALLET_HOTKEY, settings.hotkey),
        (ConfigKey.WALLET_PATH, settings.path),
    ):
        typer.echo(f"{key:<14} {setting.value}  ({setting.source})")
    pinned = config.pinned_repo()
    typer.echo(f"{ConfigKey.REPO_PATH:<14} {pinned if pinned is not None else '(unset)'}")


@app.command("set")
@guard
def set_(
    key: Annotated[ConfigKey, typer.Argument(help="Setting to write.")],
    value: Annotated[str, typer.Argument(help="Its new value.")],
) -> None:
    config.write(key, value)
    typer.echo(f"{key} = {value}")


@app.command("unset")
@guard
def unset(key: Annotated[ConfigKey, typer.Argument(help="Setting to remove.")]) -> None:
    config.unset(key)
    typer.echo(f"{key} unset")
