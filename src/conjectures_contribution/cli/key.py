from pathlib import Path
from typing import Annotated

import typer

from ..signing import SigningKey
from .errors import guard
from .repo import key_path

app = typer.Typer(add_completion=False, no_args_is_help=True, help="Manage the signing key.")


@app.command("generate")
@guard
def generate(
    path: Annotated[Path | None, typer.Option(help="Where to write the key.")] = None,
) -> None:
    destination = key_path(path)
    signing_key = SigningKey.generate()
    signing_key.save(destination)
    typer.echo(f"{destination}\n{signing_key.public_key}")


@app.command("show")
@guard
def show(path: Annotated[Path | None, typer.Option(help="Key file to read.")] = None) -> None:
    typer.echo(str(SigningKey.load(key_path(path)).public_key))
