from pathlib import Path
from typing import Annotated

import typer

from . import config
from .config import ConfigKey
from .errors import guard
from .repo import RootOptions, Workspace

app = typer.Typer(
    add_completion=False, no_args_is_help=True, help="Resolve and pin the repository."
)


@app.command("show")
@guard
def show(ctx: typer.Context) -> None:
    workspace = Workspace.discover(override=_root_override(ctx))
    typer.echo(f"root    {workspace.root}  ({workspace.source})")
    pinned = config.pinned_repo()
    typer.echo(f"pinned  {pinned if pinned is not None else '(unset)'}")


@app.command("pin")
@guard
def pin(
    ctx: typer.Context,
    path: Annotated[
        Path | None, typer.Argument(help="Repository to pin; default is the one you are in.")
    ] = None,
) -> None:
    # Resolved through discover so a path that is not a repository is refused now, rather than
    # written and then failing on every later command.
    workspace = Workspace.discover(override=path if path is not None else _root_override(ctx))
    config.write(ConfigKey.REPO_PATH, str(workspace.root))
    typer.echo(f"pinned {workspace.root}")


@app.command("unpin")
@guard
def unpin() -> None:
    config.unset(ConfigKey.REPO_PATH)
    typer.echo("unpinned")


def _root_override(ctx: typer.Context) -> Path | None:
    options = ctx.obj
    return options.repo if isinstance(options, RootOptions) else None
