from importlib.metadata import version
from pathlib import Path
from typing import Annotated

import typer

from ..checks import changeset_checks
from ..checks import checks as registered_checks
from . import check as check_cmd
from . import config_cmd, repo_cmd
from . import elaborate as elaborate_cmd
from . import key as key_cmd
from . import new as new_cmd
from . import promote as promote_cmd
from . import repo as repo_module
from . import submit as submit_cmd
from . import wallet as wallet_cmd

app = typer.Typer(
    add_completion=True,
    no_args_is_help=True,
    help="Prepare, validate, and submit contributions to the pinned conjecture pool.",
)

DISTRIBUTION = "conjectures-contribution"


def _version(value: bool) -> None:
    if value:
        typer.echo(f"{DISTRIBUTION} {version(DISTRIBUTION)}")
        raise typer.Exit


@app.callback()
def root(
    ctx: typer.Context,
    repo: Annotated[
        Path | None, typer.Option(help="Repository to act on; default is the one you are in.")
    ] = None,
    pool: Annotated[
        Path | None,
        typer.Option(help="Trusted conjecture pool to use instead of <repository>/conjectures."),
    ] = None,
    _show_version: Annotated[
        bool,
        typer.Option("--version", callback=_version, is_eager=True, help="Print the version."),
    ] = False,
) -> None:
    ctx.obj = repo_module.RootOptions(repo=repo, pool=pool)


app.command("new", help="Scaffold a draft for a target.")(new_cmd.new)
app.command("promote", help="Hash, sign, and publish a draft into contributions/.")(
    promote_cmd.promote
)
app.command("check", help="Run every static rule CI runs.")(check_cmd.check)
app.command("elaborate", help="Compile the Lean sources against a prepared Lake workspace.")(
    elaborate_cmd.elaborate
)
app.command("submit", help="Branch, commit, push, and open a pull request.")(submit_cmd.submit)
app.add_typer(config_cmd.app, name="config")
app.add_typer(key_cmd.app, name="key")
app.add_typer(repo_cmd.app, name="repo")
app.add_typer(wallet_cmd.app, name="wallet")


@app.command("checks", help="List the rules by id.")
def list_checks() -> None:
    listed = [(c.id, c.title) for c in registered_checks()]
    listed += [(c.id, c.title) for c in changeset_checks()]
    for check_id, title in sorted(listed):
        typer.echo(f"{check_id}  {title}")
