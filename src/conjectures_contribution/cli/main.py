import typer

from ..checks import changeset_checks
from ..checks import checks as registered_checks
from . import check as check_cmd
from . import key as key_cmd
from . import new as new_cmd
from . import promote as promote_cmd
from . import submit as submit_cmd

app = typer.Typer(
    add_completion=False,
    no_args_is_help=True,
    help="Prepare, validate, and submit contributions to the pinned conjecture pool.",
)

app.command("new", help="Scaffold a draft for a target.")(new_cmd.new)
app.command("promote", help="Hash, sign, and publish a draft into contributions/.")(
    promote_cmd.promote
)
app.command("check", help="Run every rule CI runs.")(check_cmd.check)
app.command("submit", help="Branch, commit, and optionally open a pull request.")(submit_cmd.submit)
app.add_typer(key_cmd.app, name="key")


@app.command("checks", help="List the rules by id.")
def list_checks() -> None:
    listed = [(c.id, c.title) for c in registered_checks()]
    listed += [(c.id, c.title) for c in changeset_checks()]
    for check_id, title in sorted(listed):
        typer.echo(f"{check_id}  {title}")
