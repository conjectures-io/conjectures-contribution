from pathlib import Path
from typing import Annotated

import typer

from .. import report
from ..checks import run_all
from ..loader import load_context
from ..store import Published
from .errors import guard
from .git import current_branch, gh, is_clean, run
from .repo import Workspace


@guard
def submit(
    contribution: Annotated[Path, typer.Argument(help="Promoted contribution directory.")],
    push: Annotated[bool, typer.Option(help="Push the branch to origin.")] = False,
    pr: Annotated[bool, typer.Option(help="Open a pull request with gh (implies --push).")] = False,
) -> None:
    workspace = Workspace.discover()
    directory = contribution.resolve()
    if not directory.is_relative_to(workspace.contributions):
        raise typer.BadParameter(f"{directory} is not under contributions/")

    findings = run_all(
        load_context(
            directory,
            contributions_root=workspace.contributions,
            pool=workspace.pool(),
            published=Published.scan(workspace.contributions),
        )
    )
    rendered = report.build(workspace.root, [(directory, findings)])
    if not rendered.ok:
        typer.echo(rendered.to_text(), err=True)
        raise typer.Exit(code=1)

    relative = directory.relative_to(workspace.root)
    branch = f"contribution/{directory.name[:12]}"
    typer.echo(f"branch {branch} from {current_branch(workspace.root)}")

    run(workspace.root, "switch", "--create", branch)
    run(workspace.root, "add", "--", str(relative))
    if is_clean(workspace.root):
        raise typer.BadParameter(f"{relative} is already committed; nothing to submit")
    run(workspace.root, "commit", "--message", f"contribution: {relative.parent.name}")

    if push or pr:
        run(workspace.root, "push", "--set-upstream", "origin", branch)
    if pr:
        # gh is optional tooling; failing here leaves a pushed branch the contributor can use.
        gh(workspace.root, "pr", "create", "--fill")
    typer.echo(f"committed {relative}")
