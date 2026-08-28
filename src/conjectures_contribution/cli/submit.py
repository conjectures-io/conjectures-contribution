from pathlib import Path
from typing import Annotated

import typer

from .. import report
from ..checks import run_all
from ..loader import load_context
from ..store import Published
from .errors import guard
from .git import GitError, current_branch, gh, require_gh, revision, run, submission_changes
from .repo import open_workspace


@guard
def submit(
    ctx: typer.Context,
    contribution: Annotated[Path, typer.Argument(help="Promoted contribution directory.")],
    push: Annotated[
        bool, typer.Option(help="Push the branch to origin; use --no-push for a local commit.")
    ] = True,
    pr: Annotated[
        bool, typer.Option(help="Open a pull request with gh; use --no-pr to skip it.")
    ] = True,
) -> None:
    workspace = open_workspace(ctx)
    directory = contribution.resolve()
    if not directory.is_relative_to(workspace.contributions):
        raise typer.BadParameter(f"{directory} is not under contributions/")

    relative = directory.relative_to(workspace.root)
    if not push and pr:
        raise typer.BadParameter("--no-push requires --no-pr")
    if current_branch(workspace.root) != "main":
        raise GitError("submit must start on the main branch; switch to main and try again")

    staged, unstaged, untracked = submission_changes(workspace.root)
    if staged:
        raise GitError("submit requires an empty staging area; commit or unstage staged changes")
    if unstaged:
        raise GitError("submit requires no tracked modifications; commit or restore them first")
    contribution_prefix = f"{relative.as_posix().rstrip('/')}/"
    unrelated = tuple(path for path in untracked if not path.startswith(contribution_prefix))
    if unrelated:
        raise GitError(
            "submit found untracked files outside the contribution; "
            "commit, remove, or ignore them first"
        )
    if not untracked:
        raise typer.BadParameter(f"{relative} is already committed; nothing to submit")
    if pr:
        require_gh(workspace.root)

    typer.echo("updating main from origin/main")
    run(workspace.root, "pull", "--ff-only", "origin", "main")
    if revision(workspace.root, "HEAD") != revision(workspace.root, "FETCH_HEAD"):
        raise GitError(
            "local main contains commits not in origin/main; reconcile it before submitting"
        )

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

    branch = f"contribution/{directory.name[:12]}"
    typer.echo(f"branch {branch} from origin/main")

    run(workspace.root, "switch", "--create", branch)
    run(workspace.root, "add", "--", str(relative))
    run(
        workspace.root,
        "commit",
        "--only",
        "--message",
        f"contribution: {relative.parent.name}",
        "--",
        str(relative),
    )

    if push:
        run(workspace.root, "push", "--set-upstream", "origin", branch)
    if pr:
        gh(workspace.root, "pr", "create", "--fill", "--base", "main")
    typer.echo(f"committed {relative}")
