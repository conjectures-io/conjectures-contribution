from pathlib import Path
from typing import Annotated

import typer

from .. import report
from ..checks import run_all
from ..loader import load_context
from ..store import Published
from .errors import guard
from .git import (
    GitError,
    current_branch,
    gh,
    prepare_fork,
    require_gh,
    run,
    submission_changes,
    update_main,
)
from .repo import open_workspace

UPSTREAM_REPOSITORY = "conjectures-io/conjectures-contribution"
UPSTREAM_URL = f"https://github.com/{UPSTREAM_REPOSITORY}.git"
UPSTREAM_REMOTE = "contribution-upstream"
FORK_REMOTE = "contribution-fork"


def _require_submission_changes(root: Path, relative: Path) -> None:
    staged, unstaged, untracked = submission_changes(root)
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


@guard
def submit(
    ctx: typer.Context,
    contribution: Annotated[Path, typer.Argument(help="Promoted contribution directory.")],
    push: Annotated[
        bool, typer.Option(help="Push the branch to origin; use --no-push for a local commit.")
    ] = True,
    pr: Annotated[
        bool,
        typer.Option(
            help=(
                "Open a pull request against conjectures-io/conjectures-contribution with gh; "
                "use --no-pr to skip it."
            )
        ),
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

    _require_submission_changes(workspace.root, relative)
    if pr:
        require_gh(workspace.root)

    typer.echo(f"updating main from {UPSTREAM_REPOSITORY}")
    update_main(workspace.root, UPSTREAM_URL)
    _require_submission_changes(workspace.root, relative)

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
    typer.echo(f"branch {branch} from canonical main")

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

    if pr:
        owner, fork_remote = prepare_fork(
            workspace.root,
            UPSTREAM_REPOSITORY,
            UPSTREAM_URL,
            UPSTREAM_REMOTE,
            FORK_REMOTE,
        )
        run(workspace.root, "push", "--set-upstream", fork_remote, branch)
        gh(
            workspace.root,
            "pr",
            "create",
            "--repo",
            UPSTREAM_REPOSITORY,
            "--base",
            "main",
            "--head",
            f"{owner}:{branch}",
            "--title",
            f"contribution: {relative.parent.name}",
            "--body-file",
            ".github/pull_request_template.md",
        )
    elif push:
        run(workspace.root, "push", "--set-upstream", "origin", branch)
    typer.echo(f"committed {relative}")
