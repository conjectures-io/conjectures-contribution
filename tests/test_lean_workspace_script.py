"""`scripts/lean_workspace.sh` reads repository variables, which carry whatever whitespace
was pasted into the GitHub UI. A value of `"true\n"` looks exactly like `"true"` in the
settings page and in a workflow log, so a variable that is set must not be read as unset."""

import subprocess
from pathlib import Path

ROOT = Path(__file__).parents[1]
SCRIPT = ROOT / "scripts" / "lean_workspace.sh"
COMMIT = "0" * 40
NOT_CONFIGURED = "No Lean workspace configured."


def _run(env: dict[str, str], tmp_path: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(  # noqa: S603
        [str(SCRIPT), COMMIT],
        capture_output=True,
        text=True,
        check=False,
        env={"PATH": "/usr/bin:/bin", "HOME": str(tmp_path), **env},
    )


def test_a_padded_bootstrap_flag_still_enables_bootstrap(tmp_path: Path) -> None:
    origin = tmp_path / "origin.git"
    subprocess.run(["git", "init", "-q", "--bare", str(origin)], check=True)  # noqa: S603, S607
    result = _run(
        {
            "CONTRIB_LEAN_BOOTSTRAP": " true\n",
            "CONTRIB_LEAN_CACHE": str(tmp_path / "cache"),
            "CONTRIB_LEAN_REPO": str(origin),
        },
        tmp_path,
    )

    # It still fails — that empty origin has no such commit — but it must fail past the branch
    # that claims nothing was configured, which is where the untrimmed value landed.
    assert NOT_CONFIGURED not in result.stderr
    assert "building a workspace for formal-conjectures@" in result.stderr
    assert result.returncode != 0


def test_an_unset_bootstrap_flag_still_reports_that_nothing_is_configured(tmp_path: Path) -> None:
    result = _run({}, tmp_path)

    assert NOT_CONFIGURED in result.stderr
    assert result.returncode == 1


def test_a_padded_workspace_path_is_not_treated_as_a_missing_directory(tmp_path: Path) -> None:
    workspace = tmp_path / "prepared"
    workspace.mkdir()
    result = _run({"CONTRIB_LEAN_WORKSPACE": f"  {workspace}\n"}, tmp_path)

    # Untrimmed, the directory test fails and the runner is told the path does not exist.
    assert "does not exist on this runner" not in result.stderr
    assert "is not a git worktree" in result.stderr
