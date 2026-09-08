"""`scripts/lean_workspace.sh` reads repository variables, which carry whatever whitespace
was pasted into the GitHub UI. A value of `"true\n"` looks exactly like `"true"` in the
settings page and in a workflow log, so a variable that is set must not be read as unset."""

import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

import pytest

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


def _stub_elan(tmp_path: Path) -> Path:
    """The bootstrap branch checks for elan before it does anything else. Whether a real one
    is on PATH differs between a developer's machine and a GitHub-hosted runner, so stub it
    and let the branch be reached either way."""
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    elan = bin_dir / "elan"
    elan.write_text("#!/bin/sh\nexit 0\n")
    elan.chmod(0o755)
    return bin_dir


def test_a_padded_bootstrap_flag_still_enables_bootstrap(tmp_path: Path) -> None:
    origin = tmp_path / "origin.git"
    subprocess.run(["git", "init", "-q", "--bare", str(origin)], check=True)  # noqa: S603, S607
    result = _run(
        {
            "CONTRIB_LEAN_BOOTSTRAP": " true\n",
            "CONTRIB_LEAN_CACHE": str(tmp_path / "cache"),
            "CONTRIB_LEAN_REPO": str(origin),
            "PATH": f"{_stub_elan(tmp_path)}:/usr/bin:/bin",
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


def test_an_operator_managed_workspace_never_prunes_the_cache(tmp_path: Path) -> None:
    cache = tmp_path / "cache"
    stale = cache / ("a" * 40)
    (stale / ".git").mkdir(parents=True)
    (stale / "bulk").write_bytes(b"x" * 1024)
    current = cache / COMMIT
    (current / ".git").mkdir(parents=True)
    (current / ".git" / "contrib-ready").touch()
    subprocess.run(["git", "init", "-q", str(current)], check=True)  # noqa: S603, S607

    result = _run({"CONTRIB_LEAN_WORKSPACE": str(current)}, tmp_path)
    assert result.returncode != 0  # HEAD is not the all-zero commit

    # An operator-managed CONTRIB_LEAN_WORKSPACE is not ours to tidy around, so nothing in
    # the cache may be touched on that path.
    assert stale.exists()


def test_the_cache_hit_path_prunes_other_commits(tmp_path: Path) -> None:
    cache = tmp_path / "cache"
    stale = cache / ("b" * 40)
    stale.mkdir(parents=True)
    (stale / "bulk").write_bytes(b"x" * 1024)
    current = cache / COMMIT
    current.mkdir(parents=True)
    (current / ".git").mkdir()
    (current / ".git" / "contrib-ready").touch()

    result = _run(
        {
            "CONTRIB_LEAN_BOOTSTRAP": "true",
            "CONTRIB_LEAN_CACHE": str(cache),
            "PATH": f"{_stub_elan(tmp_path)}:/usr/bin:/bin",
        },
        tmp_path,
    )

    # Each of these is ~13GB on the runner and nothing else removes them.
    assert not stale.exists(), result.stderr
    assert current.exists()
    assert "removing superseded workspace" in result.stderr


def _audited_source(tmp_path: Path) -> tuple[Path, Path, Path, dict[str, str], dict[str, str]]:
    origin = tmp_path / "origin"
    origin.mkdir()
    identity = {
        "GIT_AUTHOR_NAME": "Conjectures Pool Builder",
        "GIT_AUTHOR_EMAIL": "pool@conjectures.io",
        "GIT_AUTHOR_DATE": "2026-08-03T00:00:00Z",
        "GIT_COMMITTER_NAME": "Conjectures Pool Builder",
        "GIT_COMMITTER_EMAIL": "pool@conjectures.io",
        "GIT_COMMITTER_DATE": "2026-08-03T00:00:00Z",
    }

    def git(*args: str) -> str:
        return subprocess.check_output(  # noqa: S603
            ["git", "-C", str(origin), *args],  # noqa: S607
            text=True,
            env={**os.environ, **identity},
        ).strip()

    git("init", "-q")
    (origin / "Statement.lean").write_text("-- original statement\n")
    git("add", ".")
    git("-c", "commit.gpgsign=false", "commit", "-qm", "upstream")
    base = git("rev-parse", "HEAD")
    (origin / "Statement.lean").write_text("-- audited statement\n")
    git("add", ".")
    git(
        "-c",
        "commit.gpgsign=false",
        "commit",
        "-qm",
        "fix(ErdosProblems): correct audited candidate statements",
    )
    expected = git("rev-parse", "HEAD")
    patch_bytes = (git("diff", base, expected) + "\n").encode()
    git("checkout", "-q", base)

    source = tmp_path / "tooling"
    scripts = source / "scripts"
    scripts.mkdir(parents=True)
    script = scripts / SCRIPT.name
    shutil.copy2(SCRIPT, script)
    patch = source / "conjectures/tiers/tier-1/formal-conjectures-audit-fixes.patch"
    patch.parent.mkdir(parents=True)
    patch.write_bytes(patch_bytes)
    pin = {
        "base_commit": base,
        "commit": expected,
        "patch_sha256": hashlib.sha256(patch_bytes).hexdigest(),
    }
    (source / "lean-source.json").write_text(json.dumps(pin))
    bin_dir = _stub_elan(tmp_path)
    lake = bin_dir / "lake"
    lake.write_text('#!/bin/sh\nprintf "%s\\n" "$*" >> "$LAKE_CALLS"\n')
    lake.chmod(0o755)
    environment = {
        "HOME": str(tmp_path),
        "PATH": f"{bin_dir}:/usr/bin:/bin",
        "CONTRIB_LEAN_BOOTSTRAP": "true",
        "CONTRIB_LEAN_CACHE": str(tmp_path / "cache"),
        "CONTRIB_LEAN_REPO": str(origin),
        "LAKE_CALLS": str(tmp_path / "lake-calls"),
    }
    return script, source, patch, pin, environment


def test_bootstrap_reconstructs_the_exact_audited_commit_before_build(tmp_path: Path) -> None:
    script, _, _, pin, environment = _audited_source(tmp_path)
    result = subprocess.run(  # noqa: S603
        [str(script), pin["commit"]],
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    workspace = Path(result.stdout.strip())
    assert (workspace / "Statement.lean").read_text() == "-- audited statement\n"
    assert (workspace / ".git/contrib-ready").is_file()
    assert (tmp_path / "lake-calls").read_text().splitlines() == ["exe cache get", "build"]


@pytest.mark.parametrize("mismatch", ["patch", "commit"])
def test_bootstrap_refuses_audit_mismatches_before_running_lake(
    tmp_path: Path,
    mismatch: str,
) -> None:
    script, source, patch, pin, environment = _audited_source(tmp_path)
    if mismatch == "patch":
        patch.write_bytes(patch.read_bytes() + b"\n")
    else:
        pin["commit"] = "a" * 40
        (source / "lean-source.json").write_text(json.dumps(pin))
    result = subprocess.run(  # noqa: S603
        [str(script), pin["commit"]],
        env=environment,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode != 0
    assert "audit patch" in result.stderr
    assert not (tmp_path / "lake-calls").exists()
    assert not (tmp_path / "cache" / pin["commit"] / ".git/contrib-ready").exists()
