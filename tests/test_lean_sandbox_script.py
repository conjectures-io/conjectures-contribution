"""`scripts/lean_sandbox.sh` builds the docker invocation that elaborates untrusted Lean.

The script needs docker to run, so these tests read the arguments it would pass rather than
executing it: a fake `docker` on PATH records its argv and exits, and `lake` is stubbed to
resolve a toolchain without a real one being present.
"""

import subprocess
from pathlib import Path

ROOT = Path(__file__).parents[1]
SCRIPT = ROOT / "scripts" / "lean_sandbox.sh"


def _harness(tmp_path: Path) -> tuple[Path, Path, Path]:
    bin_dir = tmp_path / "bin"
    bin_dir.mkdir()
    argv = tmp_path / "argv"

    toolchain = tmp_path / "toolchain"
    (toolchain / "bin").mkdir(parents=True)
    lean = toolchain / "bin" / "lean"
    lean.write_text("#!/bin/sh\nexit 0\n")
    lean.chmod(0o755)

    lake = bin_dir / "lake"
    lake.write_text(
        "#!/bin/sh\n"
        'case "$*" in\n'
        f'  *"which lean"*) echo "{lean}" ;;\n'
        '  *"printenv LEAN_PATH"*) echo "/nonexistent-lean-path" ;;\n'
        "esac\n"
    )
    lake.chmod(0o755)

    docker = bin_dir / "docker"
    docker.write_text(f'#!/bin/sh\nprintf "%s\\n" "$@" > "{argv}"\nexit 0\n')
    docker.chmod(0o755)

    return bin_dir, argv, toolchain


def _run(
    tmp_path: Path, memory_mb: str, env: dict[str, str] | None = None
) -> tuple[subprocess.CompletedProcess[str], list[str]]:
    bin_dir, argv, _ = _harness(tmp_path)
    workspace = tmp_path / "workspace"
    workspace.mkdir()
    source = tmp_path / "Main.lean"
    source.write_text("theorem t : True := trivial\n")

    result = subprocess.run(  # noqa: S603
        [str(SCRIPT), str(workspace), str(source), "900", memory_mb, "400000"],
        capture_output=True,
        text=True,
        check=False,
        env={"PATH": f"{bin_dir}:/usr/bin:/bin", "HOME": str(tmp_path), **(env or {})},
    )
    recorded = argv.read_text().splitlines() if argv.exists() else []
    return result, recorded


def test_the_thread_ceiling_admits_a_large_contribution(tmp_path: Path) -> None:
    result, argv = _run(tmp_path, "16384")

    assert result.returncode == 0, result.stderr
    # Lean takes a thread per elaboration task, so the ceiling scales with the size of the
    # file rather than the core count. At 128 a 5158-line contribution died on startup with
    # "failed to create thread" (exit 139); bisected on the DEV runner, it needs 129-192.
    assert "--pids-limit" in argv
    assert argv[argv.index("--pids-limit") + 1] == "1024"


def test_the_thread_ceiling_is_tunable_without_a_release(tmp_path: Path) -> None:
    _, argv = _run(tmp_path, "16384", {"CONTRIB_LEAN_PIDS_LIMIT": "2048"})

    assert argv[argv.index("--pids-limit") + 1] == "2048"


def test_a_malformed_thread_ceiling_is_refused(tmp_path: Path) -> None:
    result, argv = _run(tmp_path, "16384", {"CONTRIB_LEAN_PIDS_LIMIT": "unlimited"})

    assert result.returncode == 125
    assert "pids limit must be a positive integer" in result.stderr
    assert argv == []


def test_lean_is_given_the_whole_container_budget(tmp_path: Path) -> None:
    _, argv = _run(tmp_path, "16384")

    assert argv[argv.index("--memory") + 1] == "16384m"
    assert "--memory=16384" in argv


def test_the_container_cannot_dump_core_onto_the_host(tmp_path: Path) -> None:
    _, argv = _run(tmp_path, "16384")

    # A crash inside the container is dumped by the host kernel, as the host user, into the
    # host's crash directory: five Lean cores cost 31GB of the runner's disk.
    assert "--ulimit" in argv
    assert argv[argv.index("--ulimit") + 1] == "core=0"
