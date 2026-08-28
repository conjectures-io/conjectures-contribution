from __future__ import annotations

import pytest

from .conftest import Repo

LEAN = (
    "import Mathlib\n"
    "namespace Contribution.Demo\n"
    "theorem a : True := trivial\n"
    "end Contribution.Demo\n"
)


def _promote(repo: Repo, sources: str) -> tuple[str, ...]:
    return repo.errors(repo.promote(repo.draft(files={"sources.md": sources, "s.lean": LEAN})))


def test_a_bom_is_rejected(repo: Repo) -> None:
    files: dict[str, str | bytes] = {"sources.md": "\ufeff# Sources\n\n- Original.\n"}
    assert "C022" in repo.errors(repo.promote(repo.draft(files=files)))


def test_crlf_is_rejected(repo: Repo) -> None:
    files: dict[str, str | bytes] = {"sources.md": b"# Sources\r\n\r\n- Original.\r\n"}
    assert "C022" in repo.errors(repo.promote(repo.draft(files=files)))


def test_a_missing_final_newline_is_rejected(repo: Repo) -> None:
    files: dict[str, str | bytes] = {"sources.md": "# Sources\n\n- Original."}
    assert "C022" in repo.errors(repo.promote(repo.draft(files=files)))


def test_maths_unicode_is_accepted(repo: Repo) -> None:
    cited = "# Sources\n\n- Bounds on ℕ from [Er46](https://doi.org/10.2307/2305092)\n"
    assert _promote(repo, cited) == ()


def test_sources_must_attribute_something(repo: Repo) -> None:
    assert "C023" in _promote(repo, "# Sources\n\n")


@pytest.mark.parametrize(
    "line",
    [
        "- http://example.org/paper",
        "- https://bit.ly/abc",
        "- https://203.0.113.7/paper",
        "- ftp://example.org/paper",
    ],
)
def test_uncitable_links_are_rejected(repo: Repo, line: str) -> None:
    assert "C023" in _promote(repo, f"# Sources\n\n{line}\n")


# A single very long line is the shape that makes an unbounded URL pattern
# backtrack quadratically; the scan must stay linear.
def test_a_pathological_line_does_not_hang(repo: Repo) -> None:
    assert _promote(repo, "# Sources\n\n- " + "x" * 100_000 + "\n") == ()
