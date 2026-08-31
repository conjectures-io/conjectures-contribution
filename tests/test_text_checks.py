from __future__ import annotations

import pytest

from conjectures_contribution.templates import (
    SCRIPT_FILENAME,
    SCRIPT_TEMPLATE,
    SOURCES_FILENAME,
    SOURCES_TEMPLATE,
    namespace_for,
)

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


# --- C024: the scaffold is not a contribution --------------------------------------------


def _scaffold() -> dict[str, str | bytes]:
    return {
        SOURCES_FILENAME: SOURCES_TEMPLATE,
        SCRIPT_FILENAME: SCRIPT_TEMPLATE.format(slug="demo-1", namespace=namespace_for("demo-1")),
    }


# The whole point of the rule: `contrib new` followed by `contrib promote`, with nothing
# in between, must not produce an admissible contribution.
def test_an_unedited_scaffold_is_rejected(repo: Repo) -> None:
    published = repo.promote(repo.draft(files=_scaffold()))
    assert "C024" in repo.errors(published)


def test_the_sources_placeholder_alone_is_rejected(repo: Repo) -> None:
    files: dict[str, str | bytes] = {
        SOURCES_FILENAME: SOURCES_TEMPLATE,
        SCRIPT_FILENAME: LEAN,
    }
    assert repo.errors(repo.promote(repo.draft(files=files))) == ("C024",)


def test_the_lean_placeholder_alone_is_rejected(repo: Repo) -> None:
    files: dict[str, str | bytes] = {
        SOURCES_FILENAME: "# Sources\n\n- Original work.\n",
        SCRIPT_FILENAME: SCRIPT_TEMPLATE.format(slug="demo-1", namespace="Demo"),
    }
    # One finding per surviving line: the docstring, the comment, and the theorem.
    found = repo.errors(repo.promote(repo.draft(files=files)))
    assert set(found) == {"C024"}
    assert len(found) == 3


# Reformatting the scaffold is not editing it; the rule matches the stripped line.
def test_an_indented_or_bulleted_placeholder_is_still_caught(repo: Repo) -> None:
    sources = (
        "# Sources\n\n"
        "  - Cite what this builds on: papers, Mathlib declarations, prior contributions.\n"
    )
    files: dict[str, str | bytes] = {SOURCES_FILENAME: sources, SCRIPT_FILENAME: LEAN}
    assert "C024" in repo.errors(repo.promote(repo.draft(files=files)))


def test_edited_scaffolding_passes(repo: Repo) -> None:
    files: dict[str, str | bytes] = {
        SOURCES_FILENAME: "# Sources\n\n- Adapted from [Er46](https://doi.org/10.2307/2305092).\n",
        SCRIPT_FILENAME: LEAN,
    }
    assert repo.errors(repo.promote(repo.draft(files=files))) == ()


def test_namespace_for_makes_a_lean_identifier() -> None:
    assert namespace_for("erdos-100-parts-i") == "Erdos100PartsI"
    assert namespace_for("") == "Draft"
