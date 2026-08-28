from __future__ import annotations

import pytest

from conjectures_contribution.lean import declarations, strip_comments

from .conftest import Repo

CLEAN = """\
import Mathlib
import FormalConjectures.ErdosProblems.«89»

namespace Contribution.Demo

theorem le_self (n : ℕ) : n ≤ n := le_refl n

end Contribution.Demo
"""

WRAPPED = "import Mathlib\nnamespace Contribution.Demo\n{body}\nend Contribution.Demo\n"


def test_a_clean_contribution_passes(repo: Repo) -> None:
    published = repo.with_lean(CLEAN)
    assert repo.errors(published) == ()
    assert repo.reviews(published) == ()


@pytest.mark.parametrize(
    "body",
    [
        "theorem a : False := by sorry",
        "theorem a : False := by admit",
        "axiom bad : False",
        "theorem a : True := by native_decide",
        "set_option debug.skipKernelTC true in\ntheorem a : True := trivial",
        "set_option maxHeartbeats 0 in\ntheorem a : True := trivial",
        "#eval (1 : Nat)",
        'run_cmd Lean.logInfo "hi"',
        "initialize x : Nat <- pure 1",
        "unsafe def a : Nat := 1",
        '@[extern "c_fn"] def a : Nat := 1',
        'def a := IO.FS.readFile "/etc/passwd"',
        "theorem x : True := Bounty.target",
    ],
)
def test_dangerous_constructs_are_rejected(repo: Repo, body: str) -> None:
    published = repo.with_lean(WRAPPED.format(body=body))
    assert "C019" in repo.errors(published)


def test_the_reserved_namespace_is_rejected(repo: Repo) -> None:
    source = "import Mathlib\nnamespace Bounty\ntheorem t : True := trivial\nend Bounty\n"
    assert "C019" in repo.errors(repo.with_lean(source))


@pytest.mark.parametrize(
    "body",
    [
        'macro "foo" : tactic => `(tactic| skip)',
        "attribute [simp] Nat.add_zero",
        "open Lean",
    ],
)
def test_metaprogramming_is_review_not_rejection(repo: Repo, body: str) -> None:
    source = f"import Mathlib\n{body}\n" + WRAPPED.format(body="theorem a : True := trivial")
    published = repo.with_lean(source)
    assert repo.errors(published) == ()
    assert "C019" in repo.reviews(published)


def test_the_word_sorry_in_a_docstring_is_fine(repo: Repo) -> None:
    source = "import Mathlib\n/-- Sorry, no sorry here. -/\n" + WRAPPED.format(
        body="theorem a : True := trivial"
    )
    assert repo.errors(repo.with_lean(source)) == ()


def test_an_import_outside_the_allowlist_is_rejected(repo: Repo) -> None:
    source = "import Mathlib\nimport Evil.Payload\n" + WRAPPED.format(
        body="theorem a : True := trivial"
    )
    assert "C020" in repo.errors(repo.with_lean(source))


def test_importing_lean_asks_for_review(repo: Repo) -> None:
    source = "import Mathlib\nimport Lean\n" + WRAPPED.format(body="theorem a : True := trivial")
    published = repo.with_lean(source)
    assert repo.errors(published) == ()
    assert "C020" in repo.reviews(published)


def test_a_file_that_declares_nothing_is_rejected(repo: Repo) -> None:
    assert "C021" in repo.errors(repo.with_lean("import Mathlib\n"))


def test_a_root_namespace_declaration_asks_for_review(repo: Repo) -> None:
    published = repo.with_lean("import Mathlib\ntheorem loose : True := trivial\n")
    assert repo.errors(published) == ()
    assert "C021" in repo.reviews(published)


def test_two_files_cannot_declare_the_same_name(repo: Repo) -> None:
    source = WRAPPED.format(body="theorem a : True := trivial")
    published = repo.promote(
        repo.draft(files={"sources.md": "# Sources\n\n- x.\n", "a.lean": source, "b.lean": source})
    )
    assert "C021" in repo.errors(published)


def test_declarations_are_namespace_qualified() -> None:
    source = (
        "namespace A\nnamespace B\ntheorem t : True := trivial\nend B\n"
        "section\nlemma l : True := trivial\nend\nend A\n"
    )
    assert declarations(source) == ("A.B.t", "A.l")


def test_block_comments_are_stripped_across_lines() -> None:
    stripped = strip_comments("/-\nsorry\n-/\ntheorem a : True := trivial\n")
    assert "sorry" not in "".join(stripped[:3])
    assert "theorem" in stripped[3]
