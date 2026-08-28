from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

from .checks.base import Finding, Severity


@dataclass(frozen=True, slots=True)
class Report:
    root: Path
    changeset: tuple[Finding, ...]
    results: tuple[tuple[Path, tuple[Finding, ...]], ...]

    @property
    def errors(self) -> int:
        return self._count(Severity.ERROR)

    @property
    def warnings(self) -> int:
        return self._count(Severity.WARNING)

    @property
    def reviews(self) -> int:
        return self._count(Severity.REVIEW)

    @property
    def needs_review(self) -> bool:
        return self.reviews > 0

    def _count(self, severity: Severity) -> int:
        every = (*self.changeset, *(f for _, fs in self.results for f in fs))
        return sum(1 for f in every if f.severity is severity)

    @property
    def ok(self) -> bool:
        return self.errors == 0

    def to_json(self) -> str:
        return json.dumps(
            {
                "ok": self.ok,
                "errors": self.errors,
                "warnings": self.warnings,
                "reviews": self.reviews,
                "needs_review": self.needs_review,
                "changeset": [f.to_json() for f in self.changeset],
                "results": [
                    {"contribution": self._relative(path), "findings": [f.to_json() for f in fs]}
                    for path, fs in self.results
                ],
            },
            indent=2,
            sort_keys=True,
        )

    def to_text(self) -> str:
        lines: list[str] = []
        if self.changeset:
            lines.append("changeset")
            lines.extend(self._render(f) for f in self.changeset)
        for path, findings in self.results:
            lines.append(self._relative(path))
            if not findings:
                lines.append("  ok")
            lines.extend(self._render(f) for f in findings)
        lines.append(
            f"{len(self.results)} contribution(s), "
            f"{self.errors} error(s), {self.warnings} warning(s)"
        )
        return "\n".join(lines)

    # GitHub renders these against the diff, which is where a contributor is already
    # looking; the text report is what they get locally.
    def to_annotations(self) -> str:
        kinds = {Severity.ERROR: "error", Severity.REVIEW: "warning", Severity.WARNING: "notice"}
        lines: list[str] = []
        for path, findings in ((None, self.changeset), *self.results):
            for finding in findings:
                kind = kinds.get(finding.severity)
                if kind is None:
                    continue
                located = self._annotation_path(path, finding)
                where = f"file={located}," if located else ""
                lines.append(f"::{kind} {where}title={finding.check_id}::{finding.message}")
        return "\n".join(lines)

    def to_markdown(self) -> str:
        icons = {
            Severity.ERROR: "❌",
            Severity.REVIEW: "🔎",
            Severity.WARNING: "⚠️",
            Severity.SKIPPED: "⏭",
        }
        state = "passed" if self.ok else "failed"
        lines = [f"### Contribution checks — {state}", ""]
        every = (*self.changeset, *(f for _, fs in self.results for f in fs))
        if not every:
            lines += [f"{len(self.results)} contribution(s), no findings.", ""]
            return "\n".join(lines)
        lines += ["| | Rule | Where | Detail |", "| --- | --- | --- | --- |"]
        for path, findings in ((None, self.changeset), *self.results):
            for finding in findings:
                where = self._annotation_path(path, finding) or "changeset"
                detail = finding.message.replace("|", "\\|")
                lines.append(
                    f"| {icons[finding.severity]} | `{finding.check_id}` | `{where}` | {detail} |"
                )
        lines.append("")
        return "\n".join(lines)

    def _annotation_path(self, contribution: Path | None, finding: Finding) -> str:
        if contribution is None:
            return finding.path or ""
        base = self._relative(contribution)
        return f"{base}/{finding.path}" if finding.path else base

    def _render(self, finding: Finding) -> str:
        location = f" {finding.path}:" if finding.path else ""
        return f"  {finding.check_id} {finding.severity:<7}{location} {finding.message}"

    def _relative(self, path: Path) -> str:
        try:
            return str(path.relative_to(self.root))
        except ValueError:
            return str(path)


def build(
    root: Path,
    results: Sequence[tuple[Path, Sequence[Finding]]],
    changeset: Sequence[Finding] = (),
) -> Report:
    return Report(
        root=root,
        changeset=tuple(changeset),
        results=tuple((p, tuple(f)) for p, f in results),
    )
