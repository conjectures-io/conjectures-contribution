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
        every = (*self.changeset, *(f for _, fs in self.results for f in fs))
        return sum(1 for f in every if f.severity is Severity.ERROR)

    @property
    def ok(self) -> bool:
        return self.errors == 0

    def to_json(self) -> str:
        return json.dumps(
            {
                "ok": self.ok,
                "errors": self.errors,
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
        lines.append(f"{len(self.results)} contribution(s), {self.errors} error(s)")
        return "\n".join(lines)

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
