"""Workflow-command output, so findings land on the diff instead of in a log."""

from __future__ import annotations

import os
from pathlib import Path

import typer

from ..report import Report


def running_in_actions() -> bool:
    return bool(os.environ.get("GITHUB_ACTIONS"))


def publish(report: Report, outputs: dict[str, str] | None = None) -> None:
    if not running_in_actions():
        return
    annotations = report.to_annotations()
    if annotations:
        typer.echo(annotations)
    _append(os.environ.get("GITHUB_STEP_SUMMARY"), report.to_markdown() + "\n")
    if outputs:
        _append(
            os.environ.get("GITHUB_OUTPUT"),
            "".join(f"{key}={value}\n" for key, value in outputs.items()),
        )


def _append(target: str | None, text: str) -> None:
    if not target:
        return
    with Path(target).open("a", encoding="utf-8") as handle:
        handle.write(text)
