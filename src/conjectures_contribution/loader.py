from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .checks.base import CheckContext
from .model import METADATA_FILENAME, Contribution, SchemaError
from .pool import Pool
from .store import Published


def load_context(
    directory: Path,
    *,
    contributions_root: Path,
    pool: Pool,
    published: Published,
) -> CheckContext:
    raw_bytes: bytes | None = None
    raw: Any | None = None
    contribution: Contribution | None = None
    parse_error: str | None = None

    try:
        raw_bytes = (directory / METADATA_FILENAME).read_bytes()
    except (FileNotFoundError, NotADirectoryError):
        parse_error = f"{METADATA_FILENAME} is missing"

    if raw_bytes is not None:
        try:
            raw = json.loads(raw_bytes.decode("utf-8"))
        except UnicodeDecodeError:
            parse_error = f"{METADATA_FILENAME} is not valid UTF-8"
        except json.JSONDecodeError as exc:
            parse_error = f"invalid JSON: {exc}"

    if raw is not None:
        try:
            contribution = Contribution.parse(raw)
        except SchemaError as exc:
            parse_error = str(exc)

    return CheckContext(
        directory=directory,
        contributions_root=contributions_root,
        pool=pool,
        published=published,
        raw=raw,
        raw_bytes=raw_bytes,
        contribution=contribution,
        parse_error=parse_error,
    )
