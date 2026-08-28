import functools
from collections.abc import Callable
from typing import Any, TypeVar

import typer

from ..build import BuildError
from ..model import SchemaError
from ..pool import PoolError
from ..signing import SigningError
from ..wallet import WalletError
from .git import GitError
from .repo import WorkspaceError

DOMAIN_ERRORS = (
    BuildError,
    GitError,
    PoolError,
    SchemaError,
    SigningError,
    WalletError,
    WorkspaceError,
)

F = TypeVar("F", bound=Callable[..., Any])


def guard(fn: F) -> F:
    @functools.wraps(fn)
    def wrapper(*args: Any, **kwargs: Any) -> Any:
        try:
            return fn(*args, **kwargs)
        except DOMAIN_ERRORS as exc:
            typer.secho(f"error: {exc}", fg=typer.colors.RED, err=True)
            raise typer.Exit(code=2) from None

    return wrapper  # type: ignore[return-value]
