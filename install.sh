#!/usr/bin/env sh
# Install the `contrib` command. Uses uv when it is present; otherwise a private virtualenv,
# so Python 3.11 and nothing else is required.
set -eu

SOURCE=${CONJECTURES_CONTRIBUTION_SOURCE:-$(cd "$(dirname "$0")" && pwd)}
BIN=${BIN:-${PREFIX:-$HOME/.local}/bin}
VENV=${VENV:-${PREFIX:-$HOME/.local}/share/conjectures-contribution}

# Every command locates the repository by finding conjectures/allowlist.json, and that file
# lives in a submodule. A `contrib` that cannot find its pool is worse than no `contrib`.
if [ ! -f "$SOURCE/conjectures/allowlist.json" ]; then
    echo "install.sh: checking out the conjectures submodule" >&2
    git -C "$SOURCE" submodule update --init --recursive || {
        echo "install.sh: $SOURCE/conjectures is empty and could not be checked out." >&2
        echo "install.sh: run \`git submodule update --init --recursive\` there first." >&2
        exit 1
    }
fi

if command -v uv >/dev/null 2>&1; then
    # `--refresh-package` is not optional: the version does not change between builds, so uv
    # otherwise reinstalls the wheel it cached the first time and the install silently lands a
    # revision old. `--force` replaces the tool; it does not rebuild it.
    UV_TOOL_BIN_DIR=$BIN uv tool install --force \
        --refresh-package conjectures-contribution "$SOURCE"
else
    PY=$(command -v python3.14 || command -v python3.13 || command -v python3.12 ||
        command -v python3.11 || command -v python3) || {
        echo "install.sh: needs uv, or python3.11 or newer" >&2
        exit 1
    }
    "$PY" -c 'import sys; raise SystemExit(sys.version_info < (3, 11))' || {
        echo "install.sh: $PY is $("$PY" -V), and this needs 3.11 or newer" >&2
        exit 1
    }
    # An isolated environment, so nothing here can disturb the system Python and PEP 668 has
    # nothing to object to.
    "$PY" -m venv "$VENV"
    "$VENV/bin/python" -m pip install --upgrade --quiet pip
    "$VENV/bin/python" -m pip install --upgrade "$SOURCE"
    mkdir -p "$BIN"
    ln -sf "$VENV/bin/contrib" "$BIN/contrib"
    ln -sf "$VENV/bin/contrib-admin" "$BIN/contrib-admin"
fi

"$BIN/contrib" --version
# Completion is installed for whatever shell owns the calling process, which would be this
# script's `sh`. Ask the contributor's own shell to make the call instead. `|| exit 1` is
# load-bearing: a lone command is one a shell hands straight to `exec`, which would put `sh`
# back in that slot.
"${SHELL:-sh}" -c "'$BIN/contrib' --install-completion || exit 1" ||
    echo "install.sh: no completion for ${SHELL:-sh}; bash, zsh, fish and powershell have it." >&2

# Pinned so `contrib` also works from outside the checkout. Anyone standing inside it is found
# by the walk-up regardless, so moving the repository costs only a re-pin.
"$BIN/contrib" repo pin "$SOURCE"

case ":$PATH:" in
*":$BIN:"*) ;;
*) echo "install.sh: add $BIN to your PATH to run it as \`contrib\`." >&2 ;;
esac

# This tool keeps its own settings; conjectures-miner's config.toml is deliberately not read,
# so a wallet configured there has to be named here too.
"$BIN/contrib" config show
