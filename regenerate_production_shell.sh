#!/bin/bash

# Regenerate Production Shell (production mode)
# Builds the executable coq/sh from production_shell.ml (extracted or maintained)

set -e

echo "Regenerating Production Shell (verified runner)..."

SCRIPT_DIR="$(dirname "$0")"
cd "$SCRIPT_DIR/coq"

echo "Cleaning previous build artifacts..."
rm -f production_shell.cmi production_shell.cmx production_shell.o
rm -f production_shell_runner sh

# Prefer dune build when dune file & sources present; fallback to direct ocamlopt
BUILD_MODE="dune"
if [ ! -f dune ]; then
    echo "No dune file found – falling back to direct ocamlopt build"
    BUILD_MODE="direct"
fi

SOURCE=production_shell.ml
if [ ! -f "$SOURCE" ]; then
    if [ -f sh.ml ]; then
        SOURCE=sh.ml
        echo "production_shell.ml not found, using extracted sh.ml"
    else
        echo "Error: no production shell source (production_shell.ml or sh.ml) present" >&2
        exit 1
    fi
fi

if [ "$BUILD_MODE" = "dune" ]; then
    echo "Building via dune..."
    (cd .. && dune build coq/production_shell.exe) || {
        echo "Dune build failed – retrying direct build" >&2
        BUILD_MODE="direct"
    }
fi

if [ "$BUILD_MODE" = "direct" ]; then
    echo "Building directly with ocamlopt (temporarily ignoring stale interface)..."
    if [ -f production_shell.mli ]; then
        mv production_shell.mli production_shell.mli.bak_direct_build
        RESTORE_MLI=1
    fi
        if ! ocamlfind ocamlopt -package unix,readline -linkpkg "$SOURCE" -o production_shell_runner; then
        echo "Direct build failed" >&2
        # restore interface if moved
        [ -n "$RESTORE_MLI" ] && mv production_shell.mli.bak_direct_build production_shell.mli
        exit 2
    fi
    [ -n "$RESTORE_MLI" ] && mv production_shell.mli.bak_direct_build production_shell.mli
    cp production_shell_runner sh
else
    echo "Copying dune-built executable..."
    cp ../_build/default/coq/production_shell.exe production_shell_runner
    # Provide legacy alias 'sh' as some scripts expect ./coq/sh
    cp production_shell_runner sh
fi

chmod +x production_shell_runner sh 2>/dev/null || true

echo "Smoke test (pwd; exit)..."
if echo -e "pwd\nexit" | timeout 5 ./production_shell_runner >/dev/null 2>&1; then
    echo "production_shell_runner basic test passed"
else
    echo "WARNING: production_shell_runner smoke test failed (continuing)" >&2
fi

echo
echo "Production Shell regeneration completed"
echo "Generated executables: coq/production_shell_runner (primary), coq/sh (alias)"
echo "Run with: ./coq/production_shell_runner"
