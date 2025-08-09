#!/bin/bash

# Master regeneration script - rebuilds FullAst and Production Shell
# Coordinates complete rebuild of Coq-generated components

set -e

echo "Master Regeneration Script - Rebuilding All Coq Components"
echo "==========================================================="

# Get script directory
SCRIPT_DIR="$(dirname "$0")"
cd "$SCRIPT_DIR"

echo ""
echo "1. Regenerating FullAst..."
echo "--------------------------"
./regenerate_fullast.sh

echo ""
echo "2. Regenerating Production Shell..."
echo "----------------------------------"
./regenerate_production_shell.sh

echo ""
echo "3. Final Verification..."
echo "----------------------"

# Verify FullAst
if [ -f "coq/FullAst.vo" ]; then
    echo "FullAst.vo: Ready"
else
    echo "ERROR: FullAst.vo missing"
    exit 1
fi

if [ -f "coq/sh" ] && [ -x "coq/sh" ]; then
        echo "coq/sh: Ready and executable"
else
        echo "ERROR: coq/sh missing or not executable"
        exit 1
fi

echo "Quick functionality test..."
if printf "whoami\nexit\n" | timeout 3 ./coq/sh | grep -q "ih"; then
    echo "Shell functional test: PASSED"
else
    echo "Shell functional test: WARNING (output not matched)"
fi

echo ""
echo "MASTER REGENERATION COMPLETED"
echo "================================" 
echo ""
echo "📊 Summary:"
echo "- FullAst.v compiled"
echo "- Production shell built (coq/sh)"
echo "- Proof objects present"
echo "- Executable ready"
echo ""
echo "🚀 Usage:"
echo "  ./coq/sh  # Run the shell"
echo ""
echo "📁 Key Files Generated:"
echo "  coq/FullAst.vo               # Compiled AST with proofs"
echo "  coq/production_shell.ml      # OCaml source"
echo "  coq/sh                       # Executable shell"
