#!/bin/bash
# UFRF Lean 4 Project Setup
# Run this after cloning to set up the build environment.

set -e

echo "=== UFRF Lean 4 Formalization Setup ==="
echo ""

# Check for elan/lean
if ! command -v lean &> /dev/null; then
    echo "ERROR: Lean 4 not found. Install via:"
    echo "  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh"
    exit 1
fi

echo "Lean version: $(lean --version)"
echo ""

# Check for lake
if ! command -v lake &> /dev/null; then
    echo "ERROR: Lake not found. It should come with Lean 4."
    exit 1
fi

echo "Step 1: Updating lake dependencies..."
lake update

echo ""
echo "Step 2: Downloading Mathlib cache (this saves ~30 min of compilation)..."
lake exe cache get || echo "WARNING: cache get failed; Mathlib will be compiled from source."

echo ""
echo "Step 3: Building UFRF..."
lake build

echo ""
echo "=== Build Complete ==="
echo ""

# Audit sorry statements
echo "=== Sorry Audit ==="
echo "Remaining sorry statements (proof obligations):"
echo ""
grep -rn "sorry" UFRF/ --include="*.lean" | grep -v "^--" | grep -v "AXIOM" || echo "  None! All proofs complete."

echo ""
echo "=== Axiom Audit ==="
echo "Intentional axioms (foundational postulates):"
echo ""
grep -rn "^axiom " UFRF/ --include="*.lean" || echo "  None found."

echo ""
echo "Done. Open in VS Code with the Lean 4 extension for interactive checking."
