#!/usr/bin/env bash
# Install the pinned comparator toolchain and certify one master.
#
# Usage: scripts/run-comparator.sh <target>   # target ∈ {3rdMoment, 2ndMoment, goldbach}
#
# Assumes scripts/assemble-workspace.sh <target> has already produced $WORKSPACE.
# Linux only: comparator sandboxes with landrun (Landlock) under systemd-run.
set -euo pipefail

TARGET="${1:?usage: run-comparator.sh <3rdMoment|2ndMoment|goldbach>}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="${WORKSPACE:-$REPO_ROOT/_workspace}"
TOOLS="${TOOLS:-$REPO_ROOT/_tools}"
CONFIG="$REPO_ROOT/comparator/config/$TARGET.json"

# Pinned revisions (from leanprover/lean-eval).
COMPARATOR_REV="71b52ec29e06d4b7d882726553b1ceb99a2499e0"
# lean4export must be built against the SAME Lean version as the project (v4.31.0).
# The lean-eval pin (3de59f10bc4b, toolchain v4.32.0-rc1) produces
#   "failed to read file 'Challenge.olean', incompatible header".
# 8554815c2dc6 is the lean4export commit whose lean-toolchain is v4.31.0.
LEAN4EXPORT_REV="8554815c2dc6b7abe99ec1f08849c9759ba77947"
LANDRUN_REV="5ed4a3db3a4ad930d577215c6b9abaa19df7f99f"

mkdir -p "$TOOLS"

echo ">> installing landrun @ $LANDRUN_REV"
GOBIN="$TOOLS/bin" go install "github.com/zouuup/landrun/cmd/landrun@$LANDRUN_REV"
export PATH="$TOOLS/bin:$PATH"

echo ">> building lean4export @ $LEAN4EXPORT_REV"
if [ ! -d "$TOOLS/lean4export/.git" ]; then
  git clone https://github.com/leanprover/lean4export.git "$TOOLS/lean4export"
fi
( cd "$TOOLS/lean4export" && git checkout "$LEAN4EXPORT_REV" && lake build lean4export )
export PATH="$TOOLS/lean4export/.lake/build/bin:$PATH"
export COMPARATOR_LEAN4EXPORT="$TOOLS/lean4export/.lake/build/bin/lean4export"

echo ">> building comparator @ $COMPARATOR_REV"
if [ ! -d "$TOOLS/comparator/.git" ]; then
  git clone https://github.com/leanprover/comparator.git "$TOOLS/comparator"
fi
( cd "$TOOLS/comparator" && git checkout "$COMPARATOR_REV" && lake build comparator )
COMPARATOR_BIN="$TOOLS/comparator/.lake/build/bin/comparator"

echo ">> building the workspace (Master, Challenge, Solution)"
( cd "$WORKSPACE" && lake exe cache get \
    && lake build PrimeNumberTheoremAnd.MediumPNT PrimeNumberTheoremAnd.PerronFormula \
    && lake build Master Challenge Solution )

echo ">> running comparator on $CONFIG"
cd "$WORKSPACE"
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c "lake env '$COMPARATOR_BIN' '$CONFIG'"
