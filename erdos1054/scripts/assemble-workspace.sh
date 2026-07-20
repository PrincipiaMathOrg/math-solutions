#!/usr/bin/env bash
# Assemble a comparator workspace for one master.
#
# Usage: scripts/assemble-workspace.sh <target>   # target ∈ {3rdMoment, 2ndMoment, goldbach}
#
# Clones PrimeNumberTheoremAnd @ the pinned rev, copies the selected master in as
# module `Master`, drops in the comparator Challenge and the matching Solution
# bridge, and registers Master/Challenge/Solution as lean_libs so the project
# builds them. Produces a checkout at $WORKSPACE (default: ./_workspace).
set -euo pipefail

TARGET="${1:?usage: assemble-workspace.sh <3rdMoment|2ndMoment|goldbach>}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
WORKSPACE="${WORKSPACE:-$REPO_ROOT/_workspace}"

PNT_REPO="https://github.com/AlexKontorovich/PrimeNumberTheoremAnd"
PNT_REV="d963a6e694a05cd82e5f9b9ae7f4d94123e85393"

case "$TARGET" in
  3rdMoment) MASTER="Erdos1054_3rdMomentProof.lean" ;;
  2ndMoment) MASTER="Erdos1054_2ndMomentProof.lean" ;;
  goldbach)  MASTER="GoldbachChainMaster.lean" ;;
  *) echo "unknown target: $TARGET" >&2; exit 1 ;;
esac

echo ">> assembling comparator workspace for $TARGET (master: $MASTER)"

if [ ! -d "$WORKSPACE/.git" ]; then
  git clone "$PNT_REPO" "$WORKSPACE"
fi
git -C "$WORKSPACE" fetch --depth 1 origin "$PNT_REV" || git -C "$WORKSPACE" fetch origin
git -C "$WORKSPACE" checkout "$PNT_REV"

# Copy the sources in as top-level modules of the PNT+ package.
cp "$REPO_ROOT/masters/$MASTER"                    "$WORKSPACE/Master.lean"
cp "$REPO_ROOT/comparator/Challenge.lean"          "$WORKSPACE/Challenge.lean"
cp "$REPO_ROOT/comparator/Solution_$TARGET.lean"   "$WORKSPACE/Solution.lean"

# Register the three modules as lean_libs if not already present.
LAKEFILE="$WORKSPACE/lakefile.toml"
for lib in Master Challenge Solution; do
  if ! grep -q "name = \"$lib\"" "$LAKEFILE"; then
    printf '\n[[lean_lib]]\nname = "%s"\n' "$lib" >> "$LAKEFILE"
  fi
done

echo ">> workspace ready at $WORKSPACE"
echo ">> config: $REPO_ROOT/comparator/config/$TARGET.json"
