#!/usr/bin/env bash
# Check that no Lean file imports the Mathlib umbrella module.
#
# `import Mathlib` pulls in all of Mathlib, which peaks around 6.5 GB RSS per Lean process.
# During a parallel Lake build several such processes create severe memory and GC pressure —
# one observed `PermutationInstantiation` build took 648 seconds despite compiling in about
# five seconds in isolation. PR #144 replaced every umbrella import with `Mathlib.Tactic` or
# narrower module imports; this script keeps the umbrella from creeping back in, since nothing
# else fails when it does — builds just quietly get slow again.
#
# The rule: no tracked `.lean` file may contain a bare `import Mathlib` (with or without a
# trailing comment). Submodule imports such as `import Mathlib.Tactic` are fine — that is the
# accepted broad-import compromise. If an umbrella import is ever legitimately needed, extend
# this script with an explicit allowlist rather than deleting the check.
#
# Run from the repository root; exits non-zero on violation.
set -euo pipefail

violations=$(git ls-files '*.lean' | xargs grep -nE '^import Mathlib([[:space:]]|$)' || true)

if [ -n "$violations" ]; then
  echo "::error::bare 'import Mathlib' umbrella imports are not allowed; import the specific Mathlib modules instead (see scripts/check_no_umbrella_imports.sh):"
  echo "$violations"
  exit 1
fi
