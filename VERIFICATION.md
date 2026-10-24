# Verification of the multigraph extension

The extension uses Lean `v4.35.0-rc3` and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, as did the registered simple case.

| Check | Result |
| --- | --- |
| Complete Solution build with `lake build --wfail` | Passed without warnings |
| Independent `Challenge.lean` build | Passed with nine intentional theorem placeholders |
| `lake env lean Audit.lean` | Passed for all nine compared theorems and boundary examples |
| Sandboxed `lake comparator --config comparator.json` | Passed |
| NanoDa kernel | Accepted the Solution export |
| Lean default kernel | Accepted the Solution export |

`verification/axioms.log` records the dependencies of all nine theorems:
only `propext`, `Classical.choice` and `Quot.sound`. There are no definition
holes in the Comparator configuration. The nine `sorry` placeholders occur
only in the independent Challenge, which Solution never imports.

`Audit.lean` checks that two distinct parallel edges have maximum degree two
and cannot be properly colored with one color. It also checks the empty-edge,
empty-vertex and empty-palette boundary. These examples test multiplicity and
the zero-degree case rather than assuming the graph is simple or nonempty.

The old three compared declarations are retained alongside six new ones.
The inherited proof bodies are preserved. Mathlib imports in three Galvin
modules are narrowed, and the finite interval import is explicit. No result
from the other account's reserved unfinished repositories is assumed.

The local Comparator log is `verification/comparator.log`. Local evidence is
separate from Palomar's full reusable mechanical preflight and editorial
review. The multigraph extension has not yet been registered as a new Palomar
version. The version-1 registry record remains unchanged.

The extension was self-assessed by the same Codex session that produced it;
no independent human mathematical review of the extension has been performed.
