# Verification of the multigraph extension

The extension uses Lean `v4.35.0-rc3` and Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`, as did the registered simple case.

| Check | Result |
| --- | --- |
| Complete Solution build with `lake build --wfail` | Passed without warnings |
| Independent `Challenge.lean` build | Passed with ten intentional theorem placeholders |
| `lake env lean Audit.lean` | Passed for all ten compared theorems and boundary examples |
| Sandboxed `lake comparator --config comparator.json` | Passed |
| NanoDa kernel | Accepted the Solution export |
| Lean default kernel | Accepted the Solution export |

`verification/axioms.log` records the dependencies of all ten theorems:
only `propext`, `Classical.choice` and `Quot.sound`. There are no definition
holes in the Comparator configuration. The ten `sorry` placeholders occur
only in the independent Challenge, which Solution never imports.

`Audit.lean` checks that two distinct parallel edges have maximum degree two
and cannot be properly colored with one color. It also checks the empty-edge,
empty-vertex and empty-palette boundary. These examples test multiplicity and
the zero-degree case rather than assuming the graph is simple or nonempty.

The old three compared declarations are retained alongside seven new ones.
The inherited proof bodies are preserved. Mathlib imports in three Galvin
modules are narrowed, and the finite interval import is explicit. No result
from the other account's reserved unfinished repositories is assumed.

**Borodin–Kostochka–Woodall addition (`galvin_local`).** Checked with `lake build` of the
libraries, Challenge and Solution, a `pp.all` comparison of the ten elaborated Challenge and
Solution declarations (identical), and `lake env lean Audit.lean`, which also colours a small
multigraph with parallel edges from local lists. The sandboxed Comparator and NanoDa rows above
refer to the nine-theorem extension; for the ten theorems they are left to Palomar's preflight.

The local Comparator log is `verification/comparator.log`. Local evidence is
separate from Palomar's full reusable mechanical preflight and editorial
review. The multigraph extension is submitted as version 2 of the Palomar
entry. The version-1 registry record remains unchanged.

The extension was self-assessed by the same Codex session that produced it;
no independent human mathematical review of the extension has been performed.
