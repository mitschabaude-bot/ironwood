import Lean

/-!
# Suppress the library-suggestions symbol-frequency indexer

On toolchains before v4.31.0, the `symbolFrequency` environment extension's export
function runs `whnf` over every local theorem signature with the default heartbeat
limit, and panics on a timeout (leanprover/lean4#12989, fixed upstream by
leanprover/lean4#13202). The limit cannot be raised from outside. Some deployed AGM
modules in this repository have signatures large enough to exceed it, so their builds
print panics and the Lean InfoView becomes unusable.

Adding `Zcash` to the library-suggestions name deny list makes the indexer skip every
declaration with a `Zcash` name component before reading its signature; the export
fold only visits the current module's declarations, so the entry affects only this
repository's theorems. The cost is that they are excluded from library-suggestions
ranking and candidate pools, which are used only by opt-in suggestion-driven tactics —
nothing in this repository enables one, and the in-tree `grind` calls run on explicit
lemma lists and `@[grind]` annotations. `exact?`, `apply?`, and `aesop?` use separate
machinery (`librarySearch` and Aesop rule sets) and are unaffected. Import this module
from any module whose export hits the panic; the entry also propagates to that
module's importers. The suppression is only needed on toolchains before v4.31.0.
-/

open Lean LibrarySuggestions in
run_cmd modifyEnv fun env => nameDenyListExt.addEntry env "Zcash"
