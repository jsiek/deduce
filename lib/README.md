
## Naming Convention for Theorems

* Theorem names are all lowercase, with words separated by underscore.
* The first word is the type, e.g. `uint`.
* The second word is the main function or operator, e.g. `add`.
* The third word is the second function or operator, if applicable.
* The rest of the name is descriptive.

## Module Files

A module is the top-level file with the module's name (for example, `UInt.pf`).
Larger modules are split internally across several helper files (for example,
`UIntDefs.pf`, `UIntAdd.pf`, `UIntMult.pf`, ...) that are `public import`-ed
from the main module file. Users of the standard library should import only the
top-level module (e.g. `import UInt`); the helper files are private
implementation details.

When you add a new top-level module here, also add it to the user-facing list
in `gh_pages/doc/StandardLib.md`. See `docs/knowledge-base/what-to-update.md`.

