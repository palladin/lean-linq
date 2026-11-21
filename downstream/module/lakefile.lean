import Lake
open Lake DSL

/-!
A package outside lean-linq whose source is in Lean's module system. Building
it with `lake build --wfail` checks that a module can import lean-linq, and
that neither build logs a warning.
-/

package «downstream-module»

require «lean-linq» from ".." / ".."

@[default_target]
lean_lib Consumer
