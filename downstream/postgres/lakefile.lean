import Lake
open Lake DSL

/-!
A package outside lean-linq that uses the PostgreSQL driver. Building it
checks what a downstream project gets: Lake loads lean-linq with only the
PostgreSQL client development files installed, builds the libpq shim, and
links libpq, with no link settings here.
-/

package «downstream-postgres»

require «lean-linq» from ".." / ".."

@[default_target]
lean_exe pgcheck where
  root := `Main
