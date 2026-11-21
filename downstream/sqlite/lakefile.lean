import Lake
open Lake DSL

/-!
A package outside lean-linq that uses the SQLite driver. Building and running
it checks what a downstream project gets: Lake builds the sqlite3 shim and
links SQLite, with the link settings this file shows.

On macOS it has none. On Linux, Ubuntu 24.04's SQLite uses newer glibc
symbols than Lean's bundled glibc, so the program adds the flag below, as the
README describes.
-/

package «downstream-sqlite» where
  moreLinkArgs :=
    if System.Platform.isOSX then #[] else #["-Wl,--allow-shlib-undefined"]

require «lean-linq» from ".." / ".."

@[default_target]
lean_exe sqlitecheck where
  root := `Main
