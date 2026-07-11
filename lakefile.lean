import Lake
open Lake DSL

-- Link arguments for the system sqlite3 library. The toolchain's bundled
-- linker has its own sysroot and cannot see the macOS SDK, so on macOS the
-- SDK's library directory is resolved at configuration time via `xcrun`;
-- on Linux `-lsqlite3` suffices (libsqlite3-dev).
open Lean Elab Term in
elab "sqliteLinkArgs%" : term => do
  let base := #["-lsqlite3"]
  let args ←
    if System.Platform.isOSX then do
      let out ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
      pure (#["-L" ++ out.stdout.trimAscii.toString ++ "/usr/lib"] ++ base)
    else
      pure base
  return Lean.toExpr args

package «lean-linq» where
  version := v!"0.1.0"
  description := "Type-safe, deeply-embedded SQL query DSL for Lean 4 — LINQ-style pipelines and query! comprehensions compiling to parameterized SQL for SQLite, PostgreSQL, and SQL Server"
  keywords := #["sql", "linq", "dsl", "database", "query-builder"]
  homepage := "https://github.com/palladin/lean-linq"
  license := "MIT"
  testDriver := "tests"
  moreLinkArgs := sqliteLinkArgs%

@[default_target]
lean_lib LeanLinq

lean_lib Playground

/-- The native SQLite driver — a separate target so the core library stays
FFI-free (`import LeanLinq` never pulls native code). -/
lean_lib Driver where
  globs := #[.submodules `LeanLinq.Driver]

lean_lib Tests where
  globs := #[.submodules `Tests]

lean_exe tests where
  root := `Tests.Main

lean_exe integration where
  root := `Tests.Integration

lean_exe driver where
  root := `Tests.DriverT

/-- C shim wrapping the sqlite3 API into Lean-ABI functions. Compiled with
the *system* C compiler (which knows where `sqlite3.h` lives — the
toolchain's bundled clang is `-nostdinc`), with Lean's include dir added
for `lean.h`. -/
extern_lib sqlite3_shim pkg := do
  let src ← inputTextFile <| pkg.dir / "native" / "sqlite3_shim.c"
  let oFile := pkg.buildDir / "native" / "sqlite3_shim.o"
  let leanInclude := (← getLeanInstall).includeDir
  let o ← buildO oFile src #["-I", leanInclude.toString] #["-O2"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "sqlite3_shim") #[o]
