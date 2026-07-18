import Lake
open Lake DSL

-- Link arguments for the system database libraries (sqlite3, libpq). The
-- toolchain's bundled linker has its own sysroot and cannot see the macOS
-- SDK or Homebrew kegs, so their library directories are resolved at
-- configuration time (`xcrun`, `brew --prefix libpq`); on Linux the system
-- linker finds both (libsqlite3-dev, libpq-dev).
open Lean Elab Term in
elab "dbLinkArgs%" : term => do
  let base := #["-lsqlite3", "-lpq", "-lsybdb", "-lmysqlclient"]
  let args ←
    if System.Platform.isOSX then do
      let sdk ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
      let pq ← IO.Process.output { cmd := "brew", args := #["--prefix", "libpq"] }
      let tds ← IO.Process.output { cmd := "brew", args := #["--prefix", "freetds"] }
      let my ← IO.Process.output { cmd := "brew", args := #["--prefix", "mysql-client"] }
      pure (#["-L" ++ sdk.stdout.trimAscii.toString ++ "/usr/lib",
              "-L" ++ pq.stdout.trimAscii.toString ++ "/lib",
              "-L" ++ tds.stdout.trimAscii.toString ++ "/lib",
              "-L" ++ my.stdout.trimAscii.toString ++ "/lib"] ++ base)
    else do
      -- The bundled ld.lld does not search system library dirs, and adding
      -- broad -L paths hijacks libc resolution (the toolchain's Scrt1.o
      -- wants the bundled glibc, not the system's — __libc_csu_* vanished
      -- in glibc 2.34). So: link the two libraries by explicit file path,
      -- leaving every other search untouched.
      let mut dirs := #["/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu",
                        "/usr/lib64", "/usr/lib"]
      try
        let out ← IO.Process.output { cmd := "pg_config", args := #["--libdir"] }
        dirs := dirs.push out.stdout.trimAscii.toString
      catch _ => pure ()
      let find (names : List String) (what : String) : TermElabM String := do
        for d in dirs do
          for n in names do
            if ← System.FilePath.pathExists (d ++ "/" ++ n) then
              return d ++ "/" ++ n
        throwError "lakefile: {what} not found (install the -dev package); searched {dirs}"
      let sqlite ← find ["libsqlite3.so", "libsqlite3.so.0"] "libsqlite3"
      let pq ← find ["libpq.so", "libpq.so.5"] "libpq"
      let tds ← find ["libsybdb.so", "libsybdb.so.5"] "libsybdb (freetds)"
      let my ← find ["libmysqlclient.so", "libmysqlclient.so.21"] "libmysqlclient"
      -- The system .so files carry glibc symbol versions newer than the
      -- toolchain's bundled glibc can satisfy at link time; at run time the
      -- system loader resolves them against the system glibc (same distro,
      -- always sufficient). Tell the linker to trust runtime for shlib
      -- references instead of failing on what it cannot see.
      pure #[sqlite, pq, tds, my, "-Wl,--allow-shlib-undefined"]
  return Lean.toExpr args

-- Include directory for libpq headers, resolved the same way (Linux:
-- `pg_config --includedir`, falling back to the Debian default).
open Lean Elab Term in
elab "pqIncludeDir%" : term => do
  let dir ←
    if System.Platform.isOSX then do
      let pq ← IO.Process.output { cmd := "brew", args := #["--prefix", "libpq"] }
      pure (pq.stdout.trimAscii.toString ++ "/include")
    else do
      try
        let out ← IO.Process.output { cmd := "pg_config", args := #["--includedir"] }
        pure out.stdout.trimAscii.toString
      catch _ =>
        pure "/usr/include/postgresql"
  return Lean.toExpr dir

def pqIncludeDir : String := pqIncludeDir%

-- FreeTDS include directory (sybdb.h): brew keg on macOS, /usr/include on Linux.
open Lean Elab Term in
elab "tdsIncludeDir%" : term => do
  let dir ←
    if System.Platform.isOSX then do
      let tds ← IO.Process.output { cmd := "brew", args := #["--prefix", "freetds"] }
      pure (tds.stdout.trimAscii.toString ++ "/include")
    else
      pure "/usr/include"
  return Lean.toExpr dir

def tdsIncludeDir : String := tdsIncludeDir%

open Lean Elab Term in
elab "mysqlIncludeDir%" : term => do
  let dir ←
    if System.Platform.isOSX then do
      let my ← IO.Process.output { cmd := "brew", args := #["--prefix", "mysql-client"] }
      pure (my.stdout.trimAscii.toString ++ "/include/mysql")
    else do
      try
        let out ← IO.Process.output { cmd := "mysql_config", args := #["--variable=pkgincludedir"] }
        pure out.stdout.trimAscii.toString
      catch _ => pure "/usr/include/mysql"
  return Lean.toExpr dir

def mysqlIncludeDir : String := mysqlIncludeDir%

package «lean-linq» where
  version := v!"0.1.0"
  description := "Type-safe, deeply-embedded SQL query DSL for Lean 4 — LINQ-style pipelines and query! comprehensions compiling to parameterized SQL for SQLite, PostgreSQL, and SQL Server"
  keywords := #["sql", "linq", "dsl", "database", "query-builder"]
  homepage := "https://github.com/palladin/lean-linq"
  license := "MIT"
  testDriver := "tests"
  moreLinkArgs := dbLinkArgs%

@[default_target]
lean_lib LeanLinq

-- default target so `lake build` (and CI) type-checks the demos — an
-- undeclared demo file can silently rot otherwise
@[default_target]
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

lean_exe sqlitedriver where
  root := `Tests.SqliteDriverT

lean_exe pgdriver where
  root := `Tests.PgDriverT

lean_exe mssqldriver where
  root := `Tests.MssqlDriverT

lean_exe mysqldriver where
  root := `Tests.MysqlDriverT

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

extern_lib libpq_shim pkg := do
  let src ← inputTextFile <| pkg.dir / "native" / "libpq_shim.c"
  let oFile := pkg.buildDir / "native" / "libpq_shim.o"
  let leanInclude := (← getLeanInstall).includeDir
  let o ← buildO oFile src
    #["-I", leanInclude.toString, "-I", pqIncludeDir] #["-O2"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "libpq_shim") #[o]

extern_lib mysql_shim pkg := do
  let src ← inputTextFile <| pkg.dir / "native" / "mysql_shim.c"
  let oFile := pkg.buildDir / "native" / "mysql_shim.o"
  let leanInclude := (← getLeanInstall).includeDir
  let o ← buildO oFile src
    #["-I", leanInclude.toString, "-I", mysqlIncludeDir] #["-O2"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "mysql_shim") #[o]

extern_lib freetds_shim pkg := do
  let src ← inputTextFile <| pkg.dir / "native" / "freetds_shim.c"
  let oFile := pkg.buildDir / "native" / "freetds_shim.o"
  let leanInclude := (← getLeanInstall).includeDir
  let o ← buildO oFile src
    #["-I", leanInclude.toString, "-I", tdsIncludeDir] #["-O2"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "freetds_shim") #[o]
