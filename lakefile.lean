import Lake
open System Lake DSL

/-!
Each driver is its own `lean_lib`, which names its C shim and its system
client library in `moreLinkObjs`. Lake links those into every program that
imports the driver, in this package or another, and looks the client library
up only then. So `import LeanLinq` needs no client library at all, and a
program that imports one driver needs only that driver's.
-/

/-- The standard output of a command, trimmed, or `none` if it can't run. -/
def commandOutput? (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd, args }
    if out.exitCode == 0 then
      return some out.stdout.trimAscii.toString
    return none
  catch _ =>
    return none

/-- A Homebrew keg's directory, for macOS. -/
def brewPrefix? (keg : String) : IO (Option String) :=
  commandOutput? "brew" #["--prefix", keg]

-- Link arguments for this package's own programs. They hold no database
-- library, so Lake can load the package with none installed.
open Lean Elab Term in
elab "platformLinkArgs%" : term => do
  let args ←
    if System.Platform.isOSX then do
      -- The toolchain's bundled linker has its own sysroot and cannot read
      -- the macOS SDK's stubs, so use the matching Apple linker.
      let sdk ← IO.Process.output { cmd := "xcrun", args := #["--show-sdk-path"] }
      pure #["--ld-path=/usr/bin/ld", "-L" ++ sdk.stdout.trimAscii.toString ++ "/usr/lib"]
    else
      -- The system .so files carry glibc symbol versions newer than the
      -- toolchain's bundled glibc can satisfy at link time; at run time the
      -- system loader resolves them against the system glibc (same distro,
      -- always sufficient). Tell the linker to trust runtime for shlib
      -- references instead of failing on what it cannot see.
      pure #["-Wl,--allow-shlib-undefined"]
  return Lean.toExpr args

package «lean-linq» where
  version := v!"0.1.0"
  description := "Type-safe, deeply-embedded SQL query DSL for Lean 4 — LINQ-style pipelines and query! comprehensions compiling to parameterized SQL for SQLite, PostgreSQL, and SQL Server"
  keywords := #["sql", "linq", "dsl", "database", "query-builder"]
  homepage := "https://github.com/palladin/lean-linq"
  license := "MIT"
  testDriver := "tests"
  moreLinkArgs := platformLinkArgs%

/-! ## System client libraries

Each is linked by its explicit file path. The bundled `ld.lld` does not search
system library directories, and adding broad `-L` paths hijacks libc
resolution (the toolchain's `Scrt1.o` wants the bundled glibc, not the
system's — `__libc_csu_*` vanished in glibc 2.34). A path leaves every other
search untouched. -/

/-- The directories a Linux client library may live in. -/
def linuxLibDirs : Array FilePath :=
  #["/usr/lib/x86_64-linux-gnu", "/usr/lib/aarch64-linux-gnu", "/usr/lib64", "/usr/lib"]

/-- The first of `names` found in `dirs`, as the library `what`. -/
def findLibrary (what : String) (dirs : Array FilePath) (names : Array String) : IO FilePath := do
  for dir in dirs do
    for name in names do
      if ← (dir / name).pathExists then
        return dir / name
  throw <| IO.userError
    s!"lean-linq: {what} not found (install its development package); searched {dirs}"

/-- A client library: `linuxNames` in the Linux directories and `extraDir`, or
on macOS `macName` in the Homebrew keg `keg`. -/
def clientLibrary (what : String) (linuxNames : Array String) (keg macName : String)
    (extraDir : IO (Option String) := pure none) : IO FilePath := do
  if System.Platform.isOSX then
    let some dir ← brewPrefix? keg
      | throw <| IO.userError s!"lean-linq: {what} not found (`brew install {keg}`)"
    findLibrary what #[(dir : FilePath) / "lib"] #[macName]
  else
    let extra := ((← extraDir).map fun dir => #[(dir : FilePath)]).getD #[]
    findLibrary what (linuxLibDirs ++ extra) linuxNames

/-- SQLite's library. It ships with macOS, as a stub in the SDK. -/
def sqliteLibrary : IO FilePath := do
  if System.Platform.isOSX then
    let some sdk ← commandOutput? "xcrun" #["--show-sdk-path"]
      | throw <| IO.userError "lean-linq: `xcrun --show-sdk-path` failed"
    findLibrary "libsqlite3" #[(sdk : FilePath) / "usr" / "lib"] #["libsqlite3.tbd"]
  else
    findLibrary "libsqlite3" linuxLibDirs #["libsqlite3.so", "libsqlite3.so.0"]

target libsqlite3 : FilePath :=
  Job.async do
    sqliteLibrary

target libpq : FilePath :=
  Job.async do
    clientLibrary "libpq" #["libpq.so", "libpq.so.5"] "libpq" "libpq.dylib"
      (commandOutput? "pg_config" #["--libdir"])

target libsybdb : FilePath :=
  Job.async do
    clientLibrary "libsybdb (freetds)" #["libsybdb.so", "libsybdb.so.5"] "freetds" "libsybdb.dylib"

target libmysqlclient : FilePath :=
  Job.async do
    clientLibrary "libmysqlclient" #["libmysqlclient.so", "libmysqlclient.so.21"] "mysql-client"
      "libmysqlclient.dylib"

/-! ## C shims

Each wraps a client API into Lean-ABI functions. They compile with the
*system* C compiler (which knows where the client headers live — the
toolchain's bundled clang is `-nostdinc`), with Lean's include dir added for
`lean.h`. -/

/-- Builds `native/<name>.c` into a static library, with `includeDir` on the
include path if it gives one. -/
def buildShim (pkg : Package) (name : String) (includeDir : IO (Option String) := pure none) :
    FetchM (Job FilePath) := do
  let src ← inputTextFile <| pkg.dir / "native" / s!"{name}.c"
  let leanInclude := (← getLeanInstall).includeDir
  let clientInclude := ((← includeDir).map fun dir => #["-I", dir]).getD #[]
  let o ← buildO (pkg.buildDir / "native" / s!"{name}.o") src
    (#["-I", leanInclude.toString] ++ clientInclude) #["-O2"] "cc"
  buildStaticLib (pkg.staticLibDir / nameToStaticLib name) #[o]

target sqlite3_shim pkg : FilePath :=
  buildShim pkg "sqlite3_shim"

target libpq_shim pkg : FilePath :=
  buildShim pkg "libpq_shim" do
    if System.Platform.isOSX then
      return (← brewPrefix? "libpq").map (· ++ "/include")
    return (← commandOutput? "pg_config" #["--includedir"]).getD "/usr/include/postgresql"

target mysql_shim pkg : FilePath :=
  buildShim pkg "mysql_shim" do
    if System.Platform.isOSX then
      return (← brewPrefix? "mysql-client").map (· ++ "/include/mysql")
    return (← commandOutput? "mysql_config" #["--variable=pkgincludedir"]).getD "/usr/include/mysql"

target freetds_shim pkg : FilePath :=
  buildShim pkg "freetds_shim" do
    if System.Platform.isOSX then
      return (← brewPrefix? "freetds").map (· ++ "/include")
    return some "/usr/include"

/-! ## Libraries -/

/-- The core library. It has no native code and needs no client library. -/
@[default_target]
lean_lib LeanLinq

-- default target so `lake build` (and CI) type-checks the demos — an
-- undeclared demo file can silently rot otherwise
@[default_target]
lean_lib Playground

/-- What the drivers share. It has no native code. -/
lean_lib DriverCommon where
  roots := #[`LeanLinq.Driver.TextCell, `LeanLinq.Driver.Transaction, `LeanLinq.Driver.Wire]

/-- The SQLite driver, `import LeanLinq.Driver.Sqlite`. -/
lean_lib SqliteDriver where
  roots := #[`LeanLinq.Driver.Sqlite]
  moreLinkObjs := #[sqlite3_shim, libsqlite3]

/-- The PostgreSQL driver, `import LeanLinq.Driver.Postgres`. -/
lean_lib PostgresDriver where
  roots := #[`LeanLinq.Driver.Postgres]
  moreLinkObjs := #[libpq_shim, libpq]

/-- The SQL Server driver, `import LeanLinq.Driver.Mssql`. -/
lean_lib MssqlDriver where
  roots := #[`LeanLinq.Driver.Mssql]
  moreLinkObjs := #[freetds_shim, libsybdb]

/-- The MySQL driver, `import LeanLinq.Driver.Mysql`. -/
lean_lib MysqlDriver where
  roots := #[`LeanLinq.Driver.Mysql]
  moreLinkObjs := #[mysql_shim, libmysqlclient]

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
