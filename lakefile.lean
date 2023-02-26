import Lake
open Lake DSL

require Raylib from git
  "https://github.com/KislyjKisel/Raylib.lean.git" @ "main"

require mathlib4 from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

require std4 from git
  "https://github.com/leanprover/std4" @ "main"

package chip8 {
  srcDir := "src"
}

lean_lib Chip8 {
  roots := #["Chip8", "Util"]
}

@[default_target]
lean_exe chip8 {
  root := `Main
  moreLinkArgs := #["-L/usr/local/lib", "-lraylib"]
}

extern_lib chip8_native (pkg : Package) := do
  let name := nameToStaticLib "chip8_native"
  let source ← inputFile <| pkg.srcDir / "native.c"

  let raylib_inc := (← IO.Process.output {
    cmd := "pkg-config"
    args := #["--cflags", "raylib"]
    cwd := pkg.dir
  }).stdout
  let mut flags := #["-I", (← getLeanIncludeDir).toString]
  match pkg.deps.find? λ dep ↦ dep.name == `raylib with
    | none => IO.println "Missing dependency 'Raylib'"
    | some dep =>
      flags := flags ++ #[ raylib_inc, "-I", (dep.dir / "src" / "native" / "include").toString ]

  let object ← buildO "native.c" (pkg.buildDir / "native.o") source flags
  buildStaticLib (pkg.libDir / name) #[object]
