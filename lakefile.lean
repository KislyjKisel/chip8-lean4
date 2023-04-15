import Lake
open Lake DSL

require Raylib from git
  "https://github.com/KislyjKisel/Raylib.lean.git" @ "35a04816a5d237e11c2ba0aac02f0f31216f455a"

require mathlib4 from git
  "https://github.com/leanprover-community/mathlib4" @ "cab783282affcde08a2e0b4fff70423ff1f9a575"

require std4 from git
  "https://github.com/leanprover/std4" @ "70b5bc3054838f789cec4b6f088a1ffebc5926b1"

package chip8 {
  srcDir := "src"
}

lean_lib Chip8 {
  roots := #["Chip8", "Util"]
}

@[default_target]
lean_exe chip8 {
  root := `Main
  moreLinkArgs := #["-Llake-packages/Raylib/raylib/build/raylib", "-lraylib"]
}

extern_lib chip8_native (pkg : Package) := do
  let name := nameToStaticLib "chip8_native"
  let source ← inputFile <| pkg.srcDir / "native.c"

  let mut flags := #["-I", (← getLeanIncludeDir).toString, "-fPIC"]
  match pkg.deps.find? λ dep ↦ dep.name == `raylib with
    | none => IO.println "Missing dependency 'Raylib'"
    | some dep =>
      flags := flags ++ #[
        "-I", (dep.dir / "raylib" / "build" / "raylib" / "include").toString,
        "-I", (dep.dir / "src" / "native" / "include").toString
      ]

  let object ← buildO "native.c" (pkg.buildDir / "native.o") source flags
  buildStaticLib (pkg.libDir / name) #[object]
