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
  roots := #["Chip8", "Timer"]
}

@[default_target]
lean_exe chip8 {
  root := `Main
  moreLinkArgs := #["-L/usr/local/lib", "-lraylib"]
}
