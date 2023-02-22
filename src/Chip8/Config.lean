import Raylib
import Chip8.Const

set_option autoImplicit false

namespace Chip8

inductive QuirkMemIndex where
  /-- Keep `I` unchanged -/
  | Keep
  /-- Set index to the address of the last accessed mem cell. `I := I + X` -/
  | AddX
  /-- Set index to the address one past the last accessed mem cell. `I := I + X + 1` -/
  | AddX1

structure Config where
  instructions_per_sec : Float
  ramSizeS : Σ (ramSize : UInt16), PLift (ramPrefixSize ≤ ramSize) := Sigma.mk 4096 $ PLift.up $ by decide
  /-- Maximum size of the stack (levels of nesting) -/
  stackSize : Nat
  displayWidth : Nat := 64
  displayHeight : Nat := 32
  color0 : Raylib.Color
  color1 : Raylib.Color
  /--
  Controls the behavior of [BNNN].
  `false`: jump to `NNN` + `V0` (COSMAC VIP).
  `true`: jump to `NNN` + `VX` (CHIP48/SCHIP).
  -/
  quirkJumpOffset : Bool := false
  /--
  Controls the behavior of [8XY6] and [8XYE].
  `false`: `VX := VY <<< 1` (COSMAC VIP).
  `true`: `VX := VX <<< 1` (CHIP48/SCHIP).
  -/
  quirkShift : Bool := false
  /--
  Controls the behavior of [FX1E].
  `false`: `VF` is not affected.
  `true`: `VF` is set on "overflow" (0x1000).
  -/
  quirkIndexAdd : Bool := false
  /--
  Controls `I` changes during [FX55] and [FX65].
  -/
  quirkMemIndex : QuirkMemIndex := QuirkMemIndex.AddX1
  /-- Adds [00FD] instruction: exit -/
  extExit : Bool := false

def Config.ramSize (cfg : Config) : UInt16 :=
  cfg.ramSizeS.fst
def Config.ramSize_prefix (cfg : Config) : ramPrefixSize ≤ cfg.ramSize :=
  cfg.ramSizeS.snd.down

def presetCosmacVip : Config where
  instructions_per_sec := 600 -- roughly
  stackSize := 12
  color0 := Raylib.BLACK
  color1 := Raylib.GREEN

instance instInhabitedConfig : Inhabited Config where
  default := { presetCosmacVip with
    quirkIndexAdd := true
    stackSize := 128
    color1 := Raylib.RAYWHITE
  }

end Chip8
