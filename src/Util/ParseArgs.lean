import Chip8.Const
import Chip8.Config

private
structure Args where
  ramSize : Option $ Σ (ramSize : UInt16), PLift $ Chip8.ramPrefixSize ≤ ramSize
  romName : Option String
  instructions_per_sec : Option Float
  stackSize : Option Nat
  displayWidth : Option Nat
  displayHeight : Option Nat
  color0 : Option Raylib.Color
  color1 : Option Raylib.Color
  quirkJumpOffset : Option Bool
  quirkShift : Option Bool
  quirkIndexAdd : Option Bool
  quirkMemIndex : Option Chip8.QuirkMemIndex
  quirkBitwiseFlag : Option Bool
  quirkDisplayInt : Option Bool
  quirkGetKeyRel : Option Bool

deriving Inhabited

private
def aux (rest : Except String Args) (name : String) (view : Args → Option α) (set : Args → Args)
  : Except String Args := do
  let ps ← rest
  if (view ps).isSome
    then throw s!"Argument specified multiple times: {name}"
    else pure $ set ps

private
def parseColor (src : String) : Option Raylib.Color :=
  match src.toLower with
    | "lightgray" => some Raylib.LIGHTGRAY
    | "gray" => some Raylib.GRAY
    | "darkgray" => some Raylib.DARKGRAY
    | "yellow" => some Raylib.YELLOW
    | "gold" => some Raylib.GOLD
    | "orange" => some Raylib.ORANGE
    | "pink" => some Raylib.PINK
    | "red" => some Raylib.RED
    | "maroon" => some Raylib.MAROON
    | "green" => some Raylib.GREEN
    | "lime" => some Raylib.LIME
    | "darkgreen" => some Raylib.DARKGREEN
    | "skyblue" => some Raylib.SKYBLUE
    | "blue" => some Raylib.BLUE
    | "darkblue" => some Raylib.DARKBLUE
    | "purple" => some Raylib.PURPLE
    | "violet" => some Raylib.VIOLET
    | "darkpurple" => some Raylib.DARKPURPLE
    | "beige" => some Raylib.BEIGE
    | "brown" => some Raylib.BROWN
    | "darkbrown" => some Raylib.DARKBROWN
    | "black" => some Raylib.BLACK
    | "magenta" => some Raylib.MAGENTA
    | "white" => some Raylib.RAYWHITE
    | _other => none

private
def parseArgs' (args : List String) : Except String Args :=
  match args with
    | [] => pure default

    | "--ram" :: ram :: as =>
      match ram.toNat? with
      | some ram =>
        if ram_pref: Chip8.ramPrefixSize.toNat ≤ ram
          then
            if ram_x16: ram < UInt16.size
              then aux (parseArgs' as) "ram size" Args.ramSize λ as ↦ { as with
                ramSize := some $ Sigma.mk ⟨ram, ram_x16⟩ (PLift.up ram_pref)
              }
              else throw "ram size is too large"
          else throw s!"ram size smaller than prefix size ({Chip8.ramPrefixSize})"
      | none => throw "can't parse: ram size"

    | "--ips" :: ips :: as =>
      match ips.toNat? with
        | some ips => aux (parseArgs' as) "instructions per second" Args.instructions_per_sec λ as ↦ { as with
          instructions_per_sec := some ips.toFloat
        }
        | none => throw "can't parse: instructions per second"

    | "--stack" :: stack :: as =>
      match stack.toNat? with
        | some stack => aux (parseArgs' as) "stack size" Args.stackSize λ as ↦ { as with
          stackSize := stack
        }
        | none => throw "can't parse: stack size"

    | "--dw" :: dw :: as =>
      match dw.toNat? with
        | some dw => aux (parseArgs' as) "display width" Args.displayWidth λ as ↦ { as with
          displayWidth := some dw
        }
        | none => throw "can't parse: display width"

    | "--dh" :: dh :: as =>
      match dh.toNat? with
        | some dh => aux (parseArgs' as) "display height" Args.displayHeight λ as ↦ { as with
          displayHeight := some dh
        }
        | none => throw "can't parse: display height"

    | "--c0" :: c0 :: as =>
      match parseColor c0 with
        | some c0 => aux (parseArgs' as) "color 0" Args.color0 λ as ↦ { as with
          color0 := some c0
        }
        | none => throw "can't parse: color 0"

    | "--c1" :: c1 :: as =>
      match parseColor c1 with
        | some c1 => aux (parseArgs' as) "color 1" Args.color1 λ as ↦ { as with
          color1 := some c1
        }
        | none => throw "can't parse: color 0"

    | "--Qjump-offset" :: as =>
      aux (parseArgs' as) "quirk 'jump with offset uses VX'" Args.quirkJumpOffset λ as ↦ { as with
        quirkJumpOffset := some true
      }

    | "--Qno-jump-offset" :: as =>
      aux (parseArgs' as) "quirk 'jump with offset uses VX'" Args.quirkJumpOffset λ as ↦ { as with
        quirkJumpOffset := some false
      }

    | "--Qshift" :: as =>
      aux (parseArgs' as) "quirk 'shift in-place'" Args.quirkShift λ as ↦ { as with
        quirkShift := some true
      }

    | "--Qno-shift" :: as =>
      aux (parseArgs' as) "quirk 'shift in-place'" Args.quirkShift λ as ↦ { as with
        quirkShift := some false
      }

    | "--Qindex-add" :: as =>
      aux (parseArgs' as) "quirk 'index addition overflow'" Args.quirkIndexAdd λ as ↦ { as with
        quirkIndexAdd := some true
      }

    | "--Qno-index-add" :: as =>
      aux (parseArgs' as) "quirk 'index addition overflow'" Args.quirkIndexAdd λ as ↦ { as with
        quirkIndexAdd := some false
      }

    | "--Qmem-index:keep" :: as =>
      aux (parseArgs' as) "quirk 'shift'" Args.quirkMemIndex λ as ↦ { as with
        quirkMemIndex := some .Keep
      }

    | "--Qmem-index:addx" :: as =>
      aux (parseArgs' as) "quirk 'shift'" Args.quirkMemIndex λ as ↦ { as with
        quirkMemIndex := some .AddX
      }

    | "--Qmem-index:addx1" :: as =>
      aux (parseArgs' as) "quirk 'shift'" Args.quirkMemIndex λ as ↦ { as with
        quirkMemIndex := some .AddX1
      }

    | "--Qbitwise-flag" :: as =>
      aux (parseArgs' as) "quirk 'AND/OR/XOR reset VF'" Args.quirkBitwiseFlag λ as ↦ { as with
        quirkBitwiseFlag := some true
      }

    | "--Qno-bitwise-flag" :: as =>
      aux (parseArgs' as) "quirk 'AND/OR/XOR reset VF'" Args.quirkBitwiseFlag λ as ↦ { as with
        quirkBitwiseFlag := some false
      }

    | "--Qdisplay-int" :: as =>
      aux (parseArgs' as) "quirk 'display waits interrupt'" Args.quirkDisplayInt λ as ↦ { as with
        quirkDisplayInt := some true
      }

    | "--Qno-display-int" :: as =>
      aux (parseArgs' as) "quirk 'display waits interrupt'" Args.quirkDisplayInt λ as ↦ { as with
        quirkDisplayInt := some false
      }

    | "--Qget-key-rel" :: as =>
      aux (parseArgs' as) "quirk 'get key waits release'" Args.quirkGetKeyRel λ as ↦ { as with
        quirkGetKeyRel := some true
      }

    | "--Qno-get-key-rel" :: as =>
      aux (parseArgs' as) "quirk 'get key waits release'" Args.quirkGetKeyRel λ as ↦ { as with
        quirkGetKeyRel := some false
      }

    | rom :: as =>
    if rom.startsWith "-"
      then throw s!"invalid argument: {rom}"
      else aux (parseArgs' as) "rom name" Args.romName λ as ↦ { as with
        romName := some rom
      }

def parseArgs (args : List String) : IO (String × Chip8.Config) :=
  IO.ofExcept $ match parseArgs' args with
    | Except.error e => throw $ IO.userError s!"Can't parse arguments: {e}"
    | Except.ok args => do
      let romName := (← match args.romName with
        | none => throw $ IO.userError "ROM file name not specified"
        | some r => pure r
      );
      let zero: Chip8.Config := default
      pure (romName, { zero with
        instructions_per_sec := args.instructions_per_sec.getD zero.instructions_per_sec
        ramSizeS := args.ramSize.getD zero.ramSizeS
        stackSize := args.stackSize.getD zero.stackSize
        displayWidth := args.displayWidth.getD zero.displayWidth
        displayHeight := args.displayHeight.getD zero.displayHeight
        color0 := args.color0.getD zero.color0
        color1 := args.color1.getD zero.color1
        quirkJumpOffset := args.quirkJumpOffset.getD zero.quirkJumpOffset
        quirkShift := args.quirkShift.getD zero.quirkShift
        quirkIndexAdd := args.quirkIndexAdd.getD zero.quirkIndexAdd
        quirkMemIndex := args.quirkMemIndex.getD zero.quirkMemIndex
        quirkBitwiseFlag := args.quirkBitwiseFlag.getD zero.quirkBitwiseFlag
        quirkDisplayInt := args.quirkDisplayInt.getD zero.quirkDisplayInt
        quirkGetKeyRel := args.quirkGetKeyRel.getD zero.quirkGetKeyRel
      })
