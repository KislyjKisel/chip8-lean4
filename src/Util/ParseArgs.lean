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
  volume : Option Nat

deriving Inhabited

private
def aux (rest : Except String Args) (name : String) (view : Args → Option α) (set : Args → Args)
  : Except String Args := do
  let ps ← rest
  if (view ps).isSome
    then throw s!"Argument specified multiple times: {name}"
    else pure $ set ps

private
def auxOpt
  (rest : Except String Args)
  (name : String)
  (view : Args → Option α)
  (val : Option α)
  (set : α → Args → Args)
  : Except String Args := do
  match val with
    | none => throw s!"can't parse: {name}"
    | some val => aux rest name view $ set val

private
def parseColor (src : String) : Option Raylib.Color :=
  match src.toLower with
    | "lightgray" => some .lightgray
    | "gray" => some .gray
    | "darkgray" => some .darkgray
    | "yellow" => some .yellow
    | "gold" => some .gold
    | "orange" => some .orange
    | "pink" => some .pink
    | "red" => some .red
    | "maroon" => some .maroon
    | "green" => some .green
    | "lime" => some .lime
    | "darkgreen" => some .darkgreen
    | "skyblue" => some .skyblue
    | "blue" => some .blue
    | "darkblue" => some .darkblue
    | "purple" => some .purple
    | "violet" => some .violet
    | "darkpurple" => some .darkpurple
    | "beige" => some .beige
    | "brown" => some .brown
    | "darkbrown" => some .darkbrown
    | "black" => some .black
    | "magenta" => some .magenta
    | "white" => some .raywhite
    | _other => none

private
def parseArgs' (args : List String) : Except String Args :=
  match args with
    | [] => pure default

    | "--volume" :: volume :: as =>
      auxOpt (parseArgs' as) "volume" Args.volume volume.toNat?
        λ vol as ↦ { as with volume := some vol }

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
      auxOpt (parseArgs' as) "instructions per second" Args.instructions_per_sec
        (ips.toNat?.map Nat.toFloat)
        λ ips as ↦ { as with instructions_per_sec := some ips }

    | "--stack" :: stack :: as =>
      auxOpt (parseArgs' as) "stack size" Args.stackSize stack.toNat?
        λ stack as ↦ { as with stackSize := stack }

    | "--dw" :: dw :: as =>
      auxOpt (parseArgs' as) "display width" Args.displayWidth dw.toNat?
        λ dw as ↦ { as with displayWidth := dw }

    | "--dh" :: dh :: as =>
      auxOpt (parseArgs' as) "display height" Args.displayHeight dh.toNat?
        λ dh as ↦ { as with displayHeight := dh }

    | "--c0" :: c0 :: as =>
      auxOpt (parseArgs' as) "color 0" Args.color0 (parseColor c0)
        λ c0 as ↦ { as with color0 := c0 }

    | "--c1" :: c1 :: as =>
      auxOpt (parseArgs' as) "color 1" Args.color1 (parseColor c1)
        λ c1 as ↦ { as with color1 := c1 }

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

def parseArgs (args : List String) : IO (String × Nat × Chip8.Config) :=
  IO.ofExcept $ match parseArgs' args with
    | Except.error e => throw $ IO.userError s!"Can't parse arguments: {e}"
    | Except.ok args => do
      let romName := (← match args.romName with
        | none => throw $ IO.userError "ROM file name not specified"
        | some r => pure r
      );
      let volume := args.volume.getD 30
      let zero: Chip8.Config := default
      pure (romName, volume, { zero with
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
