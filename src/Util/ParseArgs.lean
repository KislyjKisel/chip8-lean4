import Chip8.Const
import Chip8.Config

private
structure Args where
  ramSize : Option $ Σ (ramSize : UInt16), PLift $ Chip8.ramPrefixSize ≤ ramSize
  romName : Option String
deriving Inhabited

private
def aux (rest : Except String Args) (name : String) (view : Args → Option α) (set : Args → Args)
  : Except String Args := do
  let ps ← rest
  if (view ps).isSome
    then throw s!"Argument specified multiple times: {name}"
    else pure $ set ps

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
      | none => throw "ram size has bad format"

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
        ramSizeS := args.ramSize.getD zero.ramSizeS
      })
