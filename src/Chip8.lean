import Raylib

import Chip8.Config
import Chip8.Const
import Chip8.Control.Except
import Chip8.Data.Bool
import Chip8.Data.ByteVector
import Chip8.Data.Nat.Lemmas
import Chip8.Data.Vector
import Chip8.Error

namespace Chip8

structure DisplayCall (cfg : Config) where
  x0 : Nat
  y0 : Nat
  idx0 : UInt16
  idx1 : UInt16
  idx1Valid : idx1 ≤ cfg.ramSize

end Chip8

structure Chip8 (cfg : Chip8.Config) where
  ram : ByteVector cfg.ramSize.toNat
  stack : Array UInt16
  display : ByteVector (cfg.displayWidth * cfg.displayHeight)
  gpRegisters : Vector UInt8 UInt8.halfSize
  programCounter : UInt16
  indexRegister : UInt16
  delayTimer : UInt8
  soundTimer : UInt8
  randomGenerator : StdGen
  keyboardState : Vector Bool UInt8.halfSize
  displayCall : Option $ Chip8.DisplayCall cfg
  awaitedKey : Option (Fin UInt8.halfSize)
deriving Inhabited

def Chip8.runDisplay {cfg} (chip8 : Chip8 cfg) : Chip8 cfg := Id.run $ do
  if let some dc := chip8.displayCall then do
    let mut display := chip8.display;
    let mut vf: UInt8 := 0
    for ih: i in [dc.idx0.toNat : dc.idx1.toNat] do
      let y := dc.y0 + i - dc.idx0.toNat
      if yh: y < cfg.displayHeight then do
        let spriteRow := chip8.ram.get (Fin.mk i (Nat.le_trans ih.upper dc.idx1Valid))
        for sxh: spriteX in [: UInt8.width] do
          let x := dc.x0 + spriteX
          if xh: x < cfg.displayWidth then {
            let shift: UInt8 := 7 - (UInt8.mk $ Fin.mk spriteX $ sxh.upper.trans (by decide));
            let spriteBit: UInt8 := AndOp.and 1 $ spriteRow >>> shift;
            let di := (Fin.mk (y * cfg.displayWidth + x) (Nat.matrixLinearIndex_bound yh xh))
            let displayBit: UInt8 := display.get di
            if spriteBit = 1 && displayBit = 1 then {
              vf := 1
            }
            display := display.set di (Xor.xor spriteBit displayBit)
          }
          else break
      else break
    pure { chip8 with
      display := display
      gpRegisters := chip8.gpRegisters.set (Fin.mk 0xF $ by decide) vf
      displayCall := none
    }
  else
    pure chip8

def Chip8.awaitKey {cfg} (chip8 : Chip8 cfg) : Option $ Chip8 cfg := do
  if cfg.quirkGetKeyRel
    then
      if let some awkey := chip8.awaitedKey
        then
          if chip8.keyboardState.get awkey
            then none
            else some { chip8 with awaitedKey := none }
        else some chip8
    else some chip8

def Chip8.step {cfg} (chip8 : Chip8 cfg) : Except Error (Chip8 cfg) := do
  if chip8.displayCall.isSome then return chip8;
  if let some chip8 := chip8.awaitKey then {
    let pc0 := chip8.programCounter
    let pc1 := pc0 + 1
    let pc0Valid := PLift.down $
      ← MonadExcept.check (pc0 < cfg.ramSize) Error.ProgramCounterOutOfRange
    let pc1Valid := PLift.down $
      ← MonadExcept.check (pc1 < cfg.ramSize) Error.ProgramCounterOutOfRange
    let instr0 := chip8.ram.get (Fin.mk pc0.toNat pc0Valid)
    let instr1 := chip8.ram.get (Fin.mk pc1.toNat pc1Valid)
    let badInstr := badInstruction instr0 instr1
    let vfi: Fin UInt8.halfSize := Fin.mk UInt8.halfMask.toNat $ by decide
    let nibble0 := instr0.firstHalf
    -- if (dbgTrace s!"PC: {pc0}  I: {instr0.toHex} {instr1.toHex}" (λ _ ↦ false))
    --   then unreachable!;
    let chip8 := { chip8 with
      programCounter := chip8.programCounter + 2
    }
    match nibble0 with
      | 0x0 =>
        if instr0 = 0 then do {
          match instr1 with
            -- [00E0] Clear screen
            | 0xE0 => return { chip8 with
                display := chip8.display.fill 0
              }

            -- [00EE] Return
            | 0xEE =>
              if stackNonEmpty: chip8.stack.size ≠ 0
                then
                  let pc := chip8.stack.get $
                    Fin.mk chip8.stack.size.pred (Nat.pred_lt stackNonEmpty)
                  pure { chip8 with
                    programCounter := pc
                    stack := chip8.stack.pop
                  }
                else
                  throw Error.StackUnderflow

            | 0xFD =>
              if cfg.extExit
                then throw Error.Exit
                else badInstr

            | _ => badInstr
        }
        else badInstr

      -- [1NNN] Jump: Set `PC` to `NNN`
      | 0x1 =>
        let nibble1 := instr0 &&& 0x0F
        let addr := (nibble1.toUInt16 <<< 8) ||| instr1.toUInt16
        pure { chip8
          with programCounter := addr
        }

      -- [2NNN] Call: Set `PC` to `NNN` pushing old `PC` to stack
      | 0x2 =>
        let nibble1 := instr0 &&& 0x0F
        let addr := (nibble1.toUInt16 <<< 8) ||| instr1.toUInt16
        if chip8.stack.size < cfg.stackSize
          then pure { chip8 with
            stack := chip8.stack.push chip8.programCounter
            programCounter := addr
          }
          else throw Error.StackOverflow

      -- [3XNN] if `VX` equals `NN` then `PC := PC + 2`
      -- [4XNN] if `VX` *not* equals `NN` then `PC := PC + 2`
      | 0x3 | 0x4 => pure $
        if (chip8.gpRegisters.get instr0.secondHalfFin == instr1) == (nibble0 == 0x3)
          then { chip8 with programCounter := chip8.programCounter + 2 }
          else chip8

      -- [5XY0] if `VX` equals `NN` then `PC := PC + 2`
      -- [9XY0] if `VX` *not* equals `NN` then `PC := PC + 2`
      | 0x5 | 0x9 => do
        if instr1.secondHalf == 0
          then
            let vx := chip8.gpRegisters.get instr0.secondHalfFin
            let vy := chip8.gpRegisters.get instr1.firstHalfFin
            pure $ if (vx == vy) == (nibble0 == 0x5)
              then { chip8 with programCounter := chip8.programCounter + 2 }
              else chip8
          else
            badInstr

      -- [6XNN] Set `VX` to `NN`
      | 0x6 =>
        let nibble1 := instr0.secondHalfFin
        pure { chip8 with
          gpRegisters := chip8.gpRegisters.set nibble1 instr1
        }

      -- [7XNN] Add `NN` to `VX`
      | 0x7 =>
        let nibble1 := instr0.secondHalfFin
        pure { chip8 with
          gpRegisters := chip8.gpRegisters.modify nibble1 (· + instr1)
        }

      -- Binary operators
      | 0x8 =>
        let vxi := instr0.secondHalfFin
        let vyi := instr1.firstHalfFin
        let vx := chip8.gpRegisters.get vxi
        let vy := chip8.gpRegisters.get vyi
        match instr1.secondHalf with
          -- [8XY0] Assignment: `VX := VY`
          | 0x0 => pure { chip8 with
            gpRegisters := chip8.gpRegisters.set vxi vy
          }

          -- [8XY1] Bitwise OR: `VX := VX ||| VY`
          | 0x1 =>
            let gpRegisters := chip8.gpRegisters.set vxi (vx ||| vy)
            pure $ if cfg.quirkBitwiseFlag
              then { chip8 with gpRegisters := gpRegisters.set vfi 0 }
              else { chip8 with gpRegisters }

          -- [8XY2] Bitwise AND: `VX := VX &&& VY`
          | 0x2 =>
            let gpRegisters := chip8.gpRegisters.set vxi (vx &&& vy)
            pure $ if cfg.quirkBitwiseFlag
              then { chip8 with gpRegisters := gpRegisters.set vfi 0 }
              else { chip8 with gpRegisters }

          -- [8XY3] Bitwise XOR: `VX := VX ^^^ VY`
          | 0x3 =>
            let gpRegisters := chip8.gpRegisters.set vxi (vx ^^^ vy)
            pure $ if cfg.quirkBitwiseFlag
              then { chip8 with gpRegisters := gpRegisters.set vfi 0 }
              else { chip8 with gpRegisters }

          -- [8XY4] Add: `VX := VX + VY` (affecting carry flag)
          | 0x4 =>
            pure { chip8 with
              gpRegisters := (chip8.gpRegisters.set vxi (vx + vy)).set
                vfi (decide $ 255 - vx < vy).toUInt8
            }

          -- [8XY5] Subtract: `VX := VX - VY`
          | 0x5 => pure { chip8 with
            gpRegisters := (chip8.gpRegisters.set vxi (vx - vy)).set
              vfi (decide $ vx > vy).toUInt8
          }

          -- [8XY7] Subtract: `VX := VY - VX`
          | 0x7 => pure { chip8 with
            gpRegisters := (chip8.gpRegisters.set vxi (vy - vx)).set
              vfi (decide $ vy > vx).toUInt8
          }

          -- [8XY6] Bit shift (right) (affecting carry flag)
          | 0x6 => pure $
            if cfg.quirkShift
              -- `VX := VX >>> 1`
              then { chip8 with
                gpRegisters := (chip8.gpRegisters.set vxi $ vx >>> 1).set
                  vfi (vx &&& 1)
              }
              -- `VX := VY >>> 1`
              else { chip8 with
                gpRegisters := (chip8.gpRegisters.set vxi $ vy >>> 1).set
                  vfi (vy &&& 1)
              }

          -- [8XYE] Bit shift (left) (affecting carry flag)
          | 0xE => pure $
            if cfg.quirkShift
              -- `VX := VX <<< 1`
              then { chip8 with
                gpRegisters := (chip8.gpRegisters.set vxi $ vx <<< 1).set
                  vfi (vx >>> 7)
              }
              -- `VX := VY <<< 1`
              else { chip8 with
                gpRegisters := (chip8.gpRegisters.set vxi $ vy <<< 1).set
                  vfi (vx >>> 7)
              }

          | _ => badInstr


      -- [ANNN] Set `I` to `NNN`
      | 0xA =>
        let nibble1 := instr0 &&& 0x0F
        let addr := (nibble1.toUInt16 <<< 8) ||| instr1.toUInt16
        pure { chip8 with indexRegister := addr }

      -- [BNNN] Jump with offset
      | 0xB =>
        let addr := (instr0.secondHalf.toUInt16 <<< 8) ||| instr1.toUInt16
        pure { chip8 with
          programCounter := if cfg.quirkJumpOffset
            -- Set `PC` to `NNN` + `VX`
            then addr + (chip8.gpRegisters.get instr0.secondHalfFin).toUInt16
            -- Set `PC` to `NNN` + `V0`
            else addr + (chip8.gpRegisters.get (Fin.mk 0 (by decide))).toUInt16
        }

      -- [CXNN] Random `VX := (← random) &&& NN`
      | 0xC =>
        let vxi := instr0.secondHalfFin
        let (value, rnd_gen) := RandomGen.next chip8.randomGenerator
        pure { chip8 with
          gpRegisters := chip8.gpRegisters.set vxi (value.toUInt8 &&& instr1)
          randomGenerator := rnd_gen
        }

      -- [DXYN] Display at (`VX`, `VY`) the sprite at in ram at `I`, `N` bytes high
      | 0xD => do
        let nibble1 := instr0.secondHalfFin
        let nibble2 := instr1.firstHalfFin
        let x0 := (chip8.gpRegisters.get nibble1).toNat % cfg.displayWidth
        let y0 := (chip8.gpRegisters.get nibble2).toNat % cfg.displayHeight
        let nibble3 := instr1.secondHalf.toUInt16
        let idx0 := chip8.indexRegister
        let idx1 := chip8.indexRegister + nibble3
        let _ := ← MonadExcept.check (idx0 < cfg.ramSize) Error.SpriteDataOutOfBounds
        let idx1Valid := (← MonadExcept.check (idx1 ≤ cfg.ramSize) Error.SpriteDataOutOfBounds).down
        let chip8 := { chip8 with
          displayCall := some { x0, y0, idx0, idx1, idx1Valid }
        }
        pure $ if cfg.quirkDisplayInt
          then chip8
          else chip8.runDisplay

      | 0xE => match instr1 with
        -- [EX9E] if key `VX` is pressed then `PC := PC + 2`
        -- [EXA1] if key `VX` is *not* pressed then `PC := PC + 2`
        | 0x9E | 0xA1 =>
          let vx := chip8.gpRegisters.get instr0.secondHalfFin
          if h: vx.toNat < UInt8.halfSize
            then pure $ if chip8.keyboardState.get (Fin.mk vx.toNat h) == (instr1 == 0x9E)
              then { chip8 with programCounter := chip8.programCounter + 2 }
              else chip8
            else throw Error.KeyOutOfRange

        | _ => badInstr

      | 0xF => match instr1 with
        -- [FX07] Set `VX` to `DT`
        | 0x07 => pure { chip8 with
          gpRegisters := chip8.gpRegisters.set instr0.secondHalfFin chip8.delayTimer
        }

        -- [FX15] Set `DT` to `VX`
        | 0x15 => pure { chip8 with
          delayTimer := chip8.gpRegisters.get instr0.secondHalfFin
        }

        -- [FX18] Set `ST` to `VX`
        | 0x18 => pure { chip8 with
          soundTimer := chip8.gpRegisters.get instr0.secondHalfFin
        }

        -- [FX1E] `I := I + VX`
        | 0x1E =>
          let i': UInt16 := chip8.indexRegister + (chip8.gpRegisters.get instr0.secondHalfFin).toUInt16
          pure $ if cfg.quirkIndexAdd && i' ≥ 0x1000
            then { chip8 with indexRegister := i', gpRegisters := chip8.gpRegisters.set vfi 1 }
            else { chip8 with indexRegister := i' }

        -- [FX0A] Wait for key input, then write pressed key index to `VX`
        | 0x0A => pure $
          match chip8.keyboardState.indexOf? true with
            | some k => { chip8 with
              awaitedKey := some k
              gpRegisters := chip8.gpRegisters.set instr0.secondHalfFin $ 
                UInt8.mk $ Fin.mk k.val $ k.isLt.trans $ by decide
            }
            | none => { chip8 with programCounter := pc0 }

        -- [FX29] Store builtin font char ram offset in `I`
        | 0x29 =>
          pure { chip8 with
            indexRegister := fontOffset + (chip8.gpRegisters.get instr0.secondHalfFin).secondHalf.toUInt16 * fontSize
          }

        -- [FX33] Store decimal digits of `VX` in (big endian) `[I]`, `[I+1]`, `[I+2]`.
        | 0x33 =>
          let i0 := chip8.indexRegister
          let i1 := i0 + 1
          let i2 := i0 + 2
          let i0h := (← MonadExcept.check (i0 < cfg.ramSize) Error.DecimalDigitsIndexOutOfBounds).down
          let i1h := (← MonadExcept.check (i1 < cfg.ramSize) Error.DecimalDigitsIndexOutOfBounds).down
          let i2h := (← MonadExcept.check (i2 < cfg.ramSize) Error.DecimalDigitsIndexOutOfBounds).down
          let vx := chip8.gpRegisters.get instr0.secondHalfFin
          pure { chip8 with
            ram := chip8.ram
              |> λ ram ↦ .set ram (Fin.mk i0.val i0h) (vx / 100)
              |> λ ram ↦ .set ram (Fin.mk i1.val i1h) (vx / 10 % 10)
              |> λ ram ↦ .set ram (Fin.mk i2.val i2h) (vx % 10)
          }

        -- [FX55] Store: for i ∈ 0..X do `[I+i] := Vi`
        | 0x55 =>
          let mut ram := chip8.ram
          let vxi := instr0.secondHalfFin
          for vih: vi in [: vxi.val.succ] do
            let i := chip8.indexRegister + vi.toUInt16
            let ih := (← MonadExcept.check (i < cfg.ramSize) Error.MemStoreOutOfRange).down
            let vi' := Fin.mk vi (vih.upper.trans_le $ Nat.succ_le_of_lt vxi.isLt)
            ram := ram.set (Fin.mk i.toNat ih) $ chip8.gpRegisters.get vi'
          pure { chip8 with
            ram
            indexRegister := match cfg.quirkMemIndex with
              | QuirkMemIndex.Keep => chip8.indexRegister
              | QuirkMemIndex.AddX => chip8.indexRegister + instr0.secondHalf.toUInt16
              | QuirkMemIndex.AddX1 => chip8.indexRegister + instr0.secondHalf.toUInt16 + 1
          }

        -- [FX65] Load: for i ∈ 0..X do `Vi := [I+i]`
        | 0x65 =>
          let mut gpRegisters := chip8.gpRegisters
          let vxi := instr0.secondHalfFin
          for vih: vi in [: vxi.val.succ] do
            let i := chip8.indexRegister + vi.toUInt16
            let ih := (← MonadExcept.check (i < cfg.ramSize) Error.MemStoreOutOfRange).down
            let vi' := Fin.mk vi (vih.upper.trans_le $ Nat.succ_le_of_lt vxi.isLt)
            gpRegisters := gpRegisters.set vi' (chip8.ram.get (Fin.mk i.toNat ih))
          pure { chip8 with
            gpRegisters
            indexRegister := match cfg.quirkMemIndex with
              | QuirkMemIndex.Keep => chip8.indexRegister
              | QuirkMemIndex.AddX => chip8.indexRegister + instr0.secondHalf.toUInt16
              | QuirkMemIndex.AddX1 => chip8.indexRegister + instr0.secondHalf.toUInt16 + 1
          }

        | _ => badInstr

      | _ => badInstr
  }
  else pure chip8

def Chip8.render {cfg} (chip8 : Chip8 cfg) (rect : Raylib.Rectangle) : BaseIO Unit := do
  let cellW := rect.width / cfg.displayWidth.toFloat.toFloat32
  let cellH := rect.height / cfg.displayHeight.toFloat.toFloat32
  for ih: i in [: cfg.displayHeight] do
    let y := i.toFloat.toFloat32 * cellH
    let row_idx0 := i * cfg.displayWidth
    for jh: j in [: cfg.displayWidth] do
      let x := j.toFloat.toFloat32 * cellW
      let idx := row_idx0 + j
      let displayByte := chip8.display.get (Fin.mk idx $ Nat.matrixLinearIndex_bound ih.upper jh.upper)
      let color := if displayByte > 0 then cfg.color1 else cfg.color0
      Raylib.drawRectangleV (Raymath.Vector2.mk x y) (Raymath.Vector2.mk cellW cellH) color

def Chip8.load (cfg : Config) (pre : ByteVector ramPrefixSize.toNat) (rom : ByteVector (cfg.ramSize.toNat - ramPrefixSize.toNat)) (rndg : StdGen) : Chip8 cfg :=
  let zeroed: Chip8 cfg := default
  { zeroed with
    ram := (pre.append rom).subst $ Nat.add_sub_of_le cfg.ramSize_prefix
    programCounter := ramPrefixSize
    randomGenerator := rndg
  }

def Chip8.setKeys {cfg} [Monad m] (chip8 : Chip8 cfg) (isPressed : Fin UInt8.halfSize → m Bool) : m (Chip8 cfg) := do
  let mut keyboardState := Vector.replicate false
  for h: i in [: 16] do
    let key := Fin.mk i $ h.upper
    keyboardState := keyboardState.set key (← isPressed key)
  return { chip8 with keyboardState }
