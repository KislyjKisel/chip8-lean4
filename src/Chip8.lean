import Raylib

import Chip8.Config
import Chip8.Const
import Chip8.Control.Except
import Chip8.Data.Bool
import Chip8.Data.ByteVector
import Chip8.Data.Nat.Lemmas
import Chip8.Data.Vector
import Chip8.Error

structure Chip8 (cfg : Chip8.Config) where
  ram : ByteVector cfg.ramSize.toNat
  stack : Array UInt16
  display : ByteVector (cfg.displayWidth * cfg.displayHeight)
  gp_registers : Vector UInt8 UInt8.halfSize
  program_counter : UInt16
  index_register : UInt16
  delay_timer : UInt8
  sound_timer : UInt8
  random_gen : StdGen
  keys : Vector Bool UInt8.halfSize
deriving Inhabited

def Chip8.step {cfg} (chip8 : Chip8 cfg) : Except Error (Chip8 cfg) := do
  let pc0 := chip8.program_counter
  let pc1 := pc0 + 1
  let pc0Valid := PLift.down $
    ← MonadExcept.check (pc0 < cfg.ramSize) Error.ProgramCounterOutOfRange
  let pc1Valid := PLift.down $
    ← MonadExcept.check (pc1 < cfg.ramSize) Error.ProgramCounterOutOfRange
  let instr0 := chip8.ram.get (Fin.mk pc0.toNat pc0Valid)
  let instr1 := chip8.ram.get (Fin.mk pc1.toNat pc1Valid)
  let badInstr := badInstruction instr0 instr1
  let vfi: Fin UInt8.halfSize := Fin.mk UInt8.halfMask.toNat $ by decide
  let nibble0 := instr0 >>> UInt8.halfWidth
  -- if not (dbgTrace s!"PC: {pc0}  I: {instr0.toHex} {instr1.toHex}\nGP{chip8.gprs}" (λ _ ↦ true)) then {
  --   unreachable!
  -- }
  let chip8 := { chip8 with
    program_counter := chip8.program_counter + 2
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
                  program_counter := pc
                  stack := chip8.stack.pop
                }
              else
                throw Error.StackUnderflow

          | _ => badInstr
      }
      else badInstr

    -- [1NNN] Jump: Set `PC` to `NNN`
    | 0x1 =>
      let nibble1 := instr0 &&& 0x0F
      let addr := (nibble1.toUInt16 <<< 8) ||| instr1.toUInt16
      pure { chip8
        with program_counter := addr
      }

    -- [2NNN] Call: Set `PC` to `NNN` pushing old `PC` to stack
    | 0x2 =>
      let nibble1 := instr0 &&& 0x0F
      let addr := (nibble1.toUInt16 <<< 8) ||| instr1.toUInt16
      if chip8.stack.size < cfg.stackSize
        then pure { chip8 with
          stack := chip8.stack.push chip8.program_counter
          program_counter := addr
        }
        else throw Error.StackOverflow

    -- [3XNN] if `VX` equals `NN` then `PC := PC + 2`
    -- [4XNN] if `VX` *not* equals `NN` then `PC := PC + 2`
    | 0x3 | 0x4 => pure $
      if (chip8.gp_registers.get instr0.secondHalfFin == instr1) == (nibble0 == 0x3)
        then { chip8 with program_counter := chip8.program_counter + 2 }
        else chip8

    -- [5XY0] if `VX` equals `NN` then `PC := PC + 2`
    -- [9XY0] if `VX` *not* equals `NN` then `PC := PC + 2`
    | 0x5 | 0x9 => do
      if instr1.secondHalf == 0
        then
          let vx := chip8.gp_registers.get instr0.secondHalfFin
          let vy := chip8.gp_registers.get instr1.firstHalfFin
          pure $ if (vx == vy) == (nibble0 == 0x5)
            then { chip8 with program_counter := chip8.program_counter + 2 }
            else chip8
        else
          badInstr

    -- [6XNN] Set `VX` to `NN`
    | 0x6 =>
      let nibble1 := instr0.secondHalfFin
      pure { chip8 with
        gp_registers := chip8.gp_registers.set nibble1 instr1
      }

    -- [7XNN] Add `NN` to `VX`
    | 0x7 =>
      let nibble1 := instr0.secondHalfFin
      pure { chip8 with
        gp_registers := chip8.gp_registers.modify nibble1 (· + instr1)
      }

    -- Binary operators
    | 0x8 =>
      let vxi := instr0.secondHalfFin
      let vyi := instr1.firstHalfFin
      let vx := chip8.gp_registers.get vxi
      let vy := chip8.gp_registers.get vyi
      match instr1.secondHalf with
        -- [8XY0] Assignment: `VX := VY`
        | 0x0 => pure { chip8 with
          gp_registers := chip8.gp_registers.set vxi vy
        }

        -- [8XY1] Bitwise OR: `VX := VX ||| VY`
        | 0x1 => pure { chip8 with
          gp_registers := chip8.gp_registers.set vxi (vx ||| vy)
        }

        -- [8XY2] Bitwise AND: `VX := VX &&& VY`
        | 0x2 => pure { chip8 with
          gp_registers := chip8.gp_registers.set vxi (vx &&& vy)
        }

        -- [8XY3] Bitwise XOR: `VX := VX ^^^ VY`
        | 0x3 => pure { chip8 with
          gp_registers := chip8.gp_registers.set vxi (vx ^^^ vy)
        }

        -- [8XY4] Add: `VX := VX + VY` (affecting carry flag)
        | 0x4 =>
          pure { chip8 with
            gp_registers := (chip8.gp_registers.set vfi (decide $ 255 - vx < vy).toUInt8).set
              vxi (vx + vy)
          }

        -- -- [8XY1] Subtract: `VX` := `VX` ||| `VY`
        -- | 0x1 => pure { chip8 with
        --   gp_registers := chip8.gp_registers.set vxi (vx ||| vy)
        -- }

        -- [8XY5] Subtract: `VX := VX - VY`
        | 0x5 => pure { chip8 with
          gp_registers := (chip8.gp_registers.set vfi (decide $ vx > vy).toUInt8).set
            vxi (vx - vy)
        }

        -- [8XY7] Subtract: `VX := VY - VX`
        | 0x7 => pure { chip8 with
          gp_registers := (chip8.gp_registers.set vfi (decide $ vy > vx).toUInt8).set
            vxi (vx - vy)
        }

        -- [8XY6] Bit shift (right) (affecting carry flag)
        | 0x6 => pure $
          if cfg.quirkShift
            -- `VX := VX >>> 1`
            then { chip8 with
              gp_registers := (chip8.gp_registers.set vfi $ vx &&& 1).set
                vxi (vx >>> 1)
            }
            -- `VX := VY >>> 1`
            else { chip8 with
              gp_registers := (chip8.gp_registers.set vfi $ vy &&& 1).set
                vxi (vy >>> 1)
            }

        -- [8XYE] Bit shift (left) (affecting carry flag)
        | 0xE => pure $
          if cfg.quirkShift
            -- `VX := VX <<< 1`
            then { chip8 with
              gp_registers := (chip8.gp_registers.set vfi $ (vx &&& 128) >>> 7).set
                vxi (vx <<< 1)
            }
            -- `VX := VY <<< 1`
            else { chip8 with
              gp_registers := (chip8.gp_registers.set vfi $ (vy &&& 128) >>> 7).set
                vxi (vy <<< 1)
            }

        | _ => badInstr


    -- [ANNN] Set `I` to `NNN`
    | 0xA =>
      let nibble1 := instr0 &&& 0x0F
      let addr := (nibble1.toUInt16 <<< 8) ||| instr1.toUInt16
      pure { chip8 with index_register := addr }

    -- [BNNN] Jump with offset
    | 0xB =>
      let addr := (instr0.secondHalf.toUInt16 <<< 8) ||| instr1.toUInt16
      pure { chip8 with
        program_counter := if cfg.quirkJumpOffset
          -- Set `PC` to `NNN` + `VX`
          then addr + (chip8.gp_registers.get instr0.secondHalfFin).toUInt16
          -- Set `PC` to `NNN` + `V0`
          else addr + (chip8.gp_registers.get (Fin.mk 0 (by decide))).toUInt16
      }

    -- [CXNN] Random `VX := (← random) &&& NN`
    | 0xC =>
      let vxi := instr0.secondHalfFin
      let (value, rnd_gen) := RandomGen.next chip8.random_gen
      pure { chip8 with
        gp_registers := chip8.gp_registers.set vxi (value.toUInt8 &&& instr1)
        random_gen := rnd_gen
      }

    -- [DXYN] Display at (`VX`, `VY`) the sprite at in ram at `I`, `N` bytes high
    | 0xD => do
      let nibble1 := instr0.secondHalfFin
      let nibble2 := instr1.firstHalfFin
      let x0 := (chip8.gp_registers.get nibble1).toNat % cfg.displayWidth
      let y0 := (chip8.gp_registers.get nibble2).toNat % cfg.displayHeight
      let nibble3 := (instr1 &&& 0x0F).toUInt16
      let idx0 := chip8.index_register
      let idx1 := chip8.index_register + nibble3
      let _ := ← MonadExcept.check (idx0 < cfg.ramSize) Error.SpriteDataOutOfBounds
      let idx1Valid := (← MonadExcept.check (idx1 ≤ cfg.ramSize) Error.SpriteDataOutOfBounds).down
      let mut display := chip8.display
      for ih: i in [idx0.toNat : idx1.toNat] do
        let y := y0 + i - idx0.toNat
        if yh: y < cfg.displayHeight then do
          let spriteRow := chip8.ram.get (Fin.mk i (Nat.le_trans ih.upper idx1Valid))
          for sxh: spriteX in [: UInt8.width] do
            let x := x0 + spriteX
            if xh: x < cfg.displayWidth then {
              let shift: UInt8 := 7 - (UInt8.mk $ Fin.mk spriteX $ sxh.upper.trans (by decide));
              let spriteBit: UInt8 := AndOp.and 1 $ spriteRow >>> shift;
              display := display.modify
                (Fin.mk (y * cfg.displayWidth + x) (Nat.matrixLinearIndex_bound yh xh))
                (Xor.xor spriteBit)
            }
            else break
        else break
      return { chip8 with display := display }

    -- | 0xE => match instr1 with
    --   -- [EX9E] if key `VX` is pressed then `PC := PC + 2`
    --   -- [EXA1] if key `VX` is *not* pressed then `PC := PC + 2`
    --   | 0x9E | 0xA1 =>
    --     let vx := chip8.gp_registers.get instr0.secondHalfFin
    --     if h: vx.toNat < UInt8.halfSize
    --       then pure $ if chip8.keys.get (Fin.mk vx.toNat h) == (instr1 == 0x9E)
    --         then { chip8 with program_counter := chip8.program_counter + 2 }
    --         else chip8
    --       else throw Error.KeyOutOfRange

    --   | _ => badInstr

    -- | 0xF => match instr1 with
    --   -- [FX07] Set `VX` to `DT`
    --   | 0x07 => pure { chip8 with
    --     gp_registers := chip8.gp_registers.set instr0.secondHalfFin chip8.delay_timer
    --   }

    --   -- [FX15] Set `DT` to `VX`
    --   | 0x15 => pure { chip8 with
    --     delay_timer := chip8.gp_registers.get instr0.secondHalfFin
    --   }

    --   -- [FX18] Set `ST` to `VX`
    --   | 0x18 => pure { chip8 with
    --     sound_timer := chip8.gp_registers.get instr0.secondHalfFin
    --   }

    --   -- [FX1E] `I := I + VX`
    --   | 0x1E =>
    --     let i': UInt16 := chip8.index_register + (chip8.gp_registers.get instr0.secondHalfFin).toUInt16
    --     pure $ if cfg.quirkIndexAdd && i' ≥ 0x1000
    --       then { chip8 with index_register := i', gp_registers := chip8.gp_registers.set vfi 1 }
    --       else { chip8 with index_register := i' }

    --   -- [FX0A] Wait for key input, then write pressed key index to `VX`
    --   | 0x0A => pure $
    --     match chip8.keys.indexOf? true with
    --       | some k => { chip8 with
    --         gp_registers := chip8.gp_registers.set instr0.secondHalfFin $ 
    --           UInt8.mk $ Fin.mk k.val $ k.isLt.trans $ by decide
    --       }
    --       | none => { chip8 with program_counter := pc0 }

    --   -- [FX33] Store decimal digits of `VX` in (big endian) `[I]`, `[I+1]`, `[I+2]`.
    --   | 0x33 =>
    --     let i0 := chip8.index_register
    --     let i1 := i0 + 1
    --     let i2 := i0 + 2
    --     let i0h := (← MonadExcept.check (i0 < cfg.ramSize) Error.DecimalDigitsIndexOutOfBounds).down
    --     let i1h := (← MonadExcept.check (i1 < cfg.ramSize) Error.DecimalDigitsIndexOutOfBounds).down
    --     let i2h := (← MonadExcept.check (i2 < cfg.ramSize) Error.DecimalDigitsIndexOutOfBounds).down
    --     let vx := chip8.gp_registers.get instr0.secondHalfFin
    --     pure { chip8 with
    --       ram := chip8.ram
    --         |> λ ram ↦ .set ram (Fin.mk i0.val i0h) (vx / 100)
    --         |> λ ram ↦ .set ram (Fin.mk i1.val i1h) (vx / 10 % 10)
    --         |> λ ram ↦ .set ram (Fin.mk i2.val i2h) (vx % 10)
    --     }

    --   | 0x55 =>
    --     panic! "not implemented" -- TODO

    --   | 0x56 =>
    --     panic! "not implemented" -- TODO

    --  | _ => badInstr

    | _ => badInstr

def Chip8.render {cfg} (chip8 : Chip8 cfg) (rect : Raylib.Rectangle) : BaseIO Unit := do
  let cellW := rect.width / cfg.displayWidth.toFloat
  let cellH := rect.height / cfg.displayHeight.toFloat
  for ih: i in [: cfg.displayHeight] do
    let y := i.toFloat * cellH
    let row_idx0 := i * cfg.displayWidth
    for jh: j in [: cfg.displayWidth] do
      let x := j.toFloat * cellW
      let idx := row_idx0 + j
      let displayByte := chip8.display.get (Fin.mk idx $ Nat.matrixLinearIndex_bound ih.upper jh.upper)
      let color := if displayByte > 0 then cfg.color1 else cfg.color0
      Raylib.DrawRectangleV (Raylib.Vector2.mk x y) (Raylib.Vector2.mk cellW cellH) color

def Chip8.load (cfg : Config) (rom : ByteVector (cfg.ramSize.toNat - ramPrefixSize.toNat)) : Chip8 cfg :=
  let zeroed: Chip8 cfg := default
  { zeroed with
    ram := ((ByteVector.replicate (n := ramPrefixSize.toNat) 0).append rom).subst $ Nat.add_sub_of_le cfg.ramSize_prefix
    program_counter := ramPrefixSize
  }

-- todo: loop :)
def Chip8.setKeys {cfg} [Monad m] (chip8 : Chip8 cfg) (f : Fin UInt8.halfSize → m Bool) : m (Chip8 cfg) := do
  let aux ks i := f i >>= λ v ↦ pure $ Vector.set ks i v
  let mut keys := Vector.replicate false
  keys ← aux keys $ Fin.mk 0 $ by decide
  keys ← aux keys $ Fin.mk 1 $ by decide
  keys ← aux keys $ Fin.mk 2 $ by decide
  keys ← aux keys $ Fin.mk 3 $ by decide
  keys ← aux keys $ Fin.mk 4 $ by decide
  keys ← aux keys $ Fin.mk 5 $ by decide
  keys ← aux keys $ Fin.mk 6 $ by decide
  keys ← aux keys $ Fin.mk 7 $ by decide
  keys ← aux keys $ Fin.mk 8 $ by decide
  keys ← aux keys $ Fin.mk 9 $ by decide
  keys ← aux keys $ Fin.mk 10 $ by decide
  keys ← aux keys $ Fin.mk 11 $ by decide
  keys ← aux keys $ Fin.mk 12 $ by decide
  keys ← aux keys $ Fin.mk 13 $ by decide
  keys ← aux keys $ Fin.mk 14 $ by decide
  keys ← aux keys $ Fin.mk 15 $ by decide
  return { chip8 with keys }
