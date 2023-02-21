import Raylib
import Chip8
import Timer

open Raylib

def key (k : Fin 16) : IO Bool :=
  match k with
    | ⟨ 0x0, _ ⟩ => IsKeyDown KEY_X
    | ⟨ 0x1, _ ⟩ => IsKeyDown KEY_ONE
    | ⟨ 0x2, _ ⟩ => IsKeyDown KEY_TWO
    | ⟨ 0x3, _ ⟩ => IsKeyDown KEY_THREE
    | ⟨ 0x4, _ ⟩ => IsKeyDown KEY_Q
    | ⟨ 0x5, _ ⟩ => IsKeyDown KEY_W
    | ⟨ 0x6, _ ⟩ => IsKeyDown KEY_E
    | ⟨ 0x7, _ ⟩ => IsKeyDown KEY_A
    | ⟨ 0x8, _ ⟩ => IsKeyDown KEY_S
    | ⟨ 0x9, _ ⟩ => IsKeyDown KEY_D
    | ⟨ 0xA, _ ⟩ => IsKeyDown KEY_Z
    | ⟨ 0xB, _ ⟩ => IsKeyDown KEY_C
    | ⟨ 0xC, _ ⟩ => IsKeyDown KEY_FOUR
    | ⟨ 0xD, _ ⟩ => IsKeyDown KEY_R
    | ⟨ 0xE, _ ⟩ => IsKeyDown KEY_F
    | ⟨ 0xF, _ ⟩ => IsKeyDown KEY_V
    | _ => unreachable! -- howto?

def main : IO Unit := do
  SetConfigFlags $ FLAG_VSYNC_HINT ||| FLAG_WINDOW_RESIZABLE
  InitWindow 640 480 "chip8 interpreter"
  SetExitKey KEY_NULL
  let cfg: Chip8.Config := default
  let cpuInterval : Float := 1 / cfg.instructions_per_sec
  let timerInterval : Float := 1 / Chip8.timerTicksPerSec
  let rom ← LoadFileData "IBM Logo.ch8"
  if rom_fits: rom.size ≤ cfg.ramSize.toNat - Chip8.ramPrefixSize.toNat then {
    let romPadded := (ByteVector.fromArray rom).padRight rom_fits 0
    let mut chip8 := Chip8.load cfg romPadded
    let mut timersTimer := Timer.new timerInterval
    let mut cpuTimer := Timer.new cpuInterval
    repeat do
      let deltaTime ← GetFrameTime

      -- Decrement delay and sound timers (todo: emit sound)
      (timersTimer, chip8) := timersTimer.update deltaTime chip8 (m := Id) λ chip8 ↦ do
        let chip8 := if chip8.delay_timer > 0 then { chip8 with delay_timer := chip8.delay_timer - 1 } else chip8
        if chip8.sound_timer > 0 then ({ chip8 with sound_timer := chip8.sound_timer - 1 }) else chip8

      chip8 ← chip8.setKeys key

      -- Execute an instruction for each CPU timer tick since the last frame
      (cpuTimer, chip8) ← MonadExcept.ofExcept $
        (cpuTimer.update deltaTime chip8 (m := Except Chip8.Error) Chip8.step).mapError
        (IO.userError ∘ toString)

      let (screenW, screenH) := ((← GetScreenWidth), (← GetScreenHeight))
      BeginDrawing
      ClearBackground Raylib.BLANK
      chip8.render (Rectangle.mk 0 0 screenW.toUInt64.toFloat screenH.toUInt64.toFloat)
      EndDrawing

      if (← IsKeyPressed KEY_F) && (← IsKeyDown KEY_LEFT_ALT) then {
        ToggleFullscreen
        if (← IsWindowFullscreen)
          then HideCursor
          else ShowCursor
      }

      if (← WindowShouldClose)
        then break
        else continue
  }
  else {
    IO.println "ROM too big"
  }
  CloseWindow
