import Raylib
import Chip8
import Util

open Raylib

@[extern "lean_chip8_AudioStream_setSine"]
opaque Raylib.AudioStream.setSine (stream : @& AudioStream) : BaseIO Unit

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

def main (args : List String) : IO Unit := do
  if Option.isSome $ args.find? (· == "--help") then {
    IO.println "Unhelpful"
    return
  }
  let (romName, volume, cfg) ← parseArgs args
  SetConfigFlags $ FLAG_VSYNC_HINT ||| FLAG_WINDOW_RESIZABLE
  InitWindow 640 480 "chip8 interpreter"
  InitAudioDevice
  let audioStream ← LoadAudioStream 44100 16 1
  SetMasterVolume $ Float.div (Nat.min 100 $ volume.max 0).toFloat 100.0
  PlayAudioStream audioStream
  audioStream.setSine
  SetExitKey KEY_NULL
  let cpuInterval : Float := 1 / cfg.instructions_per_sec
  let timerInterval : Float := 1 / Chip8.timerTicksPerSec
  let ramPrefix ← LoadFileData "prefix.bin"
  let rom ← LoadFileData romName
  let rnd_gen := mkStdGen $ UInt64.toNat $ ByteArray.toUInt64LE! $ ← IO.getRandomBytes 8
  if rom_fits: rom.size ≤ cfg.ramSize.toNat - Chip8.ramPrefixSize.toNat then {
    if ramPrefix_size: ramPrefix.size = Chip8.ramPrefixSize.toNat then {
      let romPadded := (ByteVector.fromArray rom).padRight rom_fits 0
      let mut chip8 := Chip8.load cfg (Subtype.mk ramPrefix ramPrefix_size) romPadded rnd_gen
      let mut timersTimer := Timer.new timerInterval
      let mut cpuTimer := Timer.new cpuInterval
      repeat do
        let deltaTime ← GetFrameTime

        -- Decrement delay and sound timers (todo: emit sound)
        (timersTimer, chip8) := timersTimer.update deltaTime chip8 (m := Id) λ chip8 ↦ do
          let chip8 := if chip8.delayTimer > 0 then { chip8 with delayTimer := chip8.delayTimer - 1 } else chip8
          if chip8.soundTimer > 0 then ({ chip8 with soundTimer := chip8.soundTimer - 1 }) else chip8

        if chip8.soundTimer > 0
          then do
            ResumeAudioStream audioStream
          else do
            PauseAudioStream audioStream

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

        chip8 := chip8.runDisplay

        if (← IsKeyPressed KEY_ENTER) && (← IsKeyDown KEY_LEFT_ALT) then {
          ToggleFullscreen
          if (← IsWindowFullscreen)
            then HideCursor
            else ShowCursor
        }

        if (← WindowShouldClose)
          then break
          else continue
    }
    else TraceLog' LOG_ERROR "Ram prefix has wrong size"
  }
  else TraceLog' LOG_ERROR "ROM too big"
  CloseAudioDevice
  CloseWindow
