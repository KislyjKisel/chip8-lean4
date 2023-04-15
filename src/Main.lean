import Raylib
import Chip8
import Util

open Raylib

@[extern "lean_chip8_AudioStream_setSine"]
opaque Raylib.AudioStream.setSine (stream : @& AudioStream) : BaseIO Unit

def key (k : Fin 16) : IO Bool :=
  isKeyDown $ match k with
    | ⟨ 0x0, _ ⟩ => .x
    | ⟨ 0x1, _ ⟩ => .one
    | ⟨ 0x2, _ ⟩ => .two
    | ⟨ 0x3, _ ⟩ => .three
    | ⟨ 0x4, _ ⟩ => .q
    | ⟨ 0x5, _ ⟩ => .w
    | ⟨ 0x6, _ ⟩ => .e
    | ⟨ 0x7, _ ⟩ => .a
    | ⟨ 0x8, _ ⟩ => .s
    | ⟨ 0x9, _ ⟩ => .d
    | ⟨ 0xA, _ ⟩ => .z
    | ⟨ 0xB, _ ⟩ => .c
    | ⟨ 0xC, _ ⟩ => .four
    | ⟨ 0xD, _ ⟩ => .r
    | ⟨ 0xE, _ ⟩ => .f
    | ⟨ 0xF, _ ⟩ => .v
    | ⟨ n+0x10, h ⟩ => False.elim $ Nat.not_le_of_gt h $ Nat.le_add_left 16 n

def main (args : List String) : IO Unit := do
  if Option.isSome $ args.find? (· == "--help") then {
    IO.println "Unhelpful"
    return
  }
  let (romName, volume, cfg) ← parseArgs args
  setConfigFlags $ .vsyncHint ||| .windowResizable
  initWindow 640 480 "chip8 interpreter"
  initAudioDevice
  let audioStream ← loadAudioStream 44100 16 1
  setMasterVolume $ ((Nat.min 100 $ volume.max 0).toFloat / 100.0).toFloat32
  playAudioStream audioStream
  audioStream.setSine
  setExitKey .null
  let cpuInterval : Float := 1 / cfg.instructions_per_sec
  let timerInterval : Float := 1 / Chip8.timerTicksPerSec
  let ramPrefix ← loadFileData "prefix.bin"
  let rom ← loadFileData romName
  let rnd_gen := mkStdGen $ UInt64.toNat $ ByteArray.toUInt64LE! $ ← IO.getRandomBytes 8
  if rom_fits: rom.size ≤ cfg.ramSize.toNat - Chip8.ramPrefixSize.toNat then {
    if ramPrefix_size: ramPrefix.size = Chip8.ramPrefixSize.toNat then {
      let romPadded := (ByteVector.fromArray rom).padRight rom_fits 0
      let mut chip8 := Chip8.load cfg (Subtype.mk ramPrefix ramPrefix_size) romPadded rnd_gen
      let mut timersTimer := Timer.new timerInterval
      let mut cpuTimer := Timer.new cpuInterval
      repeat do
        let deltaTime := (← getFrameTime).toFloat

        -- Decrement delay and sound timers (todo: emit sound)
        (timersTimer, chip8) := timersTimer.update deltaTime chip8 (m := Id) λ chip8 ↦ do
          let chip8 := if chip8.delayTimer > 0 then { chip8 with delayTimer := chip8.delayTimer - 1 } else chip8
          if chip8.soundTimer > 0 then ({ chip8 with soundTimer := chip8.soundTimer - 1 }) else chip8

        if chip8.soundTimer > 0
          then do
            resumeAudioStream audioStream
          else do
            pauseAudioStream audioStream

        chip8 ← chip8.setKeys key

        -- Execute an instruction for each CPU timer tick since the last frame
        (cpuTimer, chip8) ← MonadExcept.ofExcept $
          (cpuTimer.update deltaTime chip8 (m := Except Chip8.Error) Chip8.step).mapError
          (IO.userError ∘ toString)

        let (screenW, screenH) := ((← getScreenWidth), (← getScreenHeight))
        beginDrawing
        clearBackground .blank
        chip8.render (Rectangle.mk 0 0 screenW.toFloat32 screenH.toFloat32)
        endDrawing

        chip8 := chip8.runDisplay

        if (← isKeyPressed .enter) && (← isKeyDown .leftAlt) then {
          toggleFullscreen
          if (← isWindowFullscreen)
            then hideCursor
            else showCursor
        }

        if (← windowShouldClose)
          then break
          else continue
    }
    else traceLog' .error "Ram prefix has wrong size"
  }
  else traceLog' .error "ROM too big"
  closeAudioDevice
  closeWindow
