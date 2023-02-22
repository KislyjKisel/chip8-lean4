import Chip8.Data.UInt8

namespace Chip8

inductive Error where
  | ProgramCounterOutOfRange
  | StackOverflow
  | StackUnderflow
  | BadInstruction (code : String)
  | SpriteDataOutOfBounds
  | DecimalDigitsIndexOutOfBounds
  | KeyOutOfRange
  | MemStoreOutOfRange
  | MemLoadOutOfRange

instance : ToString Error where
  toString
    | Error.ProgramCounterOutOfRange => "Program Counter out of range"
    | Error.StackOverflow => "Stack overflow"
    | Error.StackUnderflow => "Stack underflow"
    | Error.BadInstruction code => "Bad instruction: " ++ toString code
    | Error.SpriteDataOutOfBounds => "Sprite data out of bounds"
    | Error.DecimalDigitsIndexOutOfBounds => "Decimal digit's index out of bounds"
    | Error.KeyOutOfRange => "Key out of range"
    | Error.MemStoreOutOfRange => "Attempted to store data in memory at invalid index"
    | Error.MemLoadOutOfRange => "Attempted to load data from memory at invalid index"

def badInstruction [MonadExcept Error m] (high low : UInt8) : m α :=
  throw $ Error.BadInstruction $ high.toHex ++ low.toHex

end Chip8
