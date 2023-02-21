import Mathlib.Data.Fin.Basic

namespace UInt8

def width := 8
def halfWidth: UInt8 := 4
def halfSize := 16
def halfMask : UInt8 := 0b1111

def toHex (n : UInt8) :=
  hexDigitRepr (n >>> halfWidth).toNat ++ hexDigitRepr (n &&& halfMask).toNat

def firstHalf (byte : UInt8) : UInt8 :=
  (byte >>> halfWidth) &&& halfMask

def secondHalf (byte : UInt8) : UInt8 :=
  byte &&& halfMask

def secondHalfFin (byte : UInt8) : Fin halfSize :=
  Fin.mk (byte.modn halfSize).toNat $ by
    show (byte.modn halfSize).val.val < (Fin.mk (n := UInt8.size) 16 (by simp)).val
    apply (Fin.val_fin_lt (b := Fin.mk (n := UInt8.size) 16 (by simp))).mp
    show (byte.modn halfSize).val < Fin.mk (n := UInt8.size) 16 (by simp)
    apply Fin.modn_lt byte.val
    simp

def firstHalfFin (byte : UInt8) : Fin halfSize :=
  secondHalfFin $ byte >>> halfWidth

def iter (byte : UInt8) : List Bool :=
  (List.range width).map λ b ↦ decide
    (byte.toUInt32 &&& ((1 : UInt32) <<< b.toUInt32) > 0)

end UInt8
