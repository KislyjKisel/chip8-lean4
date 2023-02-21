import Std.Classes.LawfulMonad
import Std.Data.Array.Init.Lemmas

def ByteVector (n : Nat) := { bytes: ByteArray // bytes.size = n }

def ByteVector.replicate {n} (v : UInt8) : ByteVector n :=
  ⟨ ByteArray.mk (Array.mkArray n v), by
    show (Array.mkArray n v).size = n
    exact Array.size_mkArray _ _
  ⟩

instance : Inhabited (ByteVector n) where
  default := ByteVector.replicate 0

def ByteVector.get {n} (bs : ByteVector n) (i : Fin n) : UInt8 :=
  bs.val.get (Fin.mk i (by
    rewrite [bs.property]
    exact i.isLt
  ))

def ByteVector.set {n} (bv : ByteVector n) (i : Fin n) (val : UInt8) : ByteVector n :=
  Subtype.mk
    (bv.val.set (Fin.mk i.val (by rw [bv.property]; exact i.isLt)) val)
    ((Array.size_set bv.val.data _ val).trans bv.property)

def ByteVector.modify {n} (bv : ByteVector n) (i : Fin n) (f : UInt8 → UInt8) : ByteVector n :=
  bv.set i $ f (bv.get i)

def ByteVector.fill {n : Nat} (bs : ByteVector n) (x : UInt8) : ByteVector n :=
  Subtype.mk (ByteArray.mk $ bs.val.data.mapMono (Function.const _ x)) $ by
  show Array.size (Array.mapM (m := Id) (pure ∘ Function.const _ x) bs.val.data) = n
  apply Eq.trans
  case b =>
    exact bs.val.data.size
  case h₂ => exact bs.property
  case h₁ =>
    apply Iff.mp
    apply SatisfiesM_Id_eq (p := λ arr ↦ Array.size arr = bs.val.data.size)
    exact Array.size_mapM (m := Id) _ bs.val.data

def ByteVector.subst {n m} (h : n = m) (x : ByteVector n) : ByteVector m :=
  Subtype.mk x.val (x.property.trans h)

def ByteVector.append {n m} (x : ByteVector n) (y : ByteVector m) : ByteVector (n + m) :=
  let z := (y.val.copySlice 0 x.val n m)
  if h: z.size = n + m
    then Subtype.mk z h
    else unreachable!

def ByteVector.padRight {n m} (x : ByteVector n) (mh : n ≤ m) (val : UInt8) : ByteVector m :=
  (x.append (ByteVector.replicate (n := m - n) val)).subst (Nat.add_sub_of_le mh)

def ByteVector.fromArray (x : ByteArray) : ByteVector x.size :=
  Subtype.mk x rfl
