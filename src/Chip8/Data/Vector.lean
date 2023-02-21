def Vector α (n : Nat) := { array: Array α // array.size = n }

def Vector.replicate {n} (v : α) : Vector α n :=
  Subtype.mk (Array.mkArray n v) (Array.size_mkArray n v)

def Vector.set {n} (vec : Vector α n) (i : Fin n) (v : α) : Vector α n :=
  Subtype.mk
    (vec.val.set (Fin.mk i.val (by rw [vec.property]; exact i.isLt)) v)
    ((Array.size_set vec.val _ v).trans vec.property)

def Vector.get {n} (vec : Vector α n) (i : Fin n) : α :=
  vec.val.get (Fin.mk i.val (Eq.subst (Eq.symm vec.property) i.isLt))

def Vector.modify {n} (vec : Vector α n) (i : Fin n) (f : α → α) : Vector α n :=
  vec.set i $ f (vec.get i)

instance [Inhabited α] : Inhabited (Vector α n) where
  default := Vector.replicate default

def Vector.indexOf? [BEq α] (vec : Vector α n) (x : α) : Option (Fin n) :=
  (vec.val.indexOf? x).map λ i ↦ Fin.mk i.val (Nat.lt_of_lt_of_eq i.isLt vec.property)
