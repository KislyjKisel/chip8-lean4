theorem Nat.matrixLinearIndex_bound {i j w h : Nat} (ih : i < h) (jh : j < w) : i * w + j < w * h := by
  apply Nat.le_trans (m := i * w + w)
  · apply Nat.add_lt_add_left
    assumption
  · conv =>
      lhs
      rhs
      rw [← Nat.one_mul w]
    show i * w + 1 * w ≤ w * h
    rw [← Nat.right_distrib, Nat.mul_comm, Nat.add_one]
    apply Nat.mul_le_mul_left w
    assumption
