def MonadExcept.check (P : Prop) [Decidable P] {ε m} [MonadExcept ε m] [Pure m] (e : ε) : m (PLift P) :=
  dite P (λ p ↦ pure (PLift.up p)) (λ _ ↦ throw e)
