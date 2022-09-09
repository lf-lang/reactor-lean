instance [Ord α] : LE α := leOfOrd

class InjectiveCoe (α β) extends Coe α β where
  inv      : β → Option α
  invInj   : ∀ {b₁ b₂}, (inv b₁ = inv b₂) → (b₁ = b₂) 
  coeInvId : ∀ a, inv (coe a) = a

