class InjectiveCoe (α β) extends Coe α β where
  inv      : β → Option α
  invInj   : ∀ {b₁ b₂}, (inv b₁ = inv b₂) → (b₁ = b₂) 
  coeInvId : ∀ a, inv (coe a) = a

instance [Ord α] : LE α := leOfOrd

instance : DecidableEq Empty :=
  fun empty _ => empty.rec

@[reducible]
instance [DecidableEq α] {β : α → Type _} [∀ a, DecidableEq (β a)] : DecidableEq (Σ a : α, β a) :=
  fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ => 
    if h : a₁ = a₂ then 
      if h' : (h ▸ b₁) = b₂ then
        .isTrue (by subst h h'; rfl)
      else 
        .isFalse (by 
          subst h
          intro hc
          injection hc
          contradiction
        )
    else
      .isFalse (by
        intro hc
        injection hc
        contradiction
      )