theorem Nat.zero_div_eq_zero : 0 / n = 0 := by
  induction n
  case zero => simp
  case succ => rw [div_eq]; split <;> simp_all

theorem Nat.mul_div_same_eq : (n : Nat) * m / m = n := by
  induction n generalizing m
  case zero => simp [zero_div_eq_zero]
  case succ n hi => rw [Nat.mul_comm, mul_succ]; sorry

instance [Ord α] : LE α := leOfOrd

instance : DecidableEq Empty :=
  fun empty _ => empty.casesOn

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