class InjectiveCoe (α β) extends Coe α β where
  inv      : β → Option α
  invInj   : ∀ {b₁ b₂}, (inv b₁ = inv b₂) → (b₁ = b₂) 
  coeInvId : ∀ a, inv (coe a) = a

class OrdCoe (α β) [Ord α] [Ord β] extends Coe α β where
  coeOrd : ∀ a₁ a₂, compare a₁ a₂ = compare (a₁ : β) (a₂ : β)

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

def Array.unique (as : Array α) (f : α → β) [DecidableEq β] : (Array α) × (Array α) := Id.run do
  let mut included : Array α := #[] 
  let mut excluded : Array α := #[]
  for a in as do
    if included.any (f a = f ·) 
    then excluded := excluded.push a
    else included := included.push a
  return (included, excluded)

def Array.findP? (as : Array α) (p : α → Bool) : Option α := do
  loop 0 as p
where 
  loop (idx : Nat) (as : Array α) (p : α → Bool) : Option α :=
  if h : idx < as.size then
    let a := as[idx]
    if p a then a else loop (idx + 1) as p
  else 
    none
  termination_by _ => as.size - idx

theorem Array.findP?_property {as : Array α} : (as.findP? p = some a) → (p a) := by
  sorry

-- TODO: temporary
def Array.merge [Ord α] (s₁ s₂ : Array α) : Array α :=
  (s₁ ++ s₂).insertionSort (Ord.compare · · |>.isLE)