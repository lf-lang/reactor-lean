import Runtime.Time

class InjectiveCoe (α β) extends Coe α β where
  inv      : β → Option α
  invInj   : ∀ {b₁ b₂ a}, (inv b₁ = some a) → (inv b₂ = some a) → (b₁ = b₂) 
  coeInvId : ∀ a, inv (coe a) = a
  
theorem InjectiveCoe.invCoeId [inst : InjectiveCoe α β] : ∀ b, (inst.inv b = some a) → (inst.coe a = b) := 
  fun _ h => (invInj h <| inst.coeInvId a).symm  
  
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

theorem Array.findP?_property {as : Array α} : (Array.findP? as p = some a) → (p a) :=
  let rec go {idx} : (Array.findP?.loop idx as p = some a) → (p a) := by
    intro h
    unfold findP?.loop at h
    split at h <;> simp at h
    case inl hi => 
      split at h
      case inl => simp_all
      case inr => exact go h
  go
termination_by _ => as.size - idx

-- TODO: temporary
def Array.merge [Ord α] (s₁ s₂ : Array α) : Array α :=
  (s₁ ++ s₂).insertionSort (Ord.compare · · |>.isLE)

def UInt32.clipping (n : Nat) : UInt32 := 
  UInt32.ofNatCore (min n (UInt32.size - 1)) (by
    unfold min
    split
    case inr => simp
    case inl h => exact Nat.lt_succ_of_le h
  )

def IO.sleepUntil (time : Time) : IO Unit := do
  -- Note: this value clips at 0.
  let offsetNanos : Duration := time - (← IO.monoNanosNow) 
  let offsetMicros : UInt32 := .clipping (offsetNanos / 1000)
  sleep offsetMicros
