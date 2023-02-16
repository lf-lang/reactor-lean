import Runtime.Time

@[simp]
theorem Array.getElem?_nil {i : Nat} : (#[] : Array α)[i]? = none := by
  simp [getElem?]; split <;> simp; contradiction

@[simp]
theorem Array.getElem?_zero_singleton : (#[a] : Array α)[0]? = a := rfl

theorem Array.getElem?_zero_isSome_iff_not_isEmpty {as : Array α} : as[0]?.isSome ↔ ¬as.isEmpty := by
  simp [Array.isEmpty, Option.isSome_iff_exists, getElem?]
  constructor
  case mp =>
    intro ⟨_, h⟩
    split at h
    case inl hs => exact Nat.not_eq_zero_of_lt hs
    case inr => contradiction
  case mpr =>
    intro h
    split
    case inl => exists as[0]
    case inr hs => exact absurd (Nat.zero_lt_of_ne_zero h) hs

theorem Array.isEmpty_iff_data_eq_nil {as : Array α} : as.isEmpty ↔ as.data = [] := by
  simp [isEmpty, size]
  exact List.length_eq_zero

theorem Array.any_iff_mem_where {as : Array α} : (as.any p) ↔ (∃ a, (a ∈ as.data) ∧ p a) := sorry

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

def Array.merge (s₁ s₂ : Array α) (le : α → α → Bool) : Array α :=
  (s₁ ++ s₂).insertionSort le

def Array.unique (as : Array α) (f : α → β) [DecidableEq β] : (Array α) × (Array α) := Id.run do
  let mut included : Array α := #[]
  let mut excluded : Array α := #[]
  for a in as do
    if included.any (f a = f ·)
    then excluded := excluded.push a
    else included := included.push a
  return (included, excluded)

def Array.uniqueMergeMap [BEq α] (as : Array α) (f : α → Array β) (le : β → β → Bool) :
  Array β := Id.run do
  let mut processed : Array α := #[]
  let mut result : Array β := #[]
  for a in as do
    if ¬ processed.contains a then
      processed := processed.push a
      result := result.merge (f a) le
  return result

-- `Array.find?` isn't universe polymorphic.
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

def UInt32.clipping (n : Nat) : UInt32 :=
  UInt32.ofNatCore (min n (UInt32.size - 1)) (by
    rw [Nat.min_def]
    split
    case inr => simp
    case inl h => exact Nat.lt_succ_of_le h
  )

def IO.sleepUntil (time : Time) : IO Unit := do
  let offset := time - (← Time.now)
  sleep <| UInt32.clipping <| offset.to .ms
