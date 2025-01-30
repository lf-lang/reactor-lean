import Runtime.Time

theorem Array.getElem?_zero_isSome_iff_not_isEmpty {as : Array α} : as[0]?.isSome ↔ ¬as.isEmpty := by
  simp [Array.isEmpty, Option.isSome_iff_exists, getElem?]
  constructor
  case mp =>
    intro ⟨_, h, _⟩
    exact List.ne_nil_of_length_pos h
  case mpr =>
    intro h
    have he := List.ne_nil_iff_exists_cons.mp h
    have hs := List.length_pos_iff_exists_cons.mpr he
    exact ⟨as[0], hs, rfl⟩

theorem Array.isEmpty_iff_toList_eq_nil {as : Array α} : as.isEmpty ↔ as.toList = [] := by
  simp

theorem Array.any_iff_mem_where {as : Array α} : (as.any p) ↔ (∃ a, (a ∈ as.toList) ∧ p a) := sorry

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
termination_by as.size - idx

theorem Array.findP?_property {as : Array α} : (Array.findP? as p = some a) → (p a) :=
  let rec go {idx} : (Array.findP?.loop idx as p = some a) → (p a) := by
    intro h
    unfold findP?.loop at h
    split at h <;> simp at h
    case isTrue hi =>
      split at h
      case isTrue => simp_all
      case isFalse => exact go h
  go

def UInt32.clipping (n : Nat) : UInt32 :=
  UInt32.ofNatCore (min n (UInt32.size - 1)) (by
    rw [Nat.min_def]
    split
    case isTrue h => exact Nat.lt_succ_of_le h
    case isFalse  => simp
  )

def IO.sleepUntil (time : Time) : IO Unit := do
  let offset := time - (← Time.now)
  sleep <| UInt32.clipping <| offset.to .ms
