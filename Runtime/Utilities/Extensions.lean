import Runtime.Time

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
