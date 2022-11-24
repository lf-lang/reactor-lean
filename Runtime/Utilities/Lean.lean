import Std

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

def Array.map_getElem? (as : Array α) (f : α → β) {i : Nat} :
  (as.map f)[i]? = as[i]? >>= (some ∘ f) :=
  sorry

theorem Array.findSome?_some [BEq α] {as : Array α} : (as.findSome? f = some b) → (∃ a, as.contains a ∧ f a = some b) :=
  sorry

instance [Ord α] : LE α := leOfOrd

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

-- https://github.com/leanprover-community/mathlib4/blob/a56a3c33fe9ffe2312439b8b54f6cdd243b464c6/Mathlib/Data/List/Perm.lean#L8
inductive List.Perm {α} : List α → List α → Prop
  | nil   : Perm [] []
  | cons  : ∀ (x : α) {l₁ l₂ : List α}, Perm l₁ l₂ → Perm (x::l₁) (x::l₂)
  | swap  : ∀ (x y : α) (l : List α), Perm (y::x::l) (x::y::l)
  | trans : ∀ {l₁ l₂ l₃ : List α}, Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

def Array.Perm (as₁ as₂ : Array α) := List.Perm as₁.data as₂.data

infixl:50 " ~ " => Array.Perm
