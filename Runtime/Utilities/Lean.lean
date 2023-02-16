section Std4

open Lean Parser.Tactic in
macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))

namespace Nat

theorem div_eq_sub_div (h₁ : 0 < b) (h₂ : b ≤ a) : a / b = (a - b) / b + 1 := by
 rw [div_eq a, if_pos]; constructor <;> assumption

@[simp] theorem add_div_right (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = succ (x / z) := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]

theorem add_mul_div_left (x z : Nat) {y : Nat} (H : 0 < y) : (x + y * z) / y = x / y + z := by
  induction z with
  | zero => rw [Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  | succ z ih => rw [mul_succ, ← Nat.add_assoc, add_div_right _ H, ih]; rfl

theorem add_mul_div_right (x y : Nat) {z : Nat} (H : 0 < z) : (x + y * z) / z = x / z + y := by
  rw [Nat.mul_comm, add_mul_div_left _ _ H]

@[simp] protected theorem zero_div (b : Nat) : 0 / b = 0 :=
  (div_eq 0 b).trans <| if_neg <| And.rec Nat.not_le_of_gt

protected theorem mul_div_cancel (m : Nat) {n : Nat} (H : 0 < n) : m * n / n = m := by
  let t := add_mul_div_right 0 m H
  rwa [Nat.zero_add, Nat.zero_div, Nat.zero_add] at t

end Nat

variable {p q : α → Prop}

@[simp] theorem forall_exists_index {q : (∃ x, p x) → Prop} :
    (∀ h, q h) ↔ ∀ x (h : p x), q ⟨x, h⟩ :=
  ⟨fun h x hpx => h ⟨x, hpx⟩, fun h ⟨x, hpx⟩ => h x hpx⟩

theorem exists_imp : ((∃ x, p x) → b) ↔ ∀ x, p x → b := forall_exists_index

@[simp] theorem not_exists: (¬∃ x, p x) ↔ ∀ x, ¬p x := exists_imp

namespace Option

@[simp] theorem isSome_none : @isSome α none = false := rfl

@[simp] theorem isSome_some : isSome (some a) = true := rfl

theorem isSome_iff_exists : isSome x ↔ ∃ a, x = some a := by
  cases x <;> simp [isSome]
  exists ‹_›

end Option

@[inline] def decidable_of_iff (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff h

@[inline] def decidable_of_iff' (b : Prop) (h : a ↔ b) [Decidable b] : Decidable a :=
  decidable_of_decidable_of_iff h.symm

end Std4

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

theorem Array.any_iff_mem_where {as : Array α} : (as.any p) ↔ (∃ a, (a ∈ as.data) ∧ p a) := sorry

theorem Array.isEmpty_iff_data_eq_nil {as : Array α} : as.isEmpty ↔ as.data = [] := sorry

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
