import Lean

open Lean Parser.Tactic in
macro "rwa " rws:rwRuleSeq loc:(location)? : tactic =>
  `(tactic| (rw $rws:rwRuleSeq $[$loc:location]?; assumption))

open Lean Meta Elab Term in
elab "unsafe " t:term : term <= expectedType => do
  let mut t ← elabTerm t expectedType
  t ← instantiateMVars t
  if t.hasExprMVar then
    synthesizeSyntheticMVarsNoPostponing
    t ← instantiateMVars t
  if ← logUnassignedUsingErrorInfos (← getMVars t) then throwAbortTerm
  t ← mkAuxDefinitionFor (← mkAuxName `unsafe) t
  let Expr.const unsafeFn unsafeLvls .. := t.getAppFn | unreachable!
  let ConstantInfo.defnInfo unsafeDefn ← getConstInfo unsafeFn | unreachable!
  let implName ← mkAuxName `impl
  addDecl <| Declaration.defnDecl {
    name := implName
    type := unsafeDefn.type
    levelParams := unsafeDefn.levelParams
    value := ← mkOfNonempty unsafeDefn.type
    hints := ReducibilityHints.opaque
    safety := DefinitionSafety.safe
  }
  setImplementedBy implName unsafeFn
  pure $ mkAppN (mkConst implName unsafeLvls) t.getAppArgs

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

namespace List

theorem eq_nil_of_length_eq_zero (_ : length l = 0) : l = [] := match l with | [] => rfl

theorem length_eq_zero : length l = 0 ↔ l = [] :=
  ⟨eq_nil_of_length_eq_zero, fun h => h ▸ rfl⟩

end List

@[inline] def decidable_of_iff (a : Prop) (h : a ↔ b) [Decidable a] : Decidable b :=
  decidable_of_decidable_of_iff h

@[inline] def decidable_of_iff' (b : Prop) (h : a ↔ b) [Decidable b] : Decidable a :=
  decidable_of_decidable_of_iff h.symm
