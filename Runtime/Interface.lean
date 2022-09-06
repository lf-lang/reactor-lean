class InjectiveCoe (α β) extends Coe α β where
  inv      : β → Option α
  invInj   : ∀ {b₁ b₂}, (inv b₁ = inv b₂) → (b₁ = b₂) 
  coeInvId : ∀ a, inv (coe a) = a

structure Scheme where
  vars : Type
  type : (var : vars) → Type
  [varsDecidableEq : DecidableEq vars]

attribute [reducible] Scheme.type
attribute [instance] Scheme.varsDecidableEq

abbrev Scheme.restrict (σ : Scheme) (Sub : Type) [DecidableEq Sub] [InjectiveCoe Sub σ.vars] : Scheme := {
  vars := Sub,
  type := fun var => σ.type var
}

instance {σ : Scheme} {Sub : Type} [DecidableEq Sub] [InjectiveCoe Sub σ.vars] : InjectiveCoe (σ.restrict Sub).vars σ.vars := 
  inferInstance

theorem Scheme.restrict_preserves_type {σ : Scheme} {Sub : Type} [DecidableEq Sub] [InjectiveCoe Sub σ.vars] {var : Sub} : 
  (σ.restrict Sub).type var = σ.type var := rfl

abbrev Interface (σ : Scheme) := (var : σ.vars) → Option (σ.type var)

-- Merge i₂ into i₁.
def Interface.merge (i₁ i₂ : Interface σ) : Interface σ :=
  fun var => (i₂ var).orElse (fun _ => i₁ var)

-- Merge i₂ into i₁.
def Interface.merge' {Sub : Type} [DecidableEq Sub] [injCoe : InjectiveCoe Sub σ.vars] (i₁ : Interface σ) (i₂ : Interface $ σ.restrict Sub) : Interface σ :=
  fun var => 
    match h : injCoe.inv var with 
    | none => i₁ var
    | some sub => 
      have h₁ : (σ.restrict Sub).type sub = σ.type sub := Scheme.restrict_preserves_type
      have h₂ : Coe.coe sub = var := h.symm ▸ injCoe.coeInvId sub |> injCoe.invInj
      h₂ ▸ h₁ ▸ i₂ sub