import Runtime.Utilities

namespace Interface

structure Scheme where
  vars : Type
  type : (var : vars) → Type
  [varsDecidableEq : DecidableEq vars]

attribute [reducible] Scheme.type
attribute [instance] Scheme.varsDecidableEq

abbrev Scheme.restrict (σ : Scheme) (Sub : Type) [DecidableEq Sub] [InjectiveCoe Sub σ.vars] : Scheme := {
  vars := Sub
  type := fun var => σ.type var
}

abbrev Scheme.sum (σ₁ σ₂ : Scheme) : Scheme := {
  vars := Sum σ₁.vars σ₂.vars
  type := fun
    | .inl var => σ₁.type var
    | .inr var => σ₂.type var
}

abbrev Scheme.sum' (Schemes : Type) [DecidableEq Schemes] (σ : Schemes → Scheme) : Scheme := {
  vars := Σ scheme : Schemes, (σ scheme).vars
  type := fun ⟨scheme, var⟩ => (σ scheme).type var
}

instance {σ : Scheme} {Sub : Type} [DecidableEq Sub] [InjectiveCoe Sub σ.vars] : InjectiveCoe (σ.restrict Sub).vars σ.vars := 
  inferInstance

theorem Scheme.restrict_preserves_type {σ : Scheme} {Sub : Type} [DecidableEq Sub] [InjectiveCoe Sub σ.vars] {var : Sub} : 
  (σ.restrict Sub).type var = σ.type var := rfl

abbrev _root_.Interface (σ : Interface.Scheme) := (var : σ.vars) → Option (σ.type var)

def isPresent (i : Interface σ) (var : σ.vars) : Bool :=
  (i var).isSome

-- Merge i₂ into i₁.
def merge (i₁ i₂ : Interface σ) : Interface σ :=
  fun var => (i₂ var).orElse (fun _ => i₁ var)

-- Merge i₂ into i₁.
def merge' {Sub : Type} [DecidableEq Sub] [injCoe : InjectiveCoe Sub σ.vars] (i₁ : Interface σ) (i₂ : Interface $ σ.restrict Sub) : Interface σ :=
  fun var => 
    match h : injCoe.inv var with 
    | none => i₁ var
    | some sub => 
      have h₁ : (σ.restrict Sub).type sub = σ.type sub := Scheme.restrict_preserves_type
      have h₂ : Coe.coe sub = var := h.symm ▸ injCoe.coeInvId sub |> injCoe.invInj
      h₂ ▸ h₁ ▸ i₂ sub

end Interface
