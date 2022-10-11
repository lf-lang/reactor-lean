import Runtime.Utilities

namespace Interface

structure Scheme where
  vars : Type
  type : (var : vars) → Type
  [varsDecidableEq : DecidableEq vars]

attribute [reducible] Scheme.type
attribute [instance] Scheme.varsDecidableEq

abbrev Scheme.restrict (σ : Scheme) (Sub : Type) [DecidableEq Sub] [InjectiveCoe Sub σ.vars] : Scheme where
  vars := Sub
  type var := σ.type var

abbrev Scheme.union (σ₁ σ₂ : Scheme) : Scheme where
  vars := Sum σ₁.vars σ₂.vars
  type
    | .inl var => σ₁.type var 
    | .inr var => σ₂.type var

infix:65 " ⊎ " => Scheme.union

abbrev Scheme.bUnion {Schemes : Type} [DecidableEq Schemes] (σ : Schemes → Scheme) : Scheme where
  vars := Σ scheme : Schemes, (σ scheme).vars
  type := fun ⟨scheme, var⟩ => (σ scheme).type var

prefix:100 " ⨄ " => Scheme.bUnion

@[reducible]
instance {σ : Scheme} {Sub : Type} [DecidableEq Sub] [InjectiveCoe Sub σ.vars] : InjectiveCoe (σ.restrict Sub).vars σ.vars := 
  inferInstance

theorem Scheme.restrict_preserves_type (σ : Scheme) (Sub : Type) [DecidableEq Sub] [InjectiveCoe Sub σ.vars] (var : Sub) : 
  (σ.restrict Sub).type var = σ.type var := rfl

abbrev _root_.Interface (σ : Interface.Scheme) := (var : σ.vars) → (σ.type var)

end Interface

abbrev Interface? (σ : Interface.Scheme) := (var : σ.vars) → Option (σ.type var)

def Interface?.empty : Interface? σ := fun _ => none

def Interface?.isPresent (i : Interface? σ) (var : σ.vars) : Bool :=
  i var |>.isSome

-- Merge i₂ into i₁.
def Interface?.merge (i₁ i₂ : Interface? σ) : Interface? σ :=
  fun var => i₂ var |>.orElse fun _ => i₁ var