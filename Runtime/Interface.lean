import Runtime.Utilities

namespace Interface

/--
An interface scheme captures the type signature of a dependent map. Specifically, a scheme
`{ vars, type }` describes the type `(var : vars) → (type var)`.

This type is used to describe the structures of components in reactors like ports, state variables,
actions and parameters, which are all maps from names to values of different types.
-/
structure Scheme where
  vars : Type
  type : vars → Type
  [varsDecidableEq : DecidableEq vars]

attribute [reducible] Scheme.type
attribute [instance] Scheme.varsDecidableEq

/--
The (disjoint) union of two schemes describes the signature of a map where the domain is the
disjoint union of the respective schemes' domains. The codomain is extended in the obvious way.
-/
abbrev Scheme.union (σ₁ σ₂ : Scheme) : Scheme where
  vars := Sum σ₁.vars σ₂.vars
  type
    | .inl var => σ₁.type var
    | .inr var => σ₂.type var

infix:65 " ⊎ " => Scheme.union

@[simp]
theorem Scheme.union_type_left (σ₁ σ₂ : Scheme) (var : σ₁.vars) :
  (σ₁ ⊎ σ₂).type (.inl var) = σ₁.type var := rfl

@[simp]
theorem Scheme.union_type_right (σ₁ σ₂ : Scheme) (var : σ₂.vars) :
  (σ₁ ⊎ σ₂).type (.inr var) = σ₂.type var := rfl

/-- The big-union of schemes generalizes the notion of unions of schemes to a family of schemes. -/
def Scheme.bUnion (σs : I → Scheme) [DecidableEq I] : Scheme where
  vars := (i : I) × (σs i).vars
  type := fun ⟨i, var⟩ => (σs i).type var

prefix:100 " ⨄ " => Scheme.bUnion

@[simp]
theorem Scheme.bUnion_vars (σs : I → Scheme) [DecidableEq I] :
  (⨄ σs).vars = ((i : I) × (σs i).vars) := rfl

@[simp]
theorem Scheme.bUnion_type (σs : I → Scheme) [DecidableEq I] (var : (σs i).vars) :
  (⨄ σs).type ⟨i, var⟩ = (σs i).type var := rfl

/--
A scheme `σ₁` is a "subscheme" of `σ₂` if:
1. the domain of `σ₁` is a subtype of the domain of `σ₂`, and
2. `σ₁` and `σ₂` map the elements in `σ₁`'s domain to the same types.

We express property 1 not as a `Subtype` but as the coercion `coe`. Property 2 is ensured by
`coeEqType`. The `inv` map and additional properties provide an inverse map to `coe` (this map has
to be partial as `coe` isn't necessarilly bijective).
-/
class Subscheme (σ₁ σ₂ : Scheme) where
  coe       : σ₁.vars → σ₂.vars
  inv       : σ₂.vars → Option σ₁.vars
  invInj    : ∀ {a b₁ b₂}, (inv b₁ = some a) → (inv b₂ = some a) → (b₁ = b₂)
  coeInvId  : ∀ a, inv (coe a) = a
  coeEqType : ∀ {v}, σ₂.type (coe v) = σ₁.type v

theorem Subscheme.invEqType [inst : Subscheme σ₁ σ₂] : ∀ {b}, (inst.inv b = some a) → (σ₁.type a = σ₂.type b) :=
  fun h => by rw [←inst.coeEqType (v := a), inst.invInj h (inst.coeInvId a)]

end Interface

/--
An `Interface` over a scheme `{ vars, type }` is a map `(var : vars) → (type var)`. This type is
used to for components in reactors like state variables and parameters, which are maps from names to
values of different types.
-/
def Interface (σ : Interface.Scheme) := (var : σ.vars) → (σ.type var)

/--
An `Interface?` over a scheme `{ vars, type }` is a map `(var : vars) → Option (type var)`. This
type is used for components in reactors like ports and actions and parameters, which are maps from
names to values of different types which need to be able to be absent.
-/
def Interface? (σ : Interface.Scheme) := (var : σ.vars) → Option (σ.type var)

namespace Interface?

/-- The `Interface?` where every element is absent. -/
protected def empty : Interface? σ := fun _ => none

@[simp]
theorem empty_none : Interface?.empty var = none := rfl

/-- An `Interface?` is empty if it is `Interface?.empty` (that is, all elements are absent). -/
def isEmpty (i : Interface? σ) := i = Interface?.empty

@[simp]
theorem isEmpty_def (i : Interface? σ) : i.isEmpty ↔ i = Interface?.empty := by
  simp [isEmpty]

/-- An `Interface?` is empty if it is `Interface?.empty` (that is, all elements are absent). -/
def isPresent (i : Interface? σ) (var : σ.vars) : Bool :=
  i var |>.isSome

@[simp]
theorem isPresent_def (i : Interface? σ) : i.isPresent var ↔ ∃ v, i var = some v := by
  simp [isPresent, Option.isSome_iff_exists]

/--
Merges interface `i₂` "into" `i₁`. That is, for each element `e`:
* if `i₁ e` is present, return that value
* otherwise, return `i₂ e`
-/
def merge (i₁ i₂ : Interface? σ) : Interface? σ :=
  fun var => i₂ var |>.orElse fun _ => i₁ var

theorem merge_val₁ (i₁ i₂ : Interface? σ) : (i₂ var = none) → (i₁.merge i₂) var = i₁ var := by
  simp_all [merge, Option.orElse]

theorem merge_val₂ (i₁ i₂ : Interface? σ) : (i₂ var = some v) → (i₁.merge i₂) var = some v := by
  simp_all [merge, Option.orElse]

theorem merge_idem : Interface?.merge i i = i := by
  funext var
  simp [merge, Option.orElse]
  split
  · exact Eq.symm ‹_›
  · simp

/-- Restricts the domain of the given interface to that of a given subscheme. -/
def restrict [inst : Interface.Subscheme σ₁ σ₂] (i : Interface? σ₂) : Interface? σ₁ :=
  fun var => inst.coeEqType ▸ i (inst.coe var)

end Interface?
