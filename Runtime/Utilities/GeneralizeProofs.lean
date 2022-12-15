import Lean

-- Copied from:
-- https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Tactic/GeneralizeProofs.lean

open Lean Elab Term

/-- Annotates a `binderIdent` with the binder information from an `fvar`. -/
def Lean.Expr.addLocalVarInfoForBinderIdent (fvar : Expr) : TSyntax ``binderIdent → TermElabM Unit
| `(binderIdent| $n:ident) => Elab.Term.addLocalVarInfo n fvar
| tk => Elab.Term.addLocalVarInfo (Unhygienic.run `(_%$tk)) fvar

namespace Mathlib.Tactic.GeneralizeProofs
open Meta Parser.Tactic Elab.Tactic

structure State where
  /-- The user provided names, may be anonymous -/
  nextIdx : List (TSyntax ``binderIdent)
  /-- The generalizations made so far -/
  curIdx : Array GeneralizeArg := #[]

abbrev M := MonadCacheT ExprStructEq Expr $ StateRefT State MetaM

private def mkGen (e : Expr) : M Unit := do
  let s ← get
  let t ← match s.nextIdx with
  | [] => mkFreshUserName `h
  | n :: rest =>
    modify fun s => { s with nextIdx := rest }
    match n with
    | `(binderIdent| $s:ident) => pure s.getId
    | _ => mkFreshUserName `h
  modify fun s => { s with curIdx := s.curIdx.push ⟨e, t, none⟩ }

partial def visit (e : Expr) : M Expr := do
  if e.isAtomic then
    pure e
  else
    let visitBinders (xs : Array Expr) (k : M Expr) : M Expr := do
      let localInstances ← getLocalInstances
      let mut lctx ← getLCtx
      for x in xs do
        let xFVarId := x.fvarId!
        let localDecl ← xFVarId.getDecl
        let type      ← visit localDecl.type
        let localDecl := localDecl.setType type
        let localDecl ← match localDecl.value? with
           | some value => let value ← visit value; pure <| localDecl.setValue value
           | none       => pure localDecl
        lctx := lctx.modifyLocalDecl xFVarId fun _ => localDecl
      withLCtx lctx localInstances k
    checkCache (e : ExprStructEq) fun _ => do
      if (← AbstractNestedProofs.isNonTrivialProof e) then
        mkGen e
        return e
      else match e with
        | .lam ..      => lambdaLetTelescope e fun xs b => visitBinders xs do
          mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .letE ..     => lambdaLetTelescope e fun xs b => visitBinders xs do
          mkLambdaFVars xs (← visit b) (usedLetOnly := false)
        | .forallE ..  => forallTelescope e fun xs b => visitBinders xs do
          mkForallFVars xs (← visit b)
        | .mdata _ b   => return e.updateMData! (← visit b)
        | .proj _ _ b  => return e.updateProj! (← visit b)
        | .app ..      => e.withApp fun f args => return mkAppN f (← args.mapM visit)
        | _            => pure e

elab (name := generalizeProofs) "generalize_proofs"
    hs:(ppSpace (colGt binderIdent))* loc:(ppSpace location)? : tactic => do
  let ou := if loc.isSome then
    match expandLocation loc.get! with
    | .wildcard => #[]
    | .targets t _ => t
  else #[]
  let fvs ← getFVarIds ou
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let (_, ⟨_, out⟩) ← GeneralizeProofs.visit ty |>.run.run { nextIdx := hs.toList }
  let (_, fvarIds, goal) ← goal.generalizeHyp out fvs
  for h in hs, fvar in fvarIds do
    goal.withContext <| (Expr.fvar fvar).addLocalVarInfoForBinderIdent h
  replaceMainGoal [goal]
