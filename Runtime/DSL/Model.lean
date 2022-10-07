import Runtime.Network.Basic
import Lean
open Lean Macro

structure InterfaceVar where
  id : Ident
  value : Term

def InterfaceDecl := Array InterfaceVar
  deriving Inhabited

def InterfaceDecl.ids (decl : InterfaceDecl) := 
  decl.map (·.id)

def InterfaceDecl.values (decl : InterfaceDecl) := 
  decl.map (·.value)

structure TriggerDecl where
  ports : Array Ident
  actions : Array Ident
  meta : Array Ident

inductive ReactionDecl.DependencyKind
  | portSource
  | portEffect
  | actionSource
  | actionEffect

def ReactionDecl.DependencyKind.allCases : Array DependencyKind := 
  #[.portSource, .portEffect, .actionSource, .actionEffect]

structure ReactionDecl where
  dependencies : ReactionDecl.DependencyKind → Array Ident
  triggers : TriggerDecl
  body : TSyntax `Lean.Parser.Term.doSeq
  
structure ReactorDecl where
  name : Ident
  interfaces : Reactor.InterfaceKind → InterfaceDecl
  nested : InterfaceDecl
  reactions : Array ReactionDecl
  deriving Inhabited

def ReactorDecl.num (decl : ReactorDecl) (kind : Reactor.InterfaceKind) :=
  decl.interfaces kind |>.size

structure GraphDecl where
  name : Ident 
  reactors : Array ReactorDecl

def GraphDecl.reactorNames (decl : GraphDecl) :=
  decl.reactors.map (·.name)

def GraphDecl.mainReactorIdent! (decl : GraphDecl) :=
  let reactorIdent := decl.reactors[0]!.name
  mkIdentFrom reactorIdent (decl.name.getId ++ `Class ++ reactorIdent.getId)

def GraphDecl.reactorWithName (decl : GraphDecl) (className : Name) : MacroM ReactorDecl :=
  match decl.reactors.find? (·.name.getId = className) with
  | some rtr => return rtr
  | none => Macro.throwError s!"GraphDecl.reactorWithName: Unknown reactor '{className}'"

def GraphDecl.numNested (decl : GraphDecl) (rtr : Name) (kind : Reactor.InterfaceKind) : MacroM Nat := do
  let rtr ← decl.reactorWithName rtr
  rtr.nested.values.foldlM (init := 0) fun acc «class» => do
    match «class» with 
    | `($c:ident) => 
      let nestedReactor ← decl.reactorWithName c.getId
      return acc + nestedReactor.num kind
    | _ => Macro.throwError s!"GraphDecl.numNested: Illformed reactor class '{«class»}'"

def GraphDecl.numSources (decl : GraphDecl) (rtr : Name) : MacroM Nat := do
  let numLocalInputs := (← decl.reactorWithName rtr).num .inputs
  let numNestedOutputs ← decl.numNested rtr .outputs
  return numLocalInputs + numNestedOutputs

def GraphDecl.numEffects (decl : GraphDecl) (rtr : Name) : MacroM Nat := do
  let numLocalOutputs := (← decl.reactorWithName rtr).num .outputs
  let numNestedInputs ← decl.numNested rtr .inputs
  return numLocalOutputs + numNestedInputs

def GraphDecl.numDependencies (decl : GraphDecl) (rtr : Name) : ReactionDecl.DependencyKind → MacroM Nat
  | .portSource => decl.numSources rtr
  | .portEffect => decl.numEffects rtr
  | .actionSource | .actionEffect => return (← decl.reactorWithName rtr).num .actions