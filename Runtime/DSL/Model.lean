import Runtime.Network.Basic
import Lean
open Lean Macro

structure InterfaceVar where
  id : Ident
  value : Term
  default : Option Term

def InterfaceVar.getDefault (var : InterfaceVar) : MacroM Term :=
  match var.default with
  | some term => return term
  | _ => Macro.throwError s!"InterfaceVar.getDefault: Expected non-none value"

def InterfaceVar.valueIdent (var : InterfaceVar) : MacroM Ident :=
  match var.value with
  | `($value:ident) => return value
  | _ => Macro.throwError s!"InterfaceVar.valueIdent: Illformed identifier '{var.value}'"

def InterfaceDecl := Array InterfaceVar
  deriving Inhabited

def InterfaceDecl.ids (decl : InterfaceDecl) :=
  decl.map (·.id)

def InterfaceDecl.values (decl : InterfaceDecl) :=
  decl.map (·.value)

def InterfaceDecl.valueIdents (decl : InterfaceDecl) : MacroM (Array Ident) :=
  decl.mapM (·.valueIdent)

structure InstanceDecl where
  id : Ident
  «class» : Ident
  params : InterfaceDecl

def InstanceDecl.parameterValue? (decl : InstanceDecl) (param : Name) : MacroM (Option Term) := do
  match decl.params.find? (·.id.getId = param) with
  | none => return none
  | some p => return p.default

def NestedDecl := Array InstanceDecl
  deriving Inhabited

structure TriggerDecl where
  ports :   Array Ident
  actions : Array Ident
  timers :  Array Ident
  meta :    Array Ident

inductive ReactionDecl.DependencyKind
  | portSource
  | portEffect
  | actionSource
  | actionEffect

def ReactionDecl.DependencyKind.allCases : Array DependencyKind :=
  #[.portSource, .portEffect, .actionSource, .actionEffect]

structure ReactionDecl where
  kind : Ident
  dependencies : ReactionDecl.DependencyKind → Array Ident
  triggers : TriggerDecl
  body : TSyntax `Lean.Parser.Term.doSeq

structure TimerDecl where
  name : Ident
  offset : Term
  period : Term

structure ReactorDecl where
  name        : Ident
  interfaces  : Reactor.InterfaceKind → InterfaceDecl
  timers      : Array TimerDecl
  nested      : NestedDecl
  connections : InterfaceDecl
  reactions   : Array ReactionDecl
  deriving Inhabited

def ReactorDecl.num (decl : ReactorDecl) (kind : Reactor.InterfaceKind) :=
  decl.interfaces kind |>.size

structure NetworkDecl where
  reactors : Array ReactorDecl

def NetworkDecl.namespaceIdent (_ : NetworkDecl) :=
  mkIdent `LF

def NetworkDecl.networkIdent (network : NetworkDecl) :=
  mkIdentFrom network.namespaceIdent <| network.namespaceIdent.getId ++ `network

def NetworkDecl.graphName (_ : NetworkDecl) : Ident :=
  mkIdent `graph

def NetworkDecl.graphIdent (network : NetworkDecl) :=
  mkIdentFrom network.namespaceIdent <| network.namespaceIdent.getId ++ network.graphName.getId

def NetworkDecl.reactorNames (decl : NetworkDecl) :=
  decl.reactors.map (·.name)

def NetworkDecl.mainReactor (decl : NetworkDecl) : MacroM ReactorDecl := do
  match decl.reactors[0]? with
  | some rtr => return rtr
  | none => Macro.throwError "NetworkDecl.mainReactor!: No reactor declaration found"

def NetworkDecl.mainReactorClass (decl : NetworkDecl) : MacroM Term := do
  `(.$((← decl.mainReactor).name))

def NetworkDecl.reactorWithName (decl : NetworkDecl) (className : Name) : MacroM ReactorDecl :=
  match decl.reactors.find? (·.name.getId = className) with
  | some rtr => return rtr
  | none => Macro.throwError s!"NetworkDecl.reactorWithName: Unknown reactor '{className}'"

def NetworkDecl.numNested (decl : NetworkDecl) (rtr : Name) (kind : Reactor.InterfaceKind) : MacroM Nat := do
  let rtr ← decl.reactorWithName rtr
  rtr.nested.map (·.class) |>.foldlM (init := 0) fun acc «class» => do
    match «class» with
    | `($c:ident) =>
      let nestedReactor ← decl.reactorWithName c.getId
      return acc + nestedReactor.num kind
    | _ => Macro.throwError s!"NetworkDecl.numNested: Illformed reactor class '{«class»}'"

def NetworkDecl.numSources (decl : NetworkDecl) (rtr : Name) : MacroM Nat := do
  let numLocalInputs := (← decl.reactorWithName rtr).num .inputs
  let numNestedOutputs ← decl.numNested rtr .outputs
  return numLocalInputs + numNestedOutputs

def NetworkDecl.numEffects (decl : NetworkDecl) (rtr : Name) : MacroM Nat := do
  let numLocalOutputs := (← decl.reactorWithName rtr).num .outputs
  let numNestedInputs ← decl.numNested rtr .inputs
  return numLocalOutputs + numNestedInputs

def NetworkDecl.numDependencies (decl : NetworkDecl) (rtr : Name) : ReactionDecl.DependencyKind → MacroM Nat
  | .portSource => decl.numSources rtr
  | .portEffect => decl.numEffects rtr
  | .actionSource | .actionEffect => return (← decl.reactorWithName rtr).num .actions

-- This only terminates if the network (class) graph is acyclic.
partial def NetworkDecl.instancePaths (decl : NetworkDecl) : MacroM <| Array ((Array Name) × Name) := do
  let mainReactorName := (← decl.mainReactor).name.getId
  return #[(#[], mainReactorName)] ++ (← go decl mainReactorName #[])
where
  go (network : NetworkDecl) (rtrName : Name) (pre : Array Name) : MacroM <| Array ((Array Name) × Name) := do
    let rtr ← network.reactorWithName rtrName
    rtr.nested.flatMapM fun var => do
      let path := pre.push var.id.getId
      let name := var.class.getId
      return #[(path, name)] ++ (← go network name path)

instance : ToString Reactor.InterfaceKind where
  toString
    | .inputs => "inputs"
    | .outputs => "outputs"
    | .actions => "actions"
    | .state => "state"
    | .params => "params"

def NetworkDecl.type (decl : NetworkDecl) (reactor : Name) (kind : ReactionDecl.DependencyKind) (target : Name) : MacroM Term := do
  let rtrDecl ← decl.reactorWithName reactor
  match target with
  | .str .anonymous _ =>
    match kind with
    | .portSource                   => getLocal rtrDecl .inputs target
    | .portEffect                   => getLocal rtrDecl .outputs target
    | .actionSource | .actionEffect => getLocal rtrDecl .actions target
  | .str (.str .anonymous rtr) l =>
    match rtrDecl.nested.find? (·.id.getId = .mkSimple rtr) with
    | some instDecl =>
      let childRtr ← decl.reactorWithName instDecl.class.getId
      match kind with
      | .portSource                   => getLocal childRtr .outputs (.mkSimple l)
      | .portEffect                   => getLocal childRtr .inputs (.mkSimple l)
      | .actionSource | .actionEffect => getLocal childRtr .actions (.mkSimple l)
    | none => Macro.throwError s!"NetworkDecl.type: Illformed nested reactor in target '{target}' of reactor '{reactor}'"
  | _ => Macro.throwError s!"NetworkDecl.type: Illformed target name '{target}'"
where
  getLocal (rtrDecl : ReactorDecl) (kind : Reactor.InterfaceKind) (target : Name) := do
    match (rtrDecl.interfaces kind).find? (·.id.getId = target) with
    | some i => return i.value
    | none => Macro.throwError s!"NetworkDecl.type: Invalid target '{target}' of kind '{kind}' in reactor '{reactor}'"

structure LFDecl where
  network : NetworkDecl
  schedule : Array Ident
