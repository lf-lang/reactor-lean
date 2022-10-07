import Runtime.Network.Basic
import Lean
open Lean Macro

structure InterfaceVar where
  id : Ident
  value : Term

def InterfaceDecl := Array InterfaceVar
  deriving Inhabited

structure TriggerDecl where
  ports : Array Ident
  actions : Array Ident
  meta : Array Ident

inductive ReactionDecl.DependencyKind
  | portSource
  | portEffect
  | actionSource
  | actionEffect

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

structure GraphDecl where
  name : Ident 
  reactors : Array ReactorDecl

declare_syntax_cat interface_var
syntax ident " : " term : interface_var

declare_syntax_cat interface_decl
syntax "[" interface_var,* "]" : interface_decl

declare_syntax_cat ident_list
syntax "[" ident,* "]" : ident_list

declare_syntax_cat trigger_decl
syntax "triggers" "{"
  "ports" ident_list
  "actions" ident_list
  "meta" ident_list
  "}" : trigger_decl

declare_syntax_cat reaction_decl
syntax "{"  
  "portSources"   ident_list
  "portEffects"   ident_list
  "actionSources" ident_list
  "actionEffects" ident_list
  trigger_decl
  "body" ":=" doSeq
  "}" : reaction_decl

declare_syntax_cat reactor_decl
syntax "reactor" ident 
  "inputs"  interface_decl 
  "outputs" interface_decl 
  "actions" interface_decl 
  "state"   interface_decl 
  "nested"  interface_decl
  "reactions" "[" reaction_decl* "]"
  : reactor_decl

declare_syntax_cat graph_decl
syntax ident "where" reactor_decl+ : graph_decl

def InterfaceVar.fromSyntax : TSyntax `interface_var → MacroM InterfaceVar
  | `(interface_var| $id:ident : $value) => return { id := id, value := value }
  | _ => throwUnsupported

def InterfaceDecl.fromSyntax : TSyntax `interface_decl → MacroM InterfaceDecl
  | `(interface_decl| [$vars:interface_var,*]) => vars.getElems.mapM InterfaceVar.fromSyntax
  | _ => throwUnsupported

def TriggerDecl.fromSyntax : TSyntax `trigger_decl → MacroM TriggerDecl
  | `(trigger_decl| triggers { ports [$p:ident,*] actions [$a:ident,*] meta [$m:ident,*] }) =>
    return { «ports» := p, «actions» := a, «meta» := m }
  | _ => throwUnsupported

def ReactionDecl.fromSyntax : TSyntax `reaction_decl → MacroM ReactionDecl 
  | `(reaction_decl| { 
      portSources [$ps:ident,*] portEffects [$pe:ident,*] actionSources [$as:ident,*] 
      actionEffects [$ae:ident,*] $ts:trigger_decl body := $b:doSeq
    }) => return { 
      dependencies := fun | .portSource => ps | .portEffect => pe | .actionSource => as | .actionEffect => ae
      «triggers» := ← TriggerDecl.fromSyntax ts
      «body» := b
    }
  | _ => throwUnsupported

def ReactorDecl.fromSyntax : TSyntax `reactor_decl → MacroM ReactorDecl
  | `(reactor_decl| reactor $name:ident inputs $i outputs $o actions $a state $s nested $n reactions [$r:reaction_decl*]) => do
    let i ← InterfaceDecl.fromSyntax i
    let o ← InterfaceDecl.fromSyntax o
    let a ← InterfaceDecl.fromSyntax a
    let s ← InterfaceDecl.fromSyntax s
    let n ← InterfaceDecl.fromSyntax n
    let r ← r.mapM ReactionDecl.fromSyntax
    return {
      name := name
      interfaces := fun | .inputs => i | .outputs => o | .actions => a | .state => s
      «nested» := n
      «reactions» := r  
    }
  | _ => throwUnsupported

def GraphDecl.fromSyntax : TSyntax `graph_decl → MacroM GraphDecl
  | `(graph_decl| $name:ident where $reactors:reactor_decl*) => return {
      name := name
      reactors := (← reactors.mapM ReactorDecl.fromSyntax)
    }
  | _ => throwUnsupported

def InterfaceDecl.ids (decl : InterfaceDecl) := 
  decl.map (·.id)

def InterfaceDecl.values (decl : InterfaceDecl) := 
  decl.map (·.value)

def ReactorDecl.num (decl : ReactorDecl) (kind : Reactor.InterfaceKind) :=
  decl.interfaces kind |>.size

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

def InterfaceDecl.genInterfaceScheme (decl : InterfaceDecl) (name : Ident) : MacroM Command := 
  let schemeIdent := mkIdentFrom name (name.getId ++ `scheme)
  let types := decl.values
  `(
    inductive $name $[| $(decl.ids):ident]* deriving DecidableEq
    abbrev $schemeIdent : Interface.Scheme where
      vars := $name
      type var := match var with $[| $(decl.ids) => $types]*
  )

def ReactionDecl.DependencyKind.allCases : Array DependencyKind := 
  #[.portSource, .portEffect, .actionSource, .actionEffect]

def ReactionDecl.DependencyKind.name : ReactionDecl.DependencyKind → Name
  | .portSource   => `PortSource
  | .portEffect   => `PortEffect
  | .actionSource => `ActionSource
  | .actionEffect => `ActionEffect

def ReactionDecl.DependencyKind.injCoeTarget (graphIdent classIdent : Ident) : ReactionDecl.DependencyKind → MacroM Term 
  | .portSource                  => `((Network.Graph.reactionInputScheme $graphIdent $classIdent |>.vars))
  | .portEffect                  => `((Network.Graph.reactionOutputScheme $graphIdent $classIdent |>.vars))
  | .actionSource |.actionEffect => `((Network.Graph.schemes $graphIdent $classIdent |>.interface .actions |>.vars))

def ReactionDecl.genDependencyEnums (decl : ReactionDecl) (ns : Ident) : MacroM (Array Command) := do
  ReactionDecl.DependencyKind.allCases.mapM fun kind =>
    let enumIdent := mkIdentFrom ns (ns.getId ++ kind.name)
    let ids := decl.dependencies kind
    `(inductive $enumIdent $[| $ids:ident]* deriving DecidableEq)

structure InjCoeGenDescription where
  dependencyKind : ReactionDecl.DependencyKind
  ids : Array Ident
  graphIdent : Ident
  noNsReactorIdent : Ident
  reactionIdx : Nat
  isComplete : Bool

def InjCoeGenDescription.reactorIdent (descr : InjCoeGenDescription) :=
  mkIdentFrom descr.noNsReactorIdent <| descr.graphIdent.getId ++ descr.noNsReactorIdent.getId

def InjCoeGenDescription.classIdent (descr : InjCoeGenDescription) :=
  mkIdentFrom descr.noNsReactorIdent <| descr.graphIdent.getId ++ `Class ++ descr.noNsReactorIdent.getId

def InjCoeGenDescription.sourceTypeIdent (descr : InjCoeGenDescription) :=
  mkIdentFrom descr.reactorIdent (descr.reactorIdent.getId ++ s!"Reaction{descr.reactionIdx}" ++ descr.dependencyKind.name)

def InjCoeGenDescription.targetTypeTerm (descr : InjCoeGenDescription) :=
  descr.dependencyKind.injCoeTarget descr.graphIdent descr.classIdent

def InjCoeGenDescription.injCoeType (descr : InjCoeGenDescription) := do
  `(InjectiveCoe $(descr.sourceTypeIdent) $(← descr.targetTypeTerm))

def InjCoeGenDescription.sourceTerms (descr : InjCoeGenDescription) : MacroM (Array Term) := do
  descr.ids.mapM fun id => `(.$id)

def InjCoeGenDescription.sumTerms (descr : InjCoeGenDescription) : MacroM (Array Term) := 
  descr.ids.mapM fun id => do
    match id.getId with
    | .str .anonymous l            => `(.inl .$(mkIdent <| .mkSimple l))
    | .str (.str .anonymous rtr) l => `(.inr ⟨.$(mkIdent <| .mkSimple rtr), .$(mkIdent <| .mkSimple l)⟩)
    | _                            => throwUnsupported 

def InjCoeGenDescription.genInjectiveCoe (descr : InjCoeGenDescription) : MacroM Command := do
  if descr.ids.isEmpty then 
    forEmpty descr
  else 
    match descr.dependencyKind with 
    | .portSource   | .portEffect => forPorts descr
    | .actionSource | .actionEffect => forActions descr
where
  forEmpty (descr : InjCoeGenDescription) : MacroM Command := do 
    `(
      @[reducible] instance : $(← descr.injCoeType) where
        coe := (·.casesOn)
        inv _ := none
    )
  forPorts (descr : InjCoeGenDescription) : MacroM Command := do
    let sumTerms ← descr.sumTerms
    let mut invSrcTerms := sumTerms
    let mut invDstTerms ← (← descr.sourceTerms).mapM fun term => `(some $term)
    unless descr.isComplete do
      invSrcTerms := invSrcTerms.push (← `(_))
      invDstTerms := invDstTerms.push (← `(Option.none))
    `(
      @[reducible] instance : $(← descr.injCoeType) where
        coe $[| $(← descr.sourceTerms) => $sumTerms]*
        inv $[| $invSrcTerms => $invDstTerms]*
    )
  forActions (descr : InjCoeGenDescription) : MacroM Command := do
    let coeDstIdents ← descr.sourceTerms
    let mut invSrcTerms : Array Term ← descr.sourceTerms
    let mut invDstTerms : Array Term ← (← descr.sourceTerms).mapM fun ident => `(some $ident)
    unless descr.isComplete do 
      invSrcTerms := invSrcTerms.push (← `(_))
      invDstTerms := invDstTerms.push (← `(Option.none))
    `(
      @[reducible] instance : $(← descr.injCoeType) where
        coe $[| $(← descr.sourceTerms) => $coeDstIdents]*
        inv $[| $invSrcTerms => $invDstTerms]*
    )

def Reactor.InterfaceKind.allCases : Array Reactor.InterfaceKind :=
  #[.inputs, .outputs, .actions, .state]

def Reactor.InterfaceKind.name : Reactor.InterfaceKind → Name
  | .inputs  => `Input
  | .outputs => `Output
  | .actions => `Action
  | .state   => `State

def ReactorDecl.genInterfaceSchemes (decl : ReactorDecl) (ns : Ident) : MacroM (Array Command) :=
  Reactor.InterfaceKind.allCases.mapM fun kind =>
    let interface := decl.interfaces kind
    interface.genInterfaceScheme <| mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ kind.name)

def ReactorDecl.genReactionDependencyEnums (decl : ReactorDecl) (ns : Ident) : MacroM (Array Command) := do
  decl.reactions.enumerate.concatMapM fun ⟨idx, rcn⟩ => do
    let rcnNs := mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ s!"Reaction{idx}")
    rcn.genDependencyEnums rcnNs

def ReactorDecl.genReactorScheme (decl : ReactorDecl) (ns : Ident) : MacroM Command := do
  let mkNamespacedIdent name := mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ name)
  let classesEnumIdent := mkIdentFrom ns (ns.getId ++ `Class)
  let nestedEnumIdent := mkNamespacedIdent `Nested
  let namespacedNestedIds := decl.nested.ids.map fun id => mkIdentFrom id (nestedEnumIdent.getId ++ id.getId)
  let classes := decl.nested.values.map fun «class» => mkIdentFrom «class» (classesEnumIdent.getId ++ «class».getId)
  `(
    inductive $nestedEnumIdent $[| $(decl.nested.ids):ident]* deriving DecidableEq
    abbrev $(mkNamespacedIdent `scheme) : Reactor.Scheme $classesEnumIdent where
      interface -- TODO: Use `Reactor.InterfaceKind.name` for this.
        | .inputs  => $(mkIdent `Input.scheme)
        | .outputs => $(mkIdent `Output.scheme)
        | .actions => $(mkIdent `Action.scheme)
        | .state   => $(mkIdent `State.scheme)
      children := $nestedEnumIdent
      «class» child := match child with $[| $namespacedNestedIds => $classes]*
  )  

def GraphDecl.genClassesEnum (decl : GraphDecl) : MacroM Command := do
  let enumIdent := mkIdentFrom decl.name (decl.name.getId ++ `Class)
  `(inductive $enumIdent $[| $(decl.reactorNames):ident]*)

def GraphDecl.genGraphInstance (decl : GraphDecl) : MacroM Command := do
  let classEnumIdent := mkIdentFrom decl.name (decl.name.getId ++ `Class)
  let classes := decl.reactorNames.map fun reactorName => mkIdentFrom reactorName (decl.name.getId ++ `Class ++ reactorName.getId)
  let classSchemes := decl.reactorNames.map fun reactorName => mkIdentFrom reactorName (decl.name.getId ++ reactorName.getId ++ `scheme)
  `(
    abbrev $decl.name : Network.Graph where
    classes := $classEnumIdent
    root := $(decl.mainReactorIdent!)
    schemes $[| $classes => $classSchemes]*
  )

def GraphDecl.genInjectiveCoes (decl : GraphDecl) : MacroM (Array Command) :=
  decl.reactors.concatMapM fun rtr =>
    rtr.reactions.enumerate.concatMapM fun ⟨idx, rcn⟩ =>
      ReactionDecl.DependencyKind.allCases.mapM fun kind => do
        let ids := rcn.dependencies kind
        InjCoeGenDescription.genInjectiveCoe {
          dependencyKind := kind
          ids := ids
          graphIdent := decl.name
          noNsReactorIdent := rtr.name
          reactionIdx := idx
          isComplete := ids.size = (← decl.numDependencies rtr.name.getId kind)
        }

def GraphDecl.genInterfaceSchemes (decl : GraphDecl) : MacroM (Array Command) :=
  decl.reactors.concatMapM (·.genInterfaceSchemes decl.name)

def GraphDecl.genReactorSchemes (decl : GraphDecl) : MacroM (Array Command) :=
  decl.reactors.mapM (·.genReactorScheme decl.name)

def GraphDecl.genReactionDependencyEnums (decl : GraphDecl) : MacroM (Array Command) := do
  decl.reactors.concatMapM (·.genReactionDependencyEnums decl.name)

macro "gen_graph" graph:graph_decl : command => do
  let graph ← GraphDecl.fromSyntax graph
  return mkNullNode <|
    (← graph.genInterfaceSchemes) ++ 
    [← graph.genClassesEnum] ++
    (← graph.genReactorSchemes) ++
    [← graph.genGraphInstance] ++
    (← graph.genReactionDependencyEnums) ++
    (← graph.genInjectiveCoes)