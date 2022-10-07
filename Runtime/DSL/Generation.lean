import Runtime.DSL.Syntax
import Lean
open Lean Macro

def InterfaceDecl.genInterfaceScheme (decl : InterfaceDecl) (name : Ident) : MacroM Command := 
  let schemeIdent := mkIdentFrom name (name.getId ++ `scheme)
  let types := decl.values
  `(
    inductive $name $[| $(decl.ids):ident]* deriving DecidableEq
    abbrev $schemeIdent : Interface.Scheme where
      vars := $name
      type var := match var with $[| $(decl.ids) => $types]*
  )

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