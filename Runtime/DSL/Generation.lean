import Runtime.DSL.Syntax
import Runtime.DSL.Extensions
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

def TriggerDecl.genTriggers (decl : TriggerDecl) : MacroM (Array Term) := do
  let «ports» ← decl.ports.mapM fun port => `(.port $port)
  let «actions» ← decl.actions.mapM fun action => `(.action $action)
  let «metas» ← decl.meta.mapM fun m => do
    match m.getId with
    | `startup => `(.startup)
    | `shutdown => `(.shutdown)
    | invalid => Macro.throwError s!"TriggerDecl.genTriggers: Invalid meta trigger '{invalid}'"
  return «ports» ++ «actions» ++ «metas»

def ReactionDecl.DependencyKind.name : ReactionDecl.DependencyKind → Name
  | .portSource   => `PortSource
  | .portEffect   => `PortEffect
  | .actionSource => `ActionSource
  | .actionEffect => `ActionEffect

def ReactionDecl.DependencyKind.injCoeTarget (graphIdent className : Ident) : ReactionDecl.DependencyKind → MacroM Term 
  | .portSource                  => `((Network.Graph.reactionInputScheme $graphIdent .$className |>.vars))
  | .portEffect                  => `((Network.Graph.reactionOutputScheme $graphIdent .$className |>.vars))
  | .actionSource |.actionEffect => `((Network.Graph.schemes $graphIdent .$className |>.interface .actions |>.vars))

def ReactionDecl.genDependencyEnums (decl : ReactionDecl) (ns : Ident) : MacroM (Array Command) := do
  ReactionDecl.DependencyKind.allCases.mapM fun kind =>
    let enumIdent := mkIdentFrom ns (ns.getId ++ kind.name)
    let ids := decl.dependencies kind
    `(inductive $enumIdent $[| $ids:ident]* deriving DecidableEq)

def ReactionDecl.genTriggers (decl : ReactionDecl) : MacroM Term := do
  `(#[ $[$(← decl.triggers.genTriggers)],* ])

def ReactionDecl.genReactionInstance (decl : ReactionDecl) (ns reactorName : Ident) (reactionName : Name) : MacroM Term := do
  let reactionIdent := mkIdentFrom reactorName (ns.getId ++ reactorName.getId ++ reactionName) 
  `({
      «portSources»   := $(mkIdentFrom reactionIdent (reactionIdent.getId ++ `PortSource))
      «portEffects»   := $(mkIdentFrom reactionIdent (reactionIdent.getId ++ `PortEffect))
      «actionSources» := $(mkIdentFrom reactionIdent (reactionIdent.getId ++ `ActionSource))
      «actionEffects» := $(mkIdentFrom reactionIdent (reactionIdent.getId ++ `ActionEffect))
      «triggers»      := $(← decl.genTriggers)
      «body» := open $ns $reactorName $(mkIdent reactionName) PortSource PortEffect ActionSource ActionEffect State ReactionM in do $(decl.body)
  })

structure InjCoeGenDescription where
  dependencyKind : ReactionDecl.DependencyKind
  ids : Array Ident
  ns : Ident
  graphName : Ident
  reactorName : Ident
  reactionIdx : Nat
  isComplete : Bool

def InjCoeGenDescription.sourceTypeIdent (descr : InjCoeGenDescription) :=
  let reactorIdent := mkIdentFrom descr.reactorName <| descr.ns.getId ++ descr.reactorName.getId
  mkIdentFrom reactorIdent (reactorIdent.getId ++ s!"Reaction{descr.reactionIdx}" ++ descr.dependencyKind.name)

def InjCoeGenDescription.targetTypeTerm (descr : InjCoeGenDescription) :=
  descr.dependencyKind.injCoeTarget (mkIdentFrom descr.graphName <| descr.ns.getId ++ descr.graphName.getId) descr.reactorName

def InjCoeGenDescription.injCoeType (descr : InjCoeGenDescription) := do
  `(InjectiveCoe $(descr.sourceTypeIdent) $(← descr.targetTypeTerm))

def InjCoeGenDescription.sumTerms (descr : InjCoeGenDescription) : MacroM (Array Term) := 
  descr.ids.mapM fun id => do
    match id.getId with
    | .str .anonymous l            => `(.inl .$(mkIdent l))
    | .str (.str .anonymous rtr) l => `(.inr ⟨.$(mkIdent rtr), .$(mkIdent l)⟩)
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
    let mut invDstTerms ← (← descr.ids.dotted).mapM fun term => `(some $term)
    unless descr.isComplete do
      invSrcTerms := invSrcTerms.push (← `(_))
      invDstTerms := invDstTerms.push (← `(Option.none))
    `(
      @[reducible] instance : $(← descr.injCoeType) where
        coe $[| $(← descr.ids.dotted) => $sumTerms]*
        inv $[| $invSrcTerms => $invDstTerms]*
    )
  forActions (descr : InjCoeGenDescription) : MacroM Command := do
    let coeDstIdents ← descr.ids.dotted
    let mut invSrcTerms : Array Term ← descr.ids.dotted
    let mut invDstTerms : Array Term ← (← descr.ids.dotted).mapM fun ident => `(some $ident)
    unless descr.isComplete do 
      invSrcTerms := invSrcTerms.push (← `(_))
      invDstTerms := invDstTerms.push (← `(Option.none))
    `(
      @[reducible] instance : $(← descr.injCoeType) where
        coe $[| $(← descr.ids.dotted) => $coeDstIdents]*
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
  let dottedClasses ← (← decl.nested.valueIdents).dotted
  `(
    inductive $nestedEnumIdent $[| $(decl.nested.ids):ident]* deriving DecidableEq
    abbrev $(mkNamespacedIdent `scheme) : Reactor.Scheme $classesEnumIdent where
      interface -- TODO: Use `Reactor.InterfaceKind.name` for this.
        | .inputs  => $(mkIdent `Input.scheme)
        | .outputs => $(mkIdent `Output.scheme)
        | .actions => $(mkIdent `Action.scheme)
        | .state   => $(mkIdent `State.scheme)
      children := $nestedEnumIdent
      «class» child := match child with $[| $(← decl.nested.ids.dotted) => $dottedClasses]*
  )  

def ReactionDecl.genReactionInstances (decl : ReactorDecl) (ns : Ident) : MacroM Term := do
  let instances ← decl.reactions.enumerate.mapM fun ⟨idx, rcn⟩ => rcn.genReactionInstance ns decl.name s!"Reaction{idx}"
  `(#[ $[$instances],* ])

def NetworkDecl.genClassesEnum (decl : NetworkDecl) : MacroM Command := do
  let enumIdent := mkIdentFrom decl.namespaceIdent (decl.namespaceIdent.getId ++ `Class)
  `(inductive $enumIdent $[| $(decl.reactorNames):ident]*)

def NetworkDecl.genGraphInstance (decl : NetworkDecl) : MacroM Command := do
  let classEnumIdent := mkIdentFrom decl.namespaceIdent (decl.namespaceIdent.getId ++ `Class)
  let classSchemes := decl.reactorNames.map fun reactorName => mkIdentFrom reactorName (decl.namespaceIdent.getId ++ reactorName.getId ++ `scheme)
  `(
    abbrev $decl.graphIdent : Network.Graph where
    classes := $classEnumIdent
    root := $(← decl.mainReactorIdent!)
    schemes $[| $(← decl.reactorNames.dotted) => $classSchemes]*
  )

def NetworkDecl.genInjectiveCoes (decl : NetworkDecl) : MacroM (Array Command) :=
  decl.reactors.concatMapM fun rtr =>
    rtr.reactions.enumerate.concatMapM fun ⟨idx, rcn⟩ =>
      ReactionDecl.DependencyKind.allCases.mapM fun kind => do
        let ids := rcn.dependencies kind
        InjCoeGenDescription.genInjectiveCoe {
          dependencyKind := kind
          ids := ids
          ns := decl.namespaceIdent
          graphName := decl.graphName
          reactorName := rtr.name
          reactionIdx := idx
          isComplete := ids.size = (← decl.numDependencies rtr.name.getId kind)
        }

def NetworkDecl.genInterfaceSchemes (decl : NetworkDecl) : MacroM (Array Command) :=
  decl.reactors.concatMapM (·.genInterfaceSchemes decl.namespaceIdent)

def NetworkDecl.genReactorSchemes (decl : NetworkDecl) : MacroM (Array Command) :=
  decl.reactors.mapM (·.genReactorScheme decl.namespaceIdent)

def NetworkDecl.genReactionDependencyEnums (decl : NetworkDecl) : MacroM (Array Command) := do
  decl.reactors.concatMapM (·.genReactionDependencyEnums decl.namespaceIdent)

def NetworkDecl.genReactionInstanceMap (decl : NetworkDecl) : MacroM Term := do
  `(fun _ => sorry
  )

def NetworkDecl.genConnectionsMap (decl : NetworkDecl) : MacroM Term := do
  `(fun _ => sorry
  )

def NetworkDecl.genNetworkInstance (decl : NetworkDecl) : MacroM Command := do `(
  def $(decl.networkIdent) : Network where
    toGraph := $(decl.graphIdent)
    «reactions» := $(← decl.genReactionInstanceMap)
    «connections» := $(← decl.genConnectionsMap)
)

macro network:network_decl : command => do
  let network ← NetworkDecl.fromSyntax network
  return mkNullNode <|
    (← network.genInterfaceSchemes) ++ 
    [← network.genClassesEnum] ++
    (← network.genReactorSchemes) ++
    [← network.genGraphInstance] ++
    (← network.genReactionDependencyEnums) ++
    (← network.genInjectiveCoes) ++
    [← network.genNetworkInstance]