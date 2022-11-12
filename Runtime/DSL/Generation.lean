import Runtime.DSL.Syntax
import Runtime.DSL.Extensions
import Lean
open Lean Macro

def InterfaceVar.genDefaultValue (var : InterfaceVar) : MacroM Term := do
  match var.default with
  | some default => `(($default : $(var.value)))
  | none => `(none)

def InterfaceDecl.genInterfaceScheme (decl : InterfaceDecl) (name : Ident) (optionalTypeWhenNoDefault : Bool := false) : MacroM Command := do
  let schemeIdent := mkIdentFrom name (name.getId ++ `scheme)
  let types ← decl.mapM fun ⟨_, type, default⟩ => do
    match optionalTypeWhenNoDefault, default with
    | true, none => `(Option ($type))
    | _,    _    => return type
  `(
    inductive $name $[| $(decl.ids):ident]* deriving DecidableEq
    abbrev $schemeIdent : Interface.Scheme where
      vars := $name
      type var := match var with $[| $(decl.ids) => $types]*
  )

def TriggerDecl.genTriggers (decl : TriggerDecl) : MacroM (Array Term) := do
  let «ports» ← decl.ports.mapM fun port => `(.port .$port)
  let «actions» ← decl.actions.mapM fun action => `(.action .$action)
  let «timers» ← decl.timers.mapM fun timer => `(.timer .$timer)
  let «metas» ← decl.meta.mapM fun m => do
    match m.getId with
    | `startup => `(.startup)
    | `shutdown => `(.shutdown)
    | invalid => Macro.throwError s!"TriggerDecl.genTriggers: Invalid meta trigger '{invalid}'"
  return «ports» ++ «actions» ++ «timers» ++ «metas»

def ReactionDecl.DependencyKind.name : ReactionDecl.DependencyKind → Name
  | .portSource   => `PortSource
  | .portEffect   => `PortEffect
  | .actionSource => `ActionSource
  | .actionEffect => `ActionEffect

def ReactionDecl.DependencyKind.injCoeTarget (graphIdent className : Ident) : ReactionDecl.DependencyKind → MacroM Term 
  | .portSource                   => `((@Network.Graph.Class.reactionInputScheme $graphIdent .$className |>.vars))
  | .portEffect                   => `((@Network.Graph.Class.reactionOutputScheme $graphIdent .$className |>.vars))
  | .actionSource | .actionEffect => `((@Network.Graph.Class.interface $graphIdent .$className .actions |>.vars))

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
      «body» := open $ns $reactorName $(mkIdent reactionName) 
                     $(mkIdent `PortSource) $(mkIdent `PortEffect) 
                     $(mkIdent `ActionSource) $(mkIdent `ActionEffect) 
                     $(mkIdent `State) $(mkIdent `Parameter) $(mkIdent `ReactionM) 
                     in do $(decl.body)
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
    | .str (.str .anonymous rtr) l => `(.inr ⟨⟨.$(mkIdent rtr)⟩, .$(mkIdent l)⟩)
    | _                            => throwUnsupported 

def InjCoeGenDescription.genInjectiveCoe (descr : InjCoeGenDescription) : MacroM Command := do
  match descr.dependencyKind with 
    | .portSource   | .portEffect => forPorts descr
    | .actionSource | .actionEffect => forActions descr
where
  forPorts (descr : InjCoeGenDescription) : MacroM Command := do
    let sumTerms ← descr.sumTerms
    let mut invSrcTerms := sumTerms
    let mut invDstTerms ← (← descr.ids.dotted).mapM fun term => `(some $term)
    unless descr.isComplete do
      invSrcTerms := invSrcTerms.push (← `(_))
      invDstTerms := invDstTerms.push (← `(Option.none))
    `(
      @[reducible] instance : $(← descr.injCoeType) where
        coe i := match i with $[| $(← descr.ids.dotted) => $sumTerms]*
        inv i := match i with $[| $invSrcTerms => $invDstTerms]*
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
        coe i := match i with $[| $(← descr.ids.dotted) => $coeDstIdents]*
        inv i := match i with $[| $invSrcTerms => $invDstTerms]*
    )

def TimerDecl.genTimer (decl : TimerDecl) : MacroM Term := do
  `({ «offset» := $(decl.offset), «period» := $(mkIdent `Timer.Period.of) $(decl.period) })

def Reactor.InterfaceKind.name : Reactor.InterfaceKind → Name
  | .inputs  => `Input
  | .outputs => `Output
  | .actions => `Action
  | .state   => `State
  | .params  => `Parameter

def ReactorDecl.genInterfaceSchemes (decl : ReactorDecl) (ns : Ident) : MacroM (Array Command) :=
  Reactor.InterfaceKind.allCases.mapM fun kind =>
    let interface := decl.interfaces kind
    let ident := mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ kind.name)
    let optionalTypeWhenNoDefault := match kind with | .state | .params => true | _ => false
    interface.genInterfaceScheme ident optionalTypeWhenNoDefault

def ReactorDecl.genReactionDependencyEnums (decl : ReactorDecl) (ns : Ident) : MacroM (Array Command) := do
  decl.reactions.enumerate.concatMapM fun ⟨idx, rcn⟩ => do
    let rcnNs := mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ s!"Reaction{idx}")
    rcn.genDependencyEnums rcnNs

instance : Quote Reactor.InterfaceKind where
  quote
    | .inputs  => mkIdent `Reactor.InterfaceKind.inputs
    | .outputs => mkIdent `Reactor.InterfaceKind.outputs
    | .actions => mkIdent `Reactor.InterfaceKind.actions
    | .state   => mkIdent `Reactor.InterfaceKind.state
    | .params  => mkIdent `Reactor.InterfaceKind.params

def ReactorDecl.genReactorScheme (decl : ReactorDecl) (ns : Ident) : MacroM Command := do
  let mkNamespacedIdent name := mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ name)
  let classesEnumIdent := mkIdentFrom ns (ns.getId ++ `Class)
  let nestedEnumIdent := mkNamespacedIdent `Nested
  let timerEnumIdent := mkNamespacedIdent `Timer
  let timerIdents := decl.timers.map (·.name)
  let dottedClasses ← decl.nested.map (·.class) |>.dotted
  let interfaces := Reactor.InterfaceKind.allCases.map (quote ·)
  let interfaceSchemeIdents := Reactor.InterfaceKind.allCases.map fun i => mkIdent <| i.name ++ `scheme
  `(
    inductive $nestedEnumIdent $[| $(decl.nested.map (·.id)):ident]* deriving DecidableEq
    inductive $timerEnumIdent $[| $timerIdents:ident]* deriving DecidableEq
    abbrev $(mkNamespacedIdent `scheme) : Reactor.Scheme $classesEnumIdent where
      interface $[| $interfaces => $interfaceSchemeIdents]*
      «timers» := $(mkIdent `Timer)
      children := $nestedEnumIdent
      «class» child := match child with $[| $(← decl.nested.map (·.id) |>.dotted) => $dottedClasses]*
  )  

def ReactorDecl.genReactionInstances (decl : ReactorDecl) (ns : Ident) : MacroM Term := do
  let instances ← decl.reactions.enumerate.mapM fun ⟨idx, rcn⟩ => rcn.genReactionInstance ns decl.name s!"Reaction{idx}"
  `(#[ $[$instances],* ])

def ReactorDecl.genConnections (decl : ReactorDecl) (isComplete : Bool) : MacroM Term := do
  let mut lhs ← inputTerms decl
  let mut rhs ← outputTerms decl
  unless isComplete do
    lhs := lhs.push (← `(_))
    rhs := rhs.push (← `(none))
  `(
    { 
      source := fun subport => match subport with $[| $lhs => $rhs ]* 
      -- TODO: Find out why the default argument on `Connections` doesn't work here.
      eqType := sorry
    }
  )
where 
  inputTerms (decl : ReactorDecl) : MacroM (Array Term) := do 
    (← decl.connections.valueIdents).mapM fun id => do
      match id.getId with
      | .str (.str .anonymous rtr) p => `(⟨⟨.$(mkIdent rtr)⟩, .$(mkIdent p)⟩)
      | _                            => throwUnsupported 
  outputTerms (decl : ReactorDecl) : MacroM (Array Term) :=
    decl.connections.ids.mapM fun id => do
      match id.getId with
      | .str (.str .anonymous rtr) p => `(some ⟨⟨.$(mkIdent rtr)⟩, .$(mkIdent p)⟩)
      | _                            => throwUnsupported 

def ReactorDecl.genStateInterface (decl : ReactorDecl) : MacroM Term := do 
  let dottedIds ← decl.interfaces .state |>.map (·.id) |>.dotted
  let values ← decl.interfaces .state |>.mapM (·.genDefaultValue)
  `(fun var => match var with $[| $dottedIds => $values]* )

def ReactorDecl.genParamInterface (decl : ReactorDecl) : MacroM Term := do 
  let paramIdents := decl.interfaces .params |>.map (·.id)
  `(fun var => match var with $[| $(← paramIdents.dotted) => $paramIdents]*)

def ReactorDecl.genTimers (decl : ReactorDecl) : MacroM Term := do 
  let timerIdents ← decl.timers.map (·.name) |>.dotted
  let «timers» ← decl.timers.mapM (·.genTimer)
  `(fun var => match var with $[| $timerIdents => $«timers»]*)

def ReactorDecl.genReactorInstance (decl : ReactorDecl) : MacroM Term := do 
  `({
      interface := fun
        | .state => $(← decl.genStateInterface)
        | .params => $(← decl.genParamInterface)
        | .inputs | .outputs | .actions => Interface?.empty 
      timer := $(← decl.genTimers)
  })

def NetworkDecl.genClassesEnum (decl : NetworkDecl) : MacroM Command := do
  let enumIdent := mkIdentFrom decl.namespaceIdent (decl.namespaceIdent.getId ++ `Class)
  `(inductive $enumIdent $[| $(decl.reactorNames):ident]* deriving DecidableEq)

def NetworkDecl.genGraphInstance (decl : NetworkDecl) : MacroM Command := do
  let classEnumIdent := mkIdentFrom decl.namespaceIdent (decl.namespaceIdent.getId ++ `Class)
  let classSchemes := decl.reactorNames.map fun reactorName => mkIdentFrom reactorName (decl.namespaceIdent.getId ++ reactorName.getId ++ `scheme)
  `(
    abbrev $decl.graphIdent : Network.Graph where
    classes := $classEnumIdent
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

-- For user proofs.
def NetworkDecl.genReactionDefs (decl : NetworkDecl) : MacroM (Array Command) :=
  decl.reactors.mapM fun rtr => do
    let rcns ← rtr.genReactionInstances decl.namespaceIdent
    let defName := mkIdent <| decl.namespaceIdent.getId ++ rtr.name.getId ++ `reactions
    let rcnType : Term ← `(@Network.Graph.Class.reactionType $(mkIdent <| decl.namespaceIdent.getId ++ `graph) .$(mkIdent rtr.name.getId))
    `(def $defName : Array $rcnType := $rcns)

def NetworkDecl.genReactionInstanceMap (decl : NetworkDecl) : MacroM Term := do
  let dottedClasses ← decl.reactors.map (·.name) |>.dotted 
  let instanceArrays ← decl.reactors.mapM (·.genReactionInstances decl.namespaceIdent)
  `(fun $[| $dottedClasses => $instanceArrays]*)

def NetworkDecl.genConnectionsMap (decl : NetworkDecl) : MacroM Term := do
  let dottedClasses ← decl.reactors.map (·.name) |>.dotted 
  let connectionsMaps ← decl.reactors.mapM fun rtr => do
    let isComplete := rtr.connections.size = (← decl.numNested rtr.name.getId .inputs)
    rtr.genConnections isComplete
  `(fun $[| $dottedClasses => $connectionsMaps]*)

def NetworkDecl.genNetworkInstance (decl : NetworkDecl) : MacroM Command := do `(
  abbrev $(decl.networkIdent) : Network where
    toGraph := $(decl.graphIdent)
    root := $(← decl.mainReactorClass)
    «reactions» := $(← decl.genReactionInstanceMap)
    «connections» := $(← decl.genConnectionsMap)
)

-- Each instance generates its own default parameter defs as well as the the parameter defs for its children.

partial def NetworkDecl.genDefaultParameterDefs (decl : NetworkDecl) : MacroM (Array Command) := do 
  let ns := mkIdent (decl.namespaceIdent.getId ++ `Parameters.Default)
  (← decl.instancePaths).concatMapM fun ⟨path, «class»⟩ => do
    let pathName := nameForInstancePath path
    let rtrDecl ← decl.reactorWithName «class»
    (rtrDecl.interfaces .params).mapM fun param => do
      `(def $(mkIdent <| ns.getId ++ pathName ++ param.id.getId) := $(param.default.get!)) 
where 
  nameForInstancePath (path : Array Name) : Name :=
    .mkSimple <| path.foldl (s!"{·}_{·}") ""

partial def NetworkDecl.genRootParameterDefs (decl : NetworkDecl) : MacroM (Array Command) := do 
  let ns := mkIdent (decl.namespaceIdent.getId ++ `Parameters)
  (← decl.mainReactor).interfaces .params |>.mapM fun param => 
    `(def $(mkIdent <| ns.getId ++ "" ++ param.id.getId) := $(param.default.get!))

partial def NetworkDecl.genParameterDefs (decl : NetworkDecl) : MacroM (Array Command) := do 
  let ns := mkIdent (decl.namespaceIdent.getId ++ `Parameters)
  (← decl.instancePaths).concatMapM fun ⟨path, «class»⟩ => do
    let rtrDecl ← decl.reactorWithName «class»
    rtrDecl.nested.concatMapM fun «nested» => do
      let nestedPath := path.push «nested».id.getId
      let nestedDecl ← decl.reactorWithName «nested».class.getId
      nestedDecl.interfaces .params |>.mapM fun param => do
        let properDef := mkIdent <| ns.getId ++ (nameForInstancePath nestedPath) ++ param.id.getId
        match ← «nested».parameterValue? param.id.getId with
        | none => 
          let defaultDef := mkIdent <| ns.getId ++ `Default ++ (nameForInstancePath nestedPath) ++ param.id.getId
          return ← `(def $properDef := $defaultDef)
        | some paramExpr =>
          -- Only open the parent's parameter namespace if it has parameters.
          if rtrDecl.interfaces .params |>.isEmpty then 
            return ← `(def $properDef := $paramExpr)
          else
            let parentParamNs := mkIdent <| ns.getId ++ (nameForInstancePath path)
            return ← `(def $properDef := open $parentParamNs:ident in $paramExpr)
where 
  nameForInstancePath (path : Array Name) : Name :=
    .mkSimple <| path.foldl (s!"{·}_{·}") ""

partial def NetworkDecl.genExecutableInstance (decl : NetworkDecl) : MacroM Command := do 
  let executableIdent := mkIdentFrom decl.namespaceIdent (decl.namespaceIdent.getId ++ `executable)
  let instancesIdent := mkIdent `instances
  let ⟨instanceIDs, rhs⟩ := Array.unzip <| ← (← decl.instancePaths).mapM fun ⟨path, «class»⟩ => do
    let id ← pathToID path
    let ns := decl.namespaceIdent.getId ++ `Parameters ++ (nameForInstancePath path)
    let rtrDecl ← decl.reactorWithName «class»
    -- Only open the parameter namespace if the reactor has parameters.
    let value ← do 
      if rtrDecl.interfaces .params |>.isEmpty 
      then rtrDecl.genReactorInstance
      else `(open $(mkIdent ns):ident in $(← rtrDecl.genReactorInstance))
    let timerNames ← rtrDecl.timers.map (·.name) |>.dotted
    let initialTimerEvents ← timerNames.mapM fun timerName => `( 
        match ($instancesIdent $id).timer $timerName |>.initalFiring with
        | none => none
        | some t => some <| .timer t { «reactor» := $id, timer := $timerName }
      )
    return (id, value, initialTimerEvents) 
  let ⟨instanceValues, initalTimerEvents⟩ := rhs.unzip
  `(
    def $executableIdent (physicalOffset : Duration) : $(mkIdent `Network.Executable) $(decl.networkIdent) where
      physicalOffset := physicalOffset
      reactors := $instancesIdent
      queue := #[ $[$(initalTimerEvents.concatMap id)],* ].filterMap id
      lawfulQueue := sorry
    where 
      $instancesIdent:ident : (id : $(mkIdent `Network.ReactorId) $(decl.networkIdent)) → $(mkIdent `Reactor) id.class 
        $[| $instanceIDs => $instanceValues]*
  )
where
  nameForInstancePath (path : Array Name) : Name :=
    .mkSimple <| path.foldl (s!"{·}_{·}") ""
  pathToID (path : Array Name) : MacroM Term := do
    if path.isEmpty 
    then `(.nil)
    else `(.cons ⟨.$(mkIdent path[0]!)⟩ <| $(← pathToID path[1:]))

-- TODO: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/mkNullNode
macro network:network_decl : command => do
  let network ← NetworkDecl.fromSyntax network
  let commands := mkNullNode <|
    (← network.genInterfaceSchemes) ++ 
    [← network.genClassesEnum] ++
    (← network.genReactorSchemes) ++
    [← network.genGraphInstance] ++
    (← network.genReactionDependencyEnums) ++
    (← network.genInjectiveCoes) ++
    [← network.genNetworkInstance] ++
    (← network.genDefaultParameterDefs) ++
    (← network.genRootParameterDefs) ++
    (← network.genParameterDefs) ++
    [← network.genExecutableInstance] ++
    (← network.genReactionDefs)
  return ⟨commands⟩
