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
  | .portSource                   => `((Network.Graph.reactionInputScheme $graphIdent .$className |>.vars))
  | .portEffect                   => `((Network.Graph.reactionOutputScheme $graphIdent .$className |>.vars))
  | .actionSource | .actionEffect => `((Network.Graph.schemes $graphIdent .$className |>.interface .actions |>.vars))

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
    | .str (.str .anonymous rtr) l => `(.inr ⟨.$(mkIdent rtr), .$(mkIdent l)⟩)
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
  `({ «offset» := $(decl.offset), «period» := $(decl.period) })

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
  let dottedClasses ← (← decl.nested.valueIdents).dotted
  let interfaces := Reactor.InterfaceKind.allCases.map (quote ·)
  let interfaceSchemeIdents := Reactor.InterfaceKind.allCases.map fun i => mkIdent <| i.name ++ `scheme
  `(
    inductive $nestedEnumIdent $[| $(decl.nested.ids):ident]* deriving DecidableEq
    inductive $timerEnumIdent $[| $timerIdents:ident]* deriving DecidableEq
    abbrev $(mkNamespacedIdent `scheme) : Reactor.Scheme $classesEnumIdent where
      interface $[| $interfaces => $interfaceSchemeIdents]*
      «timers» := $(mkIdent `Timer)
      children := $nestedEnumIdent
      «class» child := match child with $[| $(← decl.nested.ids.dotted) => $dottedClasses]*
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
      eqType := by intro input output; cases input <;> cases output <;> rename_i rtr₁ prt₁ rtr₂ prt₂ <;> cases rtr₁ <;> cases prt₁ <;> cases rtr₂ <;> cases prt₂ <;> simp
    }
  )
where 
  inputTerms (decl : ReactorDecl) : MacroM (Array Term) := 
    decl.connections.ids.mapM fun id => do
      match id.getId with
      | .str (.str .anonymous rtr) p => `(⟨.$(mkIdent rtr), .$(mkIdent p)⟩)
      | _                            => throwUnsupported 
  outputTerms (decl : ReactorDecl) : MacroM (Array Term) := do
    (← decl.connections.valueIdents).mapM fun id => do
      match id.getId with
      | .str (.str .anonymous rtr) p => `(some ⟨.$(mkIdent rtr), .$(mkIdent p)⟩)
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
    root := $(← decl.mainReactorClass)
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
    «reactions» := $(← decl.genReactionInstanceMap)
    «connections» := $(← decl.genConnectionsMap)
)

partial def NetworkDecl.genParameterDefs (decl : NetworkDecl) : MacroM (Array Command) := do 
  let ns := mkIdent (decl.namespaceIdent.getId ++ `Parameters)
  (← decl.instancePaths).concatMapM fun ⟨path, «class»⟩ => do
    let pathName := nameForInstancePath path
    let parentName := pathName |>.getPrefix
    let parentIdent := mkIdent (decl.namespaceIdent.getId ++ `Parameters ++ parentName)
    let rtrDecl ← decl.reactorWithName «class»
    (rtrDecl.interfaces .params).mapM fun param => do
      -- TODO: the value of the defintion actually depends on whether the parent instance specified 
      -- a value for the given parameter at instantiation. right now we don't have the syntax
      -- for that, so here we're just using the default value defined by the child reactor
      --
      -- IMPORTANT: If the parent does not specify a value for the given parameter at instantiation
      -- we need to remove the `open ... in`. Otherwise we would leak the parameters of the
      -- parent reactor into the default-value declaration of the child reactor.
      `(
        def $(mkIdent <| ns.getId ++ pathName ++ param.id.getId) := 
          /-open $parentIdent:ident in-/ $(param.default.get!)
      ) 
where 
  nameForInstancePath (path : Array Name) : Name :=
    .mkSimple <| path.foldl (s!"{·}_{·}") ""

partial def NetworkDecl.genExecutableInstance (decl : NetworkDecl) : MacroM Command := do 
  let executableIdent := mkIdentFrom decl.namespaceIdent (decl.namespaceIdent.getId ++ `executable)
  let ⟨instanceIDs, rhs⟩ := Array.unzip <| ← (← decl.instancePaths).mapM fun ⟨path, «class»⟩ => do
    let id ← pathToID path
    let ns := decl.namespaceIdent.getId ++ `Parameters ++ (nameForInstancePath path)
    let rtrDecl ← decl.reactorWithName «class»
    let value ← `(open $(mkIdent ns):ident in $(← rtrDecl.genReactorInstance))
    let timerNames ← rtrDecl.timers.map (·.name) |>.dotted
    let initialTimerEvents ← timerNames.mapM fun timerName => `( 
        match (instances $id).timer $timerName |>.initalFiring with
        | none => none
        | some t => some <| .timer { 
            id := { «reactor» := $id, timer := $timerName }
            time := t
          }
      )
    return (id, value, initialTimerEvents) 
  let ⟨instanceValues, initalTimerEvents⟩ := rhs.unzip
  `(
    -- HACK: When there are no parameters used in the network, 
    --  the namespace `LF.Parameters` doesn't exist, but we still open it below.
    inductive $(mkIdent <| decl.namespaceIdent.getId ++ `Parameters) 

    def $executableIdent (physicalOffset : Duration) : $(mkIdent `Network.Executable) $(decl.networkIdent) where
      physicalOffset := physicalOffset
      reactors := instances
      queue := #[ $[$(initalTimerEvents.concatMap id)],* ].filterMap id
    where 
      instances : (id : $(mkIdent `Network.ReactorID) $(decl.networkIdent)) → $(mkIdent `Network.Reactor) ($(decl.networkIdent).scheme id) 
        $[| $instanceIDs => $instanceValues]*
  )
where
  nameForInstancePath (path : Array Name) : Name :=
    .mkSimple <| path.foldl (s!"{·}_{·}") ""
  pathToID (path : Array Name) : MacroM Term := do
    if path.isEmpty 
    then `(.nil)
    else `(.cons .$(mkIdent path[0]!) <| $(← pathToID path[1:]))

macro network:network_decl : command => do
  let network ← NetworkDecl.fromSyntax network
  return mkNullNode <|
    (← network.genInterfaceSchemes) ++ 
    [← network.genClassesEnum] ++
    (← network.genReactorSchemes) ++
    [← network.genGraphInstance] ++
    (← network.genReactionDependencyEnums) ++
    (← network.genInjectiveCoes) ++
    [← network.genNetworkInstance] ++
    (← network.genParameterDefs) ++
    [← network.genExecutableInstance]
