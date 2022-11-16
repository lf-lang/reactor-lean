import Runtime.Reaction.Monad

namespace Reaction

inductive Kind 
  | pure
  | impure

abbrev Kind.monad : Kind → (Type → Type)
  | .pure => Id
  | .impure => IO

instance {kind : Kind} : Monad kind.monad :=
  match kind with | .pure | .impure => inferInstance

inductive Trigger (Port Action Timer : Type)
  | startup
  | shutdown
  | port (p : Port)
  | action (a : Action)
  | timer (t : Timer)

structure _root_.Reaction where
  kind          : Kind
  portSources   : Interface.Scheme
  portEffects   : Interface.Scheme
  actionSources : Interface.Scheme
  actionEffects : Interface.Scheme
  state         : Interface.Scheme
  params        : Interface.Scheme
  timers        : Type
  triggers      : Array (Trigger portSources.vars actionSources.vars timers)
  body          : ReactionT portSources portEffects actionSources actionEffects state params kind.monad Unit

abbrev inputType (rcn : Reaction) :=
  ReactionT.Input rcn.portSources rcn.actionSources rcn.state rcn.params

abbrev outputType (rcn : Reaction) :=
  ReactionT.Output rcn.portEffects rcn.actionEffects rcn.state 

abbrev bodyType (rcn : Reaction) :=
  ReactionT rcn.portSources rcn.portEffects rcn.actionSources rcn.actionEffects rcn.state rcn.params rcn.kind.monad Unit

def run (rcn : Reaction) (input : rcn.inputType) := 
  Prod.fst <$> rcn.body input

end Reaction