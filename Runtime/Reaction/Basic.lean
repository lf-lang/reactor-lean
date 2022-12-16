import Runtime.Reaction.Monad

namespace Reaction

/--
A classifier to differentiate reactions which can use IO from those which can't. A reaction that can
use IO is called "impure" in this context.
-/
inductive Kind
  | pure
  | impure

/--
Depending on a reaction's kind, its body run's in a different monad. This map associates with each
reaction kind the monad in which the body should run.
-/
abbrev Kind.monad : Kind → (Type → Type)
  | pure => Id
  | impure => IO

instance {kind : Kind} : Monad kind.monad :=
  match kind with | .pure | .impure => inferInstance

/--
A reaction `Trigger` identifies an event which should cause a reaction to fire. Reactions explictly
declare their triggers and thus the events which should cause them to fire. The different kinds of
triggers are active under the following conditions (according to `Execution.Executable.triggers`):

* `startup`: at tag (0, 0)
* `shutdown`: at the last tag at which a given reactor system executes
* `port p`: when the port with name `p` is present
* `action a`: when the action with name `a` is present
* `timer t`: when the timer with name `t` fires
-/
inductive Trigger (Port Action Timer : Type)
  | startup
  | shutdown
  | port (p : Port)
  | action (a : Action)
  | timer (t : Timer)

/--
A reaction consists chiefly of two parts:
* a `body` which is a map from an "input context" to and "output context" (cf. `ReactionT`).
* a list of `triggers` which determine under which conditions the reaction's body should be run.

All remaining fields capture the entirety of the reaction's dependencies and are used to determine
the exact type of the reaction's body and triggers.
-/
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

/-- The type of the "context" passed into a reaction body upon execution. -/
abbrev inputType (rcn : Reaction) :=
  ReactionT.Input rcn.portSources rcn.actionSources rcn.state rcn.params

/-- The type of the "context" returned from a reaction body after execution. -/
abbrev outputType (rcn : Reaction) :=
  ReactionT.Output rcn.portEffects rcn.actionEffects rcn.state

/-- The type of the given reaction's body. -/
abbrev bodyType (rcn : Reaction) :=
  ReactionT rcn.portSources rcn.portEffects rcn.actionSources rcn.actionEffects rcn.state rcn.params rcn.kind.monad Unit

/--
Runs a given reaction's body on a given "input context" and returns only the "output context".
-/
def run (rcn : Reaction) (input : rcn.inputType) :=
  Prod.fst <$> rcn.body input

end Reaction
