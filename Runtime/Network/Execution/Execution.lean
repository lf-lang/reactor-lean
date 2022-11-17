import Runtime.Network.Execution.Next
import Runtime.Network.Execution.Apply
import Runtime.Network.Execution.Propagate

namespace Network.Executable

open Graph Class

-- TODO?: Refactor this à la `Reaction.Output.LocalValue` and `Reaction.Output.local`.
-- An interface for all ports (local and nested) that can act as sources of reactions of a given reactor.
def reactionInputs (exec : Executable net) (reactor : ReactorId net) : Interface? reactor.class.reactionInputScheme
  | .inl localInput           => exec.interface reactor .inputs localInput
  | .inr ⟨child, childOutput⟩ => Path.reactionInputScheme_right_type_eq_extend_child_type ▸ exec.interface (reactor.extend child) .outputs (Path.extend_class ▸ childOutput)

def fire (exec : Executable net) {reactor : ReactorId net} (reaction : Reaction reactor.class) :=
  reaction.val.run {
    ports          := exec.reactionInputs reactor     |>.restrict
    actions        := exec.interface reactor .actions |>.restrict
    state          := reaction.eqState  ▸ exec.interface reactor .state
    params         := reaction.eqParams ▸ exec.interface reactor .params
    tag            := exec.tag
    physicalOffset := exec.physicalOffset
  }

def fireToIO (exec : Executable net) {reactor : ReactorId net} (reaction : Reaction reactor.class) :=
  toIO <| exec.fire reaction
where
  toIO {α} {kind : Reaction.Kind} : (kind.monad α) → IO α := 
    match kind with | .pure => pure | .impure => id

def triggers (exec : Executable net) {reactor : ReactorId net} (reaction : Reaction reactor.class) : Bool :=
  reaction.val.triggers.any fun trigger =>
    match trigger with
    | .port   port   => exec.reactionInputs reactor                    |>.isPresent (reaction.subPS.coe port)
    | .action action => exec.interface reactor .actions                |>.isPresent (reaction.subAS.coe action)
    | .timer  timer  => exec.timer reactor (reaction.eqTimers ▸ timer) |>.firesAtTag exec.tag
    | .startup       => exec.isStartingUp
    | .shutdown      => exec.state = .shuttingDown

-- Advances the given executable to the state given by `next`.
-- This includes:
-- * advancing the tag
-- * dequeueing events for that tag
-- * clearing all ports
-- * setting actions' values for the given tag
def advance (exec : Executable net) (next : Next net) : Executable net := { exec with
  tag := next.tag
  queue := next.queue
  reactors := fun id => { exec.reactors id with
    interface := fun
      | .inputs | .outputs => Interface?.empty
      | .actions           => next.actions id
      | _                  => exec.interface id _
  }
  lawfulQueue := next.lawfulQueue 
}

def shutdown (exec : Executable net) : Executable net := 
  let next :=
    match exec.nextTime with 
    | none => .empty exec.tag.increment
    | some time => if (time = exec.time) then (Next.for exec exec.time) else (.empty exec.tag.increment)
  { exec.advance next with state := .shuttingDown }

-- Note: We can't separate out a `runInst` function at the moment as `IO` isn't universe polymorphic.
partial def run (exec : Executable net) (topo : Array (ReactionId net)) (reactionIdx : Nat) : IO Unit := do
  match topo[reactionIdx]? with 
  -- This branch is entered whenever we've completed an instantaneous execution.
  | none => 
    match exec.state, exec.nextTime with
    -- The instantaneous execution where the `.shutdown` trigger is active 
    -- has already been executed, so we terminate execution.
    | .shuttingDown, _ => return 
    -- Case 1: 
    -- The last instantaneous execution contained a shutdown request, 
    -- so the next instantaneous execution performs shutdown.
    -- Case 2:
    -- We've reached starvation (there are no more events to be processed), 
    -- so the next instantaneous execution performs shutdown.
    | .stopRequested, _ | .executing, none => exec.shutdown.run topo 0
    -- Execution continues normally at the tag of the next event.
    | .executing, some time => 
      let exec := exec.advance (Next.for exec time)
      IO.sleepUntil exec.absoluteTime
      exec.run topo 0
  -- This branch is entered whenever we're within an instantaneous execution.
  | some reactionId => 
    let reaction := reactionId.reaction
    let mut exec := exec
    if exec.triggers reaction then
      exec := (← exec.fireToIO reaction)
        |> ReactionOutput.fromRaw 
        |> exec.apply 
        |>.propagate reactionId 
    exec.run topo (reactionIdx + 1)

end Network.Executable