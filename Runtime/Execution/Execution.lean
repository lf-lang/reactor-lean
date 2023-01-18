import Runtime.Execution.Next
import Runtime.Execution.Apply
import Runtime.Execution.Propagate
import Runtime.Execution.Triggers

namespace Execution.Executable
open Network Graph Class

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

-- Advances the given executable to the state given by `next`.
-- This includes:
-- * advancing the tag
-- * dequeueing events for that tag
-- * clearing all ports
-- * setting actions' values for the given tag
def advance (exec : Executable net) (next : Next net) : Executable net := { exec with
  tag := next.tag
  queue := next.queue
  toPropagate := #[]
  reactors := fun id => { exec.reactors id with
    timer := next.timers exec id
    interface := fun
      | .inputs  => next.inputs id
      | .actions => next.actions id
      | .outputs => Interface?.empty
      | _        => exec.interface id _
  }
}

theorem advance_tag_strictly_increasing (exec : Executable net) :
  (Next.for exec = some next) → exec.tag < (exec.advance next).tag :=
  Next.for_tag_strictly_monotonic exec

def shutdown (exec : Executable net) (h : exec.state = .shutdownPending) : Executable net :=
  match hn : Next.for exec  with
  | some next => { exec.advance next with state := .shuttingDown }
  | none => by have h' := Next.for_isSome_if_shutdownPending h; simp [hn] at h'

-- TODO: Once Lean has universe polymorphic IO:
-- * factor out a `runInst` function for the instantaneous execution
-- * factor out a `runTimed` function for everything currently happening in the `none` branch
-- Then you can actually prove theorems about these functions.
partial def run (exec : Executable net) (topo : Array (ReactionId net)) (reactionIdx : Nat) : IO Unit := do
  match topo[reactionIdx]? with
  -- This branch is entered whenever we've completed an instantaneous execution.
  | none =>
    match h : exec.state with
    -- The instantaneous execution where the `.shutdown` trigger is active
    -- has already been executed, so we terminate execution.
    | .shuttingDown => return
    -- The last instantaneous execution contained a shutdown request,
    -- so the next instantaneous execution performs shutdown.
    | .shutdownPending => exec.shutdown h |>.run topo 0
    -- Case 1:
    -- We've reached starvation (there are no more events to be processed),
    -- so the next instantaneous execution performs shutdown.
    -- Case 2:
    -- Execution continues normally at the tag of the next event.
    | .executing =>
      match Next.for exec with
      | none =>
        let exec := { exec with state := .shutdownPending }
        exec.shutdown rfl |>.run topo 0
      | some next =>
        let exec := exec.advance next
        IO.sleepUntil exec.absoluteTime
        exec.run topo 0
  -- This branch is entered whenever we're within an instantaneous execution.
  | some reactionId =>
    let reaction := reactionId.reaction
    let mut exec := exec
    if Triggers exec reaction then
      exec := (← exec.fireToIO reaction)
        |> ReactionOutput.fromRaw
        |> exec.apply
        |>.propagate reactionId
    exec.run topo (reactionIdx + 1)

end Execution.Executable
