import Runtime.Network.Execution.Next
import Runtime.Network.Execution.Apply
import Runtime.Network.Execution.Propagate

namespace Network.Executable

-- TODO?: Refactor this à la `Reaction.Output.LocalValue` and `Reaction.Output.local`.
-- An interface for all ports (local and nested) that can act as inputs of reactions of a given reactor.
def reactionInputs (exec : Executable net) (reactor : ReactorId net) : Interface? reactor.class.reactionInputScheme
  | .inl localInput           => exec.interface reactor .inputs localInput
  | .inr ⟨child, childOutput⟩ => open Graph Path Class in reactionInputScheme_right_type_eq_extend_child_type ▸ exec.interface (reactor.extend child) .outputs (extend_class ▸ childOutput)

def runRcn (exec : Executable net) {reactor : ReactorId net} (reaction : Graph.Class.ReactionType reactor.class) := do
  let ports   := exec.reactionInputs reactor |>.restrict
  let actions := exec.interface reactor .actions |>.restrict
  let state   := exec.interface reactor .state
  let params  := exec.interface reactor .params
  reaction.val.run ports actions state params exec.tag exec.physicalOffset

def triggers (exec : Executable net) {reactor : ReactorId net} (reaction : Graph.Class.ReactionType reactor.class) : Bool :=
  reaction.val.triggers.any fun trigger =>
    match trigger with
    | .port   port   => exec.reactionInputs reactor     |>.isPresent (reaction.subPS.coe port)
    | .action action => exec.interface reactor .actions |>.isPresent (reaction.subAS.coe action)
    | .timer  timer  => exec.timer reactor timer        |>.firesAtTag exec.tag
    | .startup       => exec.isStartingUp
    | .shutdown      => exec.isShuttingDown

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

def prepareForShutdown (exec : Executable net) : Executable net := { exec with
  tag := { exec.tag with microstep := exec.tag.microstep + 1 }
  isShuttingDown := true
}

-- We can't separate out a `runInst` function at the moment as `IO` isn't universe polymorphic.
partial def run (exec : Executable net) (topo : Array (ReactionId net)) (reactionIdx : Nat) : IO Unit := do
  match topo[reactionIdx]? with 
  | none => 
    unless exec.isShuttingDown do
      match Next.for exec with
      | none      => run exec.prepareForShutdown topo 0
      | some next => run (exec.advance next) topo 0
  | some reactionId =>
    IO.sleepUntil exec.absoluteTime
    let mut exec := exec
    let reaction := reactionId.reaction
    if exec.triggers reaction then
      exec := 
        (← exec.runRcn reaction)
        |> ReactionOutput.fromRaw
        |> exec.apply
        |>.propagate reactionId 
    run exec topo (reactionIdx + 1)

end Network.Executable