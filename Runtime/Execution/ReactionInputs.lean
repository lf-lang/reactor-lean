import Runtime.Execution.Basic

namespace Execution.Executable
open Network Graph Class

-- TODO?: Refactor this à la `Reaction.Output.LocalValue` and `Reaction.Output.local`.
-- An interface for all ports (local and nested) that can act as sources of reactions of a given reactor.
def reactionInputs (exec : Executable net) (reactor : ReactorId net) : Interface? reactor.class.reactionInputScheme
  | .inl localInput           => exec.interface reactor .inputs localInput
  | .inr ⟨child, childOutput⟩ => type_correctness ▸ exec.interface (reactor.extend child) .outputs (Path.extend_class ▸ childOutput)
where
  type_correctness {graph start} {path : Path graph start} {child childOutput} :
    path.class.reactionInputScheme.type (.inr ⟨child, childOutput⟩) =
    ((path.extend child).class.interface .outputs).type (Path.extend_class ▸ childOutput) := by
    simp
    sorry -- HEQ: by extend_class

end Execution.Executable
