import Runtime.Execution.Basic

namespace Execution.Executable
open Network Graph Path

/--
An interface for all ports (local and nested) that can act as sources of reactions of a given
reactor.
-/
def reactionInputs (exec : Executable net) (reactor : ReactorId net) :
  Interface? reactor.class.reactionInputScheme
  | .inl input           => exec.interface reactor .inputs input
  | .inr ⟨child, output⟩ =>
    have h₁ := by rw [extend_class]
    have h₂ := by simp; congr; apply extend_class; apply cast_heq
    exec.interface (reactor.extend child) .outputs (output |> cast h₁) |> cast h₂

end Execution.Executable
