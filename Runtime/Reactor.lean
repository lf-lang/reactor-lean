import Runtime.Reaction

namespace Reactor

inductive PortKind
  | input
  | output

abbrev PortKind.opposite : PortKind → PortKind 
  | .input => .output
  | .output => .input

inductive InterfaceKind 
  | inputs 
  | outputs 
  | actions
  | state

instance : Coe PortKind InterfaceKind where
  coe
    | .input => .inputs
    | .output => .outputs

def Scheme := InterfaceKind → Interface.Scheme 
def _root_.Reactor (σ : Reactor.Scheme) := (kind : InterfaceKind) → (Interface $ σ kind)

end Reactor