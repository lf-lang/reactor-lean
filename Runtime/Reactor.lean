import Runtime.Interface

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

structure Scheme (Classes : Type) where
  interface : InterfaceKind → Interface.Scheme 
  children : Type
  «class» : children → Classes
  [decEqChildren : DecidableEq children]
  
attribute [instance] Scheme.decEqChildren

end Reactor