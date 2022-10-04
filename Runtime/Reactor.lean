import Runtime.Interface

namespace Reactor

inductive PortKind
  | input
  | output

inductive InterfaceKind 
  | inputs 
  | outputs 
  | actions
  | state

@[reducible]
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
attribute [reducible] Scheme.interface
attribute [reducible] Scheme.class

end Reactor