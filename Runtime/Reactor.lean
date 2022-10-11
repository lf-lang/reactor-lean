import Runtime.Interface
import Runtime.Timer

namespace Reactor

inductive PortKind
  | input
  | output

inductive InterfaceKind 
  | inputs 
  | outputs 
  | actions
  | state

abbrev InterfaceKind.interfaceType : InterfaceKind → (Interface.Scheme → Type)
  | inputs | outputs | actions => Interface?
  | state  => Interface

def InterfaceKind.allCases : Array Reactor.InterfaceKind :=
  #[.inputs, .outputs, .actions, .state]

@[reducible]
instance : Coe PortKind InterfaceKind where
  coe
    | .input => .inputs
    | .output => .outputs

structure Scheme (Classes : Type) where
  interface : InterfaceKind → Interface.Scheme
  timers    : Type
  timer     : timers → Timer
  children  : Type
  «class»   : children → Classes
  [decEqChildren : DecidableEq children]
  
attribute [instance] Scheme.decEqChildren
attribute [reducible] Scheme.interface
attribute [reducible] Scheme.class

end Reactor