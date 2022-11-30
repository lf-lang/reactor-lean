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
  | params

abbrev InterfaceKind.interfaceType : InterfaceKind → (Interface.Scheme → Type)
  | inputs | outputs | actions => Interface?
  | state  | params            => Interface

def InterfaceKind.allCases : Array Reactor.InterfaceKind :=
  #[.inputs, .outputs, .actions, .state, .params]

instance : Coe PortKind InterfaceKind where
  coe
    | .input => .inputs
    | .output => .outputs

structure Scheme (classes : Type) where
  interface : InterfaceKind → Interface.Scheme
  timers    : Type
  children  : Type
  «class»   : children → classes
  [decEqTimers : DecidableEq timers]
  [decEqChildren : DecidableEq children]

attribute [instance] Scheme.decEqTimers
attribute [instance] Scheme.decEqChildren

end Reactor
