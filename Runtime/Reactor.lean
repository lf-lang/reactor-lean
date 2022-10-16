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

-- A reactor's parameters have no influence on the *structure* of the reactor.
-- That is, the scheme is unaffected.
--
-- ! This is not true: the type of reactions changes!

-- WIP

structure Parameters where
  scheme : Interface.Scheme
  values : Interface scheme

structure Scheme (Classes : Type) (params : Interface.Scheme) where
  interface : InterfaceKind → Interface.Scheme
  timers    : Type
  timer     : timers → Timer
  children  : Type
  «class»   : children → Classes
  [decEqTimers : DecidableEq timers]
  [decEqChildren : DecidableEq children]
  
attribute [instance] Scheme.decEqTimers
attribute [instance] Scheme.decEqChildren
attribute [reducible] Scheme.interface
attribute [reducible] Scheme.class

end Reactor