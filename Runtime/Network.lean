import Runtime.Reactor

namespace Network

inductive Tree 
  | node (scheme : Reactor.Scheme) (Nested : Type) (nested : Nested → Tree) (decEq : DecidableEq Nested)

abbrev Tree.scheme : Tree → Reactor.Scheme 
  | .node scheme .. => scheme

abbrev Tree.Nested : Tree → Type 
  | .node _ Nested .. => Nested

abbrev Tree.nested : (tree : Tree) → (tree.Nested → Tree)  
  | .node _ _ nested _ => nested

def Tree.leaf (scheme : Reactor.Scheme) : Tree :=
  .node scheme Empty (·.rec) inferInstance

inductive ReactorID.Nested : Tree → Type _
  | final [decEq : DecidableEq IDs] (id : IDs) (nested : IDs → Tree) : Nested (.node _ IDs nested decEq)
  | cons [decEq : DecidableEq IDs] (head : IDs) (nested : IDs → Tree) : (Nested $ nested head) → (Nested $ .node _ IDs nested decEq)

inductive ReactorID (tree : Tree)
  | main
  | nested : ReactorID.Nested tree → ReactorID tree

abbrev Tree.subtree (tree : Tree) : ReactorID tree → Tree
  | .main => tree
  | .nested n =>
    match n with 
    | ReactorID.Nested.final id nested  => nested id
    | ReactorID.Nested.cons head tail nestedID => subtree (tail head) (.nested nestedID)

notation tree:max "[" id "]" => Tree.subtree tree id

abbrev Tree.reactionType : Tree → Type _
  | .node scheme Nested nested _ =>
    Reaction 
      (scheme.inputs.sum (Interface.Scheme.sum' Nested fun n => (nested n).scheme.outputs))   
      (scheme.outputs.sum (Interface.Scheme.sum' Nested fun n => (nested n).scheme.inputs))
      scheme.actions
      scheme.state

structure PortID (kind : PortKind) (tree : Tree) where
  reactor : ReactorID tree
  port : tree[reactor].scheme.ports kind |>.vars

abbrev Connection (tree : Tree) := (PortID .output tree) × (PortID .input tree)

structure _root_.Network where
  tree : Tree
  reactions : (id : ReactorID tree) → Array $ tree[id].reactionType
  reactors :  (id : ReactorID tree) → Reactor $ tree[id].scheme
  connections : Array (Connection tree)

end Network