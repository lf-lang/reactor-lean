import Runtime.Reactor

namespace Network

namespace ReactorID

-- This represents a tree of types for reactors' IDs.
-- Leaves are constructed with the `Empty` type.
inductive Tree 
  | node (IDs : Type) (nested : IDs → Tree)

inductive Nested : Tree → Type _
  | final (id : IDs) : Nested (.node IDs nested)
  | cons (head : IDs) {nested : IDs → Tree} : (Nested $ nested head) → (Nested $ .node IDs nested)

end ReactorID

open ReactorID in
inductive ReactorID (tree : Tree)
  | main
  | nested : Nested tree → ReactorID tree

/-
#check []
open Lean in
macro "[" elems:term,*  "]" : term => do
  let ids := elems.getElems
  match ids.size with
  | 0 => `(Network.ReactorID.main)
  | 1 => `(Network.ReactorID.nested (Network.ReactorID.Nested.final $(ids[0]!)))
  | _ => 
    `(Network.ReactorID.nested ($[cons $ids]*))
-/

structure Scheme where
  tree : ReactorID.Tree
  reactor : (ReactorID tree) → Reactor.Scheme 

def Scheme.reactorIDs (σ : Network.Scheme) := ReactorID σ.tree

structure PortID (kind : PortKind) (σ : Network.Scheme) where
  reactor : σ.reactorIDs
  port : σ.reactor reactor |>.ports kind |>.vars

abbrev Connection (σ : Network.Scheme) := (PortID .output σ) × (PortID .input σ)

structure _root_.Network where
  scheme : Network.Scheme
  reactor : (id : scheme.reactorIDs) → Reactor (scheme.reactor id)
  connections : Array (Connection scheme)

end Network