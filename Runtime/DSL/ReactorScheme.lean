import Runtime.Reactor
import Lean
open Lean Macro

declare_syntax_cat reactor_child
syntax ident " : " ident : reactor_child

def getReactorChildComponents : (TSyntax `reactor_child) → MacroM (Ident × Ident)
  | `(reactor_child| $i₁:ident : $i₂:ident) => return (i₁, i₂)
  | _ => throwUnsupported

declare_syntax_cat reactor_scheme
syntax "[" reactor_child,* "]" : reactor_scheme

def getReactorSchemeChildren : (TSyntax `reactor_scheme) → MacroM (Array $ TSyntax `reactor_child)
  | `(reactor_scheme| [ $children,* ]) => return children
  | _ => throwUnsupported

macro "gen_reactor_scheme" name:ident scheme:reactor_scheme : command => do
  let vars ← getReactorSchemeChildren scheme
  let components ← vars.mapM getReactorChildComponents
  let ⟨ids, classes⟩ := components.unzip
  let qualifiedIds := ids.map fun id => mkIdentFrom id <| `Nested ++ id.getId
  let classes := classes.map fun «class» => mkIdentFrom «class» <| `Classes ++ «class».getId
  let schemeName := mkIdentFrom name <| name.getId ++ `scheme
  let nestedName := mkIdentFrom name <| name.getId ++ `Nested
  `(
    inductive $nestedName $[| $ids:ident]* deriving DecidableEq
    abbrev $schemeName : Reactor.Scheme $(mkIdent `Classes) where
      interface 
        | .inputs =>  $(mkIdent `Input.scheme)
        | .outputs => $(mkIdent `Output.scheme)
        | .actions => $(mkIdent `Action.scheme)
        | .state =>   $(mkIdent `State.scheme)
      children := $(mkIdent `Nested)
      «class» child := match child with $[| $qualifiedIds => $classes]*
  )