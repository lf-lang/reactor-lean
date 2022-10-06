import Runtime.Network.Basic
import Lean
open Lean Macro

structure InterfaceVar where
  id : Ident
  value : Term

def InterfaceDecl := Array InterfaceVar
  
deriving instance Inhabited for InterfaceDecl

structure ReactorDecl where
  name : Ident
  interfaces : Reactor.InterfaceKind → InterfaceDecl
  nested : InterfaceDecl
  deriving Inhabited

structure GraphDecl where
  name : Ident 
  reactors : Array ReactorDecl

declare_syntax_cat interface_var
syntax ident " : " term : interface_var

declare_syntax_cat interface_decl
syntax "[" interface_var,* "]" : interface_decl

declare_syntax_cat reactor_decl
syntax ident "where" 
  "inputs"  ":=" interface_decl 
  "outputs" ":=" interface_decl 
  "actions" ":=" interface_decl 
  "state"   ":=" interface_decl 
  "nested"  ":=" interface_decl
  : reactor_decl

declare_syntax_cat graph_decl
syntax ident "where" reactor_decl+ : graph_decl

def InterfaceVar.fromSyntax : TSyntax `interface_var → MacroM InterfaceVar
  | `(interface_var| $id:ident : $value) => return { id := id, value := value }
  | _ => throwUnsupported

def InterfaceDecl.fromSyntax : TSyntax `interface_decl → MacroM InterfaceDecl
  | `(interface_decl| [$vars:interface_var,*]) => vars.getElems.mapM InterfaceVar.fromSyntax
  | _ => throwUnsupported

def ReactorDecl.fromSyntax : TSyntax `reactor_decl → MacroM ReactorDecl
  | `(reactor_decl| $name:ident where inputs := $i outputs := $o actions := $a state := $s nested := $n) => do
    let i ← InterfaceDecl.fromSyntax i
    let o ← InterfaceDecl.fromSyntax o
    let a ← InterfaceDecl.fromSyntax a
    let s ← InterfaceDecl.fromSyntax s
    let n ← InterfaceDecl.fromSyntax n
    return {
      name := name
      interfaces := fun | .inputs => i | .outputs => o | .actions => a | .state => s
      «nested» := n  
    }
  | _ => throwUnsupported

def GraphDecl.fromSyntax : TSyntax `graph_decl → MacroM GraphDecl
  | `(graph_decl| $name:ident where $reactors:reactor_decl*) => return {
      name := name
      reactors := (← reactors.mapM ReactorDecl.fromSyntax)
    }
  | _ => throwUnsupported

def InterfaceDecl.ids (decl : InterfaceDecl) := 
  decl.map (·.id)

def InterfaceDecl.values (decl : InterfaceDecl) := 
  decl.map (·.value)

def GraphDecl.reactorNames (decl : GraphDecl) :=
  decl.reactors.map (·.name)

def GraphDecl.mainReactorIdent! (decl : GraphDecl) :=
  let reactorIdent := decl.reactors[0]!.name
  mkIdentFrom reactorIdent (decl.name.getId ++ `Class ++ reactorIdent.getId)

def InterfaceDecl.genInterfaceScheme (decl : InterfaceDecl) (name : Ident) : MacroM Command := 
  let schemeIdent := mkIdentFrom name (name.getId ++ `scheme)
  let types := decl.values
  `(
    inductive $name $[| $(decl.ids):ident]* deriving DecidableEq
    abbrev $schemeIdent : Interface.Scheme where
      vars := $name
      type var := match var with $[| $(decl.ids) => $types]*
  )

def Reactor.InterfaceKind.name : Reactor.InterfaceKind → Name
  | .inputs  => `Input
  | .outputs => `Output
  | .actions => `Action
  | .state   => `State

def ReactorDecl.genInterfaceSchemes (decl : ReactorDecl) (ns : Ident) : MacroM (Array Command) :=
  #[Reactor.InterfaceKind.inputs, .outputs, .actions, .state].mapM fun kind =>
    let interface := decl.interfaces kind
    interface.genInterfaceScheme <| mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ kind.name)

def ReactorDecl.genReactorScheme (decl : ReactorDecl) (ns : Ident) : MacroM Command := do
  let mkNamespacedIdent name := mkIdentFrom decl.name (ns.getId ++ decl.name.getId ++ name)
  let classesEnumIdent := mkIdentFrom ns (ns.getId ++ `Class)
  let nestedEnumIdent := mkNamespacedIdent `Nested
  let schemeIdent := mkNamespacedIdent `scheme
  let namespacedNestedIds := decl.nested.ids.map fun id => mkIdentFrom id (nestedEnumIdent.getId ++ id.getId)
  let classes := decl.nested.values.map fun «class» => mkIdentFrom «class» (classesEnumIdent.getId ++ «class».getId)
  `(
    inductive $nestedEnumIdent $[| $(decl.nested.ids):ident]* deriving DecidableEq
    abbrev $schemeIdent : Reactor.Scheme $classesEnumIdent where
      interface -- TODO: Use `Reactor.InterfaceKind.name` for this.
        | .inputs  => $(mkIdent `Input.scheme)
        | .outputs => $(mkIdent `Output.scheme)
        | .actions => $(mkIdent `Action.scheme)
        | .state   => $(mkIdent `State.scheme)
      children := $nestedEnumIdent
      «class» child := match child with $[| $namespacedNestedIds => $classes]*
  )
  
def GraphDecl.genClassesEnum (decl : GraphDecl) : MacroM Command := do
  let enumIdent := mkIdentFrom decl.name (decl.name.getId ++ `Class)
  `(inductive $enumIdent $[| $(decl.reactorNames):ident]*)

def GraphDecl.genGraphInstance (decl : GraphDecl) : MacroM Command := do
  let classEnumIdent := mkIdentFrom decl.name (decl.name.getId ++ `Class)
  let classes := decl.reactorNames.map fun reactorName => mkIdentFrom reactorName (decl.name.getId ++ `Class ++ reactorName.getId)
  let classSchemes := decl.reactorNames.map fun reactorName => mkIdentFrom reactorName (decl.name.getId ++ reactorName.getId ++ `scheme)
  `(
    abbrev $decl.name : Network.Graph where
    classes := $classEnumIdent
    root := $(decl.mainReactorIdent!)
    schemes $[| $classes => $classSchemes]*
  )

def GraphDecl.genInterfaceSchemes (decl : GraphDecl) : MacroM (Array Command) :=
  decl.reactors.concatMapM fun reactor => reactor.genInterfaceSchemes decl.name

def GraphDecl.genReactorSchemes (decl : GraphDecl) : MacroM (Array Command) :=
  decl.reactors.mapM (·.genReactorScheme decl.name)

macro "gen_graph" graph:graph_decl : command => do
  let graph ← GraphDecl.fromSyntax graph
  return mkNullNode <|
    (← graph.genInterfaceSchemes) ++ 
    [← graph.genClassesEnum] ++
    (← graph.genReactorSchemes) ++
    [← graph.genGraphInstance]
