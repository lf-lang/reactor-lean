import Lean
open Lean Macro

declare_syntax_cat reaction_input
syntax          ident : reaction_input -- use
syntax "!" noWs ident : reaction_input -- source trigger
syntax "@" noWs ident : reaction_input -- action trigger

inductive ReactionDependency.Kind
  | use    
  | source -- (trigger) 
  | action -- (trigger) 
  | effect

structure ReactionDependency where
  ident : Ident
  kind : ReactionDependency.Kind

def ReactionDependency.input? (d : ReactionDependency) : Option Ident :=
  match d.kind with 
  | .use | .source => d.ident
  | _ => none

def ReactionDependency.source? (d : ReactionDependency) : Option Ident :=
  match d.kind with 
  | .source => d.ident
  | _ => none

def ReactionDependency.action? (d : ReactionDependency) : Option Ident :=
  match d.kind with 
  | .action => d.ident
  | _ => none

def ReactionDependency.effect? (d : ReactionDependency) : Option Ident :=
  match d.kind with 
  | .effect => d.ident
  | _ => none

def ReactionDependency.fromReactionInput : TSyntax `reaction_input → MacroM ReactionDependency
  | `(reaction_input| $i:ident)  => return ⟨i, .use⟩
  | `(reaction_input| !$i:ident) => return ⟨i, .source⟩
  | `(reaction_input| @$i:ident) => return ⟨i, .action⟩
  | _ => throwUnsupported

declare_syntax_cat reaction_signature
syntax "(" reaction_input,*  ")" " → " "(" ident,* ")" : reaction_signature

def getReactionDependencies : TSyntax `reaction_signature → MacroM (Array ReactionDependency)
  | `(reaction_signature| ($inputs:reaction_input,*) → ($effects:ident,*)) => do
    let effects' := effects.getElems.map (⟨·, .effect⟩)
    let inputs' ← inputs.getElems.mapM ReactionDependency.fromReactionInput
    return inputs' ++ effects'
  | _ => throwUnsupported

declare_syntax_cat reaction_decl
syntax "reaction" ident reaction_signature "{" doSeq "}" : reaction_decl 

def getReactionDeclComponents : TSyntax `reaction_decl → MacroM (Ident × TSyntax `reaction_signature × TSyntax `Lean.Parser.Term.doSeq)
  | `(reaction_decl| reaction $name:ident $signature:reaction_signature { $body:doSeq }) => return (name, signature, body)
  | _ => throwUnsupported

def makeReactionDependenciesCommand (reactorIdent : Ident) (rcn : TSyntax `reaction_decl) : MacroM Command := do
  let ⟨name, signature, _⟩ ← getReactionDeclComponents rcn
  let dependencies ← getReactionDependencies signature
  let inputs      := dependencies.filterMap (·.input?)
  let effects     := dependencies.filterMap (·.effect?)
  let inputIdent  := mkIdentFrom name (reactorIdent.getId ++ name.getId ++ `Source)
  let effectIdent := mkIdentFrom name (reactorIdent.getId ++ name.getId ++ `Effect)
  `(  
    inductive $inputIdent  $[| $inputs:ident]* deriving DecidableEq
    inductive $effectIdent $[| $effects:ident]* deriving DecidableEq
  )

def makeReactionTriggers (reactorName : Name) (reactionName : Name) (signature : TSyntax `reaction_signature) : MacroM Term := do
  let dependencies ← getReactionDependencies signature
  let sources : Array Ident := dependencies.filterMap fun d => d.source? >>= (mkIdent $ reactorName ++ reactionName ++ `Source ++ ·.getId)
  let actions : Array Ident := dependencies.filterMap fun d => d.action? >>= (mkIdent $ reactorName ++ `Action ++ ·.getId)
  `(#[ $[.source $sources],* , $[.action $actions],*])