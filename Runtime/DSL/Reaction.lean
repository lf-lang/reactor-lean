import Lean
open Lean Macro

declare_syntax_cat reaction_input
syntax           ident : reaction_input -- port use
syntax  "!" noWs ident : reaction_input -- port trigger
syntax  "@" noWs ident : reaction_input -- action use
syntax "!@" noWs ident : reaction_input -- action trigger

declare_syntax_cat reaction_output
syntax           ident : reaction_output -- port effect
syntax  "@" noWs ident : reaction_output -- action effect

inductive ReactionDependency.Role
  | use
  | trigger
  | effect

inductive ReactionDependency.Kind
  | port   (role : Role)
  | action (role : Role)

structure ReactionDependency where
  ident : Ident
  kind : ReactionDependency.Kind

def ReactionDependency.portSource? : ReactionDependency → Option Ident
  | ⟨ident, .port .use⟩ | ⟨ident, .port .trigger⟩ => ident
  | _ => none

def ReactionDependency.portEffect? : ReactionDependency → Option Ident
  | ⟨ident, .port .effect⟩ => ident
  | _ => none

def ReactionDependency.portTrigger? : ReactionDependency → Option Ident
  | ⟨ident, .port .trigger⟩ => ident
  | _ => none

def ReactionDependency.actionSource? : ReactionDependency → Option Ident
  | ⟨ident, .action .use⟩ | ⟨ident, .action .trigger⟩ => ident
  | _ => none

def ReactionDependency.actionEffect? : ReactionDependency → Option Ident
  | ⟨ident, .action .effect⟩ => ident
  | _ => none

def ReactionDependency.actionTrigger? : ReactionDependency → Option Ident
  | ⟨ident, .action .trigger⟩ => ident
  | _ => none

def ReactionDependency.fromReactionInput : TSyntax `reaction_input → MacroM ReactionDependency
  | `(reaction_input| $i:ident)   => return ⟨i, .port .use⟩
  | `(reaction_input| !$i:ident)  => return ⟨i, .port .trigger⟩
  | `(reaction_input| @$i:ident)  => return ⟨i, .action .use⟩
  | `(reaction_input| !@$i:ident) => return ⟨i, .action .trigger⟩
  | _ => throwUnsupported

def ReactionDependency.fromReactionOutput : TSyntax `reaction_output → MacroM ReactionDependency
  | `(reaction_output| $i:ident)  => return ⟨i, .port .effect⟩
  | `(reaction_output| @$i:ident) => return ⟨i, .action .effect⟩
  | _ => throwUnsupported

declare_syntax_cat reaction_signature
syntax "(" reaction_input,*  ")" " → " "(" reaction_output,* ")" : reaction_signature

def getReactionDependencies : TSyntax `reaction_signature → MacroM (Array ReactionDependency)
  | `(reaction_signature| ($sources:reaction_input,*) → ($effects:reaction_output,*)) => do
    let sources' ← sources.getElems.mapM ReactionDependency.fromReactionInput
    let effects' ← effects.getElems.mapM ReactionDependency.fromReactionOutput
    return sources' ++ effects'
  | _ => throwUnsupported

declare_syntax_cat reaction_decl
syntax "reaction" ident reaction_signature "{" doSeq "}" : reaction_decl 

def getReactionDeclComponents : TSyntax `reaction_decl → MacroM (Ident × TSyntax `reaction_signature × TSyntax `Lean.Parser.Term.doSeq)
  | `(reaction_decl| reaction $name:ident $signature:reaction_signature { $body:doSeq }) => return (name, signature, body)
  | _ => throwUnsupported

def makeReactionDependenciesCommand (reactorIdent : Ident) (rcn : TSyntax `reaction_decl) : MacroM Command := do
  let ⟨name, signature, _⟩ ← getReactionDeclComponents rcn
  let dependencies         ← getReactionDependencies signature
  let portSources          := dependencies.filterMap (·.portSource?)
  let portEffects          := dependencies.filterMap (·.portEffect?)
  let actionSources        := dependencies.filterMap (·.actionSource?)
  let actionEffects        := dependencies.filterMap (·.actionEffect?)
  let reactionNamespace    := reactorIdent.getId ++ `Reactions ++ name.getId
  let portSourcesIdent     := mkIdentFrom name (reactionNamespace ++ `Port.Source)
  let portEffectsIdent     := mkIdentFrom name (reactionNamespace ++ `Port.Effect)
  let actionSourcesIdent   := mkIdentFrom name (reactionNamespace ++ `Action.Source)
  let actionEffectsIdent   := mkIdentFrom name (reactionNamespace ++ `Action.Effect)
  `(  
    inductive $portSourcesIdent   $[| $portSources:ident]*   deriving DecidableEq
    inductive $portEffectsIdent   $[| $portEffects:ident]*   deriving DecidableEq
    inductive $actionSourcesIdent $[| $actionSources:ident]* deriving DecidableEq
    inductive $actionEffectsIdent $[| $actionEffects:ident]* deriving DecidableEq
  )

def makeReactionTriggers (reactorName : Name) (reactionName : Name) (signature : TSyntax `reaction_signature) : MacroM Term := do
  let dependencies ← getReactionDependencies signature
  let ports := dependencies.filterMap fun d => do
    let trigger ← d.portTrigger?
    return mkIdent $ reactorName ++ `Reactions ++ reactionName ++ `Source ++ trigger.getId
  let actions := dependencies.filterMap fun d => do
    let trigger ← d.actionTrigger?
    return mkIdent $ reactorName ++ `Action ++ trigger.getId
  let portTerms ← ports.mapM fun ident => `(Trigger.port $ident)
  let actionTerms ← actions.mapM fun ident => `(Trigger.action $ident)
  let terms := portTerms ++ actionTerms
  `(#[$[$terms],*])