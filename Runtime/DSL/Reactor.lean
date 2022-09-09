import Runtime.DSL.Interface
import Runtime.DSL.Reaction
import Lean
open Lean Macro

declare_syntax_cat reactor_scheme_field
syntax ident " := " interface_scheme : reactor_scheme_field

def getReactorSchemeFieldComponents : (TSyntax `reactor_scheme_field) → MacroM (Ident × TSyntax `interface_scheme)
  | `(reactor_scheme_field| $i:ident := $s) => return (i, s)
  | _ => throwUnsupported

declare_syntax_cat reactor_scheme
syntax "{" reactor_scheme_field* reaction_decl* "}" : reactor_scheme

inductive ReactorSchemeField
  | input
  | output
  | action
  | state
  deriving BEq

def ReactorSchemeField.all : Array ReactorSchemeField := 
  #[.input, .output, .action, .state]

instance : ToString ReactorSchemeField where
  toString
    | .input => "input"
    | .output => "output"
    | .action => "action"
    | .state => "state"

def ReactorSchemeField.fromIdent (i : Ident) : MacroM ReactorSchemeField :=
  match i.getId.toString with
  | "input"  => return .input
  | "output" => return .output
  | "action" => return .action
  | "state"   => return .state
  | invalid   => Macro.throwErrorAt i s!"invalid reactor field '{invalid}'"

def getReactorSchemeInterfaces : (TSyntax `reactor_scheme) → MacroM (ReactorSchemeField → (MacroM $ TSyntax `interface_scheme))
  | `(reactor_scheme| { $syns:reactor_scheme_field* $__:reaction_decl* }) => do
    let components ← syns.mapM getReactorSchemeFieldComponents
    let fields ← components.mapM fun ⟨id, scheme⟩ => return (← ReactorSchemeField.fromIdent id, scheme)
    return fun field => 
      match fields.find? (·.fst == field) with 
      | none          => Macro.throwError s!"missing field '{field}'"
      | some ⟨_, syn⟩ => return syn
  | _ => throwUnsupported

def makeReactorSchemeInterfaceCommands (container : Ident) (scheme : TSyntax `reactor_scheme) : MacroM (Array Command) := do
  let interfaces ← getReactorSchemeInterfaces scheme
  ReactorSchemeField.all.mapM fun field => do
    let fieldIdent := mkIdentFrom container (container.getId ++ (toString field).capitalize)
    let «interface» ← interfaces field
    `(interface $fieldIdent:ident $«interface»)

def getReactorSchemeReactionDecls : (TSyntax `reactor_scheme) → MacroM (Array $ TSyntax `reaction_decl)
  | `(reactor_scheme| { $__:reactor_scheme_field* $reactions:reaction_decl* }) => return reactions
  | _ => throwUnsupported

def makeReactorSchemeCommand (name : Ident) (reactions : Array Ident) : MacroM Command := do
  let schemeIdent := mkIdentFrom name (name.getId ++ `scheme)
  let reactionInstanceIdents := reactions.map fun rcn => mkIdentFrom rcn (name.getId ++ `Reactions ++ rcn.getId ++ `instance)
  `(
    def $schemeIdent : $(mkIdent `Reactor.Scheme) := {
      inputs    := $(mkIdent `Input.scheme)
      outputs   := $(mkIdent `Output.scheme)
      actions   := $(mkIdent `Action.scheme)
      state     := $(mkIdent `State.scheme)
      reactions := #[$[$reactionInstanceIdents],*]
    }
  ) 

def makeInjectiveCoeCommand (name : Ident) (reactor : TSyntax `reactor_scheme) (reactions : Array (Ident × TSyntax `reaction_signature)) : MacroM (Array Command) := do
  let reactorInterfaces ← getReactorSchemeInterfaces reactor
  let ⟨reactorInputIdents, _⟩ := (← (← getInterfaceSchemeVars (← reactorInterfaces .input)).mapM getInterfaceVarComponents).unzip
  let ⟨reactorOutputIdents, _⟩ := (← (← getInterfaceSchemeVars (← reactorInterfaces .output)).mapM getInterfaceVarComponents).unzip
  let reactorInputType := mkIdentFrom name (name.getId ++ (toString ReactorSchemeField.input).capitalize)
  let reactorOutputType := mkIdentFrom name (name.getId ++ (toString ReactorSchemeField.output).capitalize)
  let mut commands : Array Command := #[]
  for ⟨reactionIdent, signature⟩ in reactions do
    let reactionSourceType := mkIdentFrom reactionIdent (name.getId ++ `Reactions ++ reactionIdent.getId ++ `Source)
    let reactionEffectType := mkIdentFrom reactionIdent (name.getId ++ `Reactions ++ reactionIdent.getId ++ `Effect)
    let reactionSourceIdents : Array Ident := (← getReactionDependencies signature).filterMap (·.input?)
    let reactionSourceIdents' := reactionSourceIdents.map fun ident => mkIdentFrom ident (name.getId ++ `Reactions ++ reactionIdent.getId ++ `Source ++ ident.getId.getRoot)
    let reactionSourceIdentsAsInput := reactionSourceIdents.map fun ident => mkIdentFrom ident (name.getId ++ `Input ++ ident.getId.getRoot)
    let nonSourceInputs := reactorInputIdents.filter (¬ reactionSourceIdents.contains ·)
    let reactionEffectIdents : Array Ident := (← getReactionDependencies signature).filterMap (·.effect?)
    let reactionEffectIdents' := reactionEffectIdents.map fun ident => mkIdentFrom ident (name.getId ++ `Reactions ++ reactionIdent.getId ++ `Effect ++ ident.getId.getRoot)
    let reactionEffectIdentsAsOutput := reactionEffectIdents.map fun ident => mkIdentFrom ident (name.getId ++ `Output ++ ident.getId.getRoot)
    let nonEffectOutputs := reactorOutputIdents.filter (¬ reactionEffectIdents.contains ·)
    commands := commands.push (← `(
      @[reducible]
      instance : $(mkIdent `InjectiveCoe) $reactionSourceType $reactorInputType where
        coe a := match a with $[| $reactionSourceIdents' => $reactionSourceIdentsAsInput]*
        inv b := match b with $[| $reactionSourceIdentsAsInput => some $reactionSourceIdents']* $[| $nonSourceInputs => none]*
        invInj := by intro b₁ b₂ _; cases b₁ <;> cases b₂ <;> simp at *
        coeInvId := (by cases · <;> rfl)

      @[reducible]
      instance : $(mkIdent `InjectiveCoe) $reactionEffectType $reactorOutputType where
        coe a := match a with $[| $reactionEffectIdents' => $reactionEffectIdentsAsOutput]*
        inv b := match b with $[| $reactionEffectIdentsAsOutput => some $reactionEffectIdents']* $[| $nonEffectOutputs => none]*
        invInj := by intro b₁ b₂ _; cases b₁ <;> cases b₂ <;> simp at *
        coeInvId := (by cases · <;> rfl)
    ))
  return commands

def makeReactionInstanceCommands (reactorIdent : Ident) (reactions : Array $ TSyntax `reaction_decl) : MacroM (Array Command) := do
  let mut commands : Array Command := #[]
  for rcn in reactions do
    let ⟨reactionIdent, reactionSignature, reactionBody⟩ ← getReactionDeclComponents rcn
    let reactionInstanceIdent := mkIdentFrom reactionIdent (reactorIdent.getId ++ `Reactions ++ reactionIdent.getId ++ `instance)
    let reactorName := reactorIdent.getId
    let reactionName := reactorName ++ `Reactions ++ reactionIdent.getId
    let reactorActionType := mkIdent $ reactorName ++ `Action
    let reactorStateType := mkIdent $ reactorName ++ `State
    let reactionSourceType := mkIdent $ reactionName ++ `Source
    let reactionEffectType := mkIdent $ reactionName ++ `Effect
    let triggers ← makeReactionTriggers reactorName reactionIdent.getId reactionSignature
    commands := commands.push (← `(
      def $reactionInstanceIdent : $(mkIdent `Reaction) $(mkIdent $ reactorName ++ `Input ++ `scheme) $(mkIdent $ reactorName ++ `Output ++ `scheme) $(mkIdent $ reactorActionType.getId ++ `scheme) $(mkIdent $ reactorStateType.getId ++ `scheme) := {
        sources := $reactionSourceType
        effects := $reactionEffectType
        triggers := $triggers,
        body := open $(mkIdent `ReactionM) $reactionSourceType $reactionEffectType $reactorActionType $reactorStateType in do
          $reactionBody
      }
    ))
  return commands

def makeReactorInstanceCommand (name : Ident): MacroM Command := `(
    def $(mkIdentFrom name $ name.getId ++ `instance) : $(mkIdent `Reactor) $(mkIdentFrom name $ name.getId ++ `scheme) := {
      inputs  := fun _ => none
      outputs := fun _ => none
      actions := fun _ => none
      state   := fun _ => none
    }
  )

-- Generates:
--
-- inductive ReactorName.Input
-- inductive ReactorName.Output
-- inductive ReactorName.Action
-- inductive ReactorName.State
-- def ReactorName.Input.scheme
-- def ReactorName.Output.scheme
-- def ReactorName.Action.scheme
-- def ReactorName.State.scheme
-- def ReactorName.scheme
-- def ReactorName.instance
--
-- For each reaction:
-- 
-- inductive ReactorName.Reactions.ReactionName.Source
-- inductive ReactorName.Reactions.ReactionName.Effect
-- instance : InjectiveCoe ReactorName.Reactions.ReactionName.Source ReactorName.Input
-- instance : InjectiveCoe ReactorName.Reactions.ReactionName.Effect ReactorName.Output
-- def ReactorName.Reactions.ReactionName.instance
macro "reactor" name:ident scheme:reactor_scheme : command => do
  let reactionDecls ← getReactorSchemeReactionDecls scheme
  let reactionComponents ← reactionDecls.mapM getReactionDeclComponents
  let ⟨reactionIdents, reactionFunctions⟩ := reactionComponents.unzip
  let ⟨reactionSignatures, _⟩ := reactionFunctions.unzip
  let reactionDependenciesCommands ← reactionDecls.mapM (makeReactionDependenciesCommand name)
  let interfaceCommands ← makeReactorSchemeInterfaceCommands name scheme
  let reactionInstanceCommands ← makeReactionInstanceCommands name reactionDecls
  let injectiveCoeCommands ← makeInjectiveCoeCommand name scheme (Array.zip reactionIdents reactionSignatures)
  let reactorSchemeCommand ← makeReactorSchemeCommand name reactionIdents
  let reactorInstanceCommand ← makeReactorInstanceCommand name
  -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Antiquot.20Splice/near/297760730
  return mkNullNode <| reactionDependenciesCommands ++ interfaceCommands ++ injectiveCoeCommands ++ reactionInstanceCommands ++ [reactorSchemeCommand, reactorInstanceCommand]