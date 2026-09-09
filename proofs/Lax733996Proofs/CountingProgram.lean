import Lax733996Proofs.CountingQuery
import Lax733996Proofs.GuessWordCorrectness
import Lax733996Proofs.LogarithmicWidth
import Lax307052Proofs.BinaryDecrement
import Lax307052Proofs.UnaryExpansion

/-! Inductive counting with a fixed set of binary registers. Every guessed
path and every census is generated sequentially. -/

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines
open Lax307052Proofs
open SearchProgram (Register)
open StackMacros (Macro)
open scoped Classical

noncomputable section

abbrev Context (M : Machine) := GraphQuery.Context M Unit
abbrev Data (M : Machine) := GraphQuery.Data M Unit
abbrev Routine (M : Machine) := GraphQuery.Macro M Unit
abbrev Code (M : Machine) := ChoiceLanguage.Command GraphQuery.Key (GraphQuery.Alphabet M Unit) (Context M)

variable (M : Machine)

local infixr:55 " ⋙ₘ " => Macro.seq
local infixr:55 " ⋙ " => ChoiceLanguage.Command.seq

def valid (s : Context M) : Bool := decide (s.user.phase ≠ .done)
def running (s : Context M) : Bool := valid M s && !s.flag

def copy (src dst : Register) : Routine M :=
  Macro.clear (GraphQuery.key .aux) ⋙ₘ
    Macro.copy (SearchProgram.key src) (SearchProgram.key dst) (GraphQuery.key .aux)

def fill (dst : Register) (extra : Option Bool := none) : Routine M :=
  Macro.clear (GraphQuery.key .aux) ⋙ₘ
    Macro.copyMap (SearchProgram.key .width) (SearchProgram.key dst) (GraphQuery.key .aux)
      (fun _ => SearchProgram.bit false) ⋙ₘ
    match extra with
    | none => Macro.skip
    | some b => Macro.push (SearchProgram.key dst) (fun _ => SearchProgram.bit b)

def increment (r : Register) : Routine M :=
  Macro.clear (GraphQuery.key .aux) ⋙ₘ
    Macro.increment (SearchProgram.key r) (GraphQuery.key .aux) SearchProgram.bit SearchProgram.readBit

def decrement (r : Register) : Routine M :=
  Macro.clear (GraphQuery.key .aux) ⋙ₘ
    BinaryCounter.decrement (SearchProgram.key r) (GraphQuery.key .aux) SearchProgram.bit SearchProgram.readBit

def compare (src dst : Register) : Routine M :=
  Macro.clear (GraphQuery.key .aux) ⋙ₘ
    Macro.copy (SearchProgram.key src) (GraphQuery.key .left) (GraphQuery.key .aux) ⋙ₘ
    Macro.copy (SearchProgram.key dst) (GraphQuery.key .right) (GraphQuery.key .aux) ⋙ₘ
    Macro.compare (GraphQuery.key .left) (GraphQuery.key .right)

def requireFlag : Routine M :=
  Macro.assign (fun s => {s with user := {s.user with phase := if s.flag then s.user.phase else .done}})

def requireAnswer : Routine M :=
  Macro.assign (fun s => {s with user := {s.user with phase := if s.user.answer then s.user.phase else .done}})

def beginLoop : Routine M := Macro.assign (fun s => {s with flag := false})

def guess (dst : Register) : Code M :=
  .det ((Macro.clear (SearchProgram.key dst) ⋙ₘ copy M .width .aux).code) ⋙
    GuessWord.code (SearchProgram.key .aux) (SearchProgram.key dst) SearchProgram.bit

def pathStep : Code M :=
  .choose (fun s b => {s with flag := b}) ⋙
    .branch (fun s => s.flag)
      (guess M .b ⋙ .det ((GraphQuery.procedure M Unit ⋙ₘ requireAnswer M ⋙ₘ copy M .b .a).code))
      (.det .skip)

/-- Check reachability of the census vertex using at most the current depth.
A choice to stay pads shorter paths to the fixed number of iterations. -/
def path : Code M :=
  .det ((fill M .a ⋙ₘ copy M .depth .kinds ⋙ₘ decrement M .kinds).code) ⋙
    .loop (running M) (pathStep M ⋙ .det ((decrement M .kinds).code)) ⋙
    .det ((compare M .a .frameMiddle ⋙ₘ requireFlag M).code)

def censusTake : Code M :=
  path M ⋙ .branch (valid M)
    (.det ((copy M .frameMiddle .a ⋙ₘ copy M .frameB .b ⋙ₘ GraphQuery.procedure M Unit ⋙ₘ
      Macro.assign (fun s => {s with user := {s.user with overflow := s.user.overflow || s.user.answer}}) ⋙ₘ
      increment M .frameDepth).code))
    (.det .skip)

def censusStep : Code M :=
  .choose (fun s b => {s with flag := b}) ⋙
    .branch (fun s => s.flag) (censusTake M) (.det .skip) ⋙
    .det ((increment M .frameMiddle).code)

/-- Enumerate every candidate in order and count those with a checked path. -/
def census : Code M :=
  .det ((fill M .frameMiddle ⋙ₘ fill M .frameDepth (some false) ⋙ₘ fill M .a ⋙ₘ
    compare M .frameB .a ⋙ₘ
    Macro.assign (fun s => {s with user := {s.user with overflow := s.flag}}) ⋙ₘ beginLoop M).code) ⋙
    .loop (running M) (censusStep M) ⋙
    .det ((compare M .frameDepth .middle ⋙ₘ requireFlag M).code)

def layerStep : Code M :=
  census M ⋙
    .branch (fun s => s.user.overflow) (.det ((increment M .frameA).code)) (.det .skip) ⋙
    .det ((increment M .frameB).code)

def layer : Code M :=
  .det ((fill M .frameB ⋙ₘ fill M .frameA (some false) ⋙ₘ beginLoop M).code) ⋙
    .loop (running M) (layerStep M) ⋙ .det ((copy M .frameA .middle).code)

def letterWidth : ℕ := FiniteCoding.width (ConfigurationWords.Payload M)

def expandWidth (c : ℕ) : Routine M :=
  Macro.appendCopies (GraphQuery.key .bound) (SearchProgram.key .width) (GraphQuery.key .aux)
    (2 * letterWidth M * c) ⋙ₘ
    Macro.putWord (SearchProgram.key .width) (List.replicate (3 * letterWidth M) (SearchProgram.symbol .tally)) ⋙ₘ
    Macro.clear (GraphQuery.key .bound)

def initializeCode (c : ℕ) : StackRoutines.Code
    (K := GraphQuery.Key) (Γ := GraphQuery.Alphabet M Unit) (σ := GraphQuery.User M) :=
  .seq (LogarithmicWidth.code (GraphQuery.key .constructorLeft) (GraphQuery.key .constructorRight)
    (GraphQuery.key .bound) SearchProgram.bit SearchProgram.readBit (SearchProgram.symbol .tally))
    ((expandWidth M c ⋙ₘ fill M .middle (some true) ⋙ₘ fill M .depth ⋙ₘ beginLoop M).code)

def program (c : ℕ) : Code M :=
  .det (initializeCode M c) ⋙ .loop (running M) (layer M ⋙ .det ((increment M .depth).code))

def initial : Context M := ⟨⟨.call, false, false, GraphQuery.initial M⟩, none, false, .leftEnd, none⟩

def machine (c : ℕ) : Machine :=
  ChoiceLanguage.machine (program M c) (initial M) (fun s => valid M s && !s.user.overflow)

end

end Lax733996Proofs.CountingProgram
