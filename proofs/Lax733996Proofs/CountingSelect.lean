import Lax733996Proofs.CountingTake

namespace Lax733996Proofs.CountingProgram

open Lax434930.PolynomialTime Lax434930.SpaceMachines Lax307052Proofs
open Lax307052.Reachability
open ChoiceLanguage (Exec Total Good)
open scoped Classical

noncomputable section

set_option maxHeartbeats 1000000

variable (M : Machine)

def CensusSelectPost (w : Word) (m k c : ℕ) (u v : Fin (2 ^ m)) (d e : Data M) : Prop :=
  Keeps censusTakeWrites d e ∧
    (valid M e.state = true → valid M d.state = true) ∧
    ((reg e .frameDepth = SearchProgram.word (m + 1) c ∧ e.state.user.overflow = d.state.user.overflow) ∨
      (reg e .frameDepth = SearchProgram.word (m + 1) (c + 1) ∧
        e.state.user.overflow = (d.state.user.overflow || EncodedGraph.graph M w m u v) ∧
        Within (fun x y => EncodedGraph.graph M w m x y = true) k (EncodedGraph.first m) u))

lemma censusSelect_total (w : Word) (bound m k c : ℕ) (hk : k < 2 ^ m) (hc : c < 2 ^ (m + 1))
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) :
    Total w bound (censusSelect M) d := by
  apply Total.seq (.choose d _ hd)
  intro e he
  cases he with
  | choose _ _ b _ =>
    cases b with
    | false => exact .branch_false rfl (.det (.skip _ hd))
    | true =>
      exact .branch_true rfl (censusTake_total M w bound m k c hk hc
        (StackLanguage.assigned d {d.state with flag := true}) hd hw hdepth hm u v hu hv hcnt)

lemma censusSelect_sound (w : Word) (bound m k c : ℕ) (hk : k < 2 ^ m) (hc : c < 2 ^ (m + 1))
    (d e : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c)
    (h : Exec w bound (censusSelect M) d e) : CensusSelectPost M w m k c u v d e := by
  cases h with
  | seq hchoose hb =>
    cases hchoose with
    | choose _ _ b _ =>
      cases b with
      | false =>
        cases hb with
        | branch_true ht _ => simp [StackLanguage.assigned] at ht
        | branch_false _ he =>
          cases he with
          | det hs =>
            cases hs
            exact ⟨Keeps.refl _ _, fun h => h, Or.inl ⟨hcnt, rfl⟩⟩
      | true =>
        cases hb with
        | branch_false ht _ => simp [StackLanguage.assigned] at ht
        | branch_true _ he =>
          obtain ⟨hkeep, hlive, hr⟩ := censusTake_sound M w bound m k c hk hc
            (StackLanguage.assigned d {d.state with flag := true}) e hd hw hdepth hm u v hu hv hcnt he
          refine ⟨hkeep, hlive, ?_⟩
          rcases hr with ⟨_, hcnt, hfound⟩ | hr
          · exact Or.inl ⟨hcnt, hfound⟩
          · exact Or.inr hr

lemma censusSelect_skip (w : Word) (bound : ℕ) (d : Data M) (hd : Good w bound d) :
    Exec w bound (censusSelect M) d (StackLanguage.assigned d {d.state with flag := false}) :=
  .seq (.choose d _ false hd) (.branch_false rfl (.det (.skip _ hd)))

lemma censusSelect_take (w : Word) (bound m k c : ℕ) (hk : k < 2 ^ m) (hc : c < 2 ^ (m + 1))
    (d : Data M) (hd : Good w bound d) (hw : reg d .width = SearchProgram.unary m)
    (hdepth : reg d .depth = SearchProgram.word m k) (hm : m + 1 < bound)
    (u v : Fin (2 ^ m)) (hu : reg d .frameMiddle = SearchProgram.word m u.val)
    (hv : reg d .frameB = SearchProgram.word m v.val)
    (hcnt : reg d .frameDepth = SearchProgram.word (m + 1) c) (hl : valid M d.state = true)
    (hreach : Within (fun x y => EncodedGraph.graph M w m x y = true) k (EncodedGraph.first m) u) :
    ∃ e, Exec w bound (censusSelect M) d e ∧ Keeps censusTakeWrites d e ∧
      reg e .frameDepth = SearchProgram.word (m + 1) (c + 1) ∧
      e.state.user.overflow = (d.state.user.overflow || EncodedGraph.graph M w m u v) ∧ valid M e.state = true := by
  obtain ⟨e, he, ⟨hkeep, _, hr⟩, hel⟩ := censusTake_complete M w bound m k c hk hc
    (StackLanguage.assigned d {d.state with flag := true}) hd hw hdepth hm u v hu hv hcnt hl hreach
  rcases hr with ⟨hf, _, _⟩ | ⟨hcnt, hfound, _⟩
  · simp [hel] at hf
  · exact ⟨e, .seq (.choose d _ true hd) (.branch_true rfl he), hkeep, hcnt, hfound, hel⟩

end

end Lax733996Proofs.CountingProgram
