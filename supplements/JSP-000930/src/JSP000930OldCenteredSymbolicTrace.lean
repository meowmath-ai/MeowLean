import JSP000930CohenStrictInterior
import JSP000930SymbolicPrefixCompleteMap
import JSP000930SymbolicOneValueGridShift

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

open scoped Classical in
noncomputable def overwritePalette (H : J → ℕ → ComplexBits B) (z : J)
    (v : ComplexBits B) : J → ℕ → ComplexBits B :=
  fun j n => if j = z then v else H j n

noncomputable def oldCenteredTrace (site : J → ComplexBits B)
    (H : J → ℕ → ComplexBits B) (p : SymbolicTrace J) (i : PinNumber p)
    (c : ℚ × ℚ) (R : ℕ) (e : ℚ) (he : 0 < e) : PolyTrace B J := by
  classical
  let q := decodeSymbolicTrace site (overwritePalette H (pinAt p i).1
    (ComplexBits.checked (gaussianRat c))) p
  exact ⟨q.coeff,q.pins.erase (pinAt p i).1,R,e,he⟩

set_option maxHeartbeats 400000 in
theorem oldCenteredTrace_valid_exact (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace J) (i : PinNumber p) (c : ℚ × ℚ)
    (R : ℕ) (e : ℚ) (he : 0 < e) (m : B)
    (hSite : ∀ j ∈ p.pins.map Prod.fst,(site j).CutOn m)
    (hH : ∀ j ∈ p.pins.map Prod.fst,j ≠ (pinAt p i).1 → ∀ n,(H j n).CutOn m)
    (hApart : ∀ j ∈ p.pins.map Prod.fst,∀ k ∈ p.pins.map Prod.fst,j ≠ k →
      m ≤ ((site j).name =ᴮ (site k).name)ᶜ) :
    m ≤ polyValid site H (oldCenteredTrace site H p i c R e he) ∧
    m ≤ ((oldCenteredTrace site H p i c R e he).eval (site (pinAt p i).1)).name =ᴮ
      (ComplexBits.checked (gaussianRat c)).name := by
  classical
  let v : ComplexBits B := ComplexBits.checked (gaussianRat c)
  let H' := overwritePalette H (pinAt p i).1 v
  let u := symbolVal p site H'
  let t := decodeSymbolicTrace site H' p
  let q := oldCenteredTrace site H p i c R e he
  have hu : ∀ j,(u j).CutOn m := by
    rintro (j|j)
    · exact hSite _ (pinAt_mem_symbolicSite p j)
    · by_cases hj : (pinAt p j).1 = (pinAt p i).1
      · have hEq : u (.inr j) = v := by simp only [u,symbolVal,H',overwritePalette,ite_eq_left hj]
        rw [hEq]
        exact ComplexBits.checked_cutOn _ _
      · have hEq : u (.inr j) = H (pinAt p j).1 (pinAt p j).2 := by
          simp only [u,symbolVal,H',overwritePalette,ite_eq_right hj]
        rw [hEq]
        exact hH _ (pinAt_mem_symbolicSite p j) hj _
  have hA : ∀ j a,a ∈ symbolicOtherSites p j → m ≤ ((u (.inl j)).name =ᴮ (u a).name)ᶜ := by
    intro j a h
    obtain ⟨k,hkj,rfl⟩ := (mem_symbolicOtherSites p j a).mp h
    exact hApart _ (pinAt_mem_symbolicSite p j) _ (pinAt_mem_symbolicSite p k)
      (fun h => hkj ((pinAt_first_inj p h).symm))
  have hT := symbolicTrace_valid_from_environment site H' p m hu hA
  have hEval : q.eval (site (pinAt p i).1) = t.eval (site (pinAt p i).1) := rfl
  refine ⟨?_,?_⟩
  · unfold polyValid
    refine le_inf (hT.trans inf_le_left) ?_
    unfold paletteValue
    apply le_iInf
    intro k
    have hOld : k.1 ∈ t.pins := Finset.mem_of_mem_erase k.2
    have hNot : k.1 ≠ (pinAt p i).1 := Finset.ne_of_mem_erase k.2
    have hVal : m ≤ ⨆ n, (t.eval (site k.1)).name =ᴮ (H' k.1 n).name :=
      (hT.trans inf_le_right).trans (iInf_le (fun j : {j : J // j ∈ t.pins} =>
        ⨆ n : ℕ, (t.eval (site j.val)).name =ᴮ (H' j.val n).name) ⟨k.1,hOld⟩)
    change m ≤ ⨆ n : ℕ, (t.eval (site k.1)).name =ᴮ (H k.1 n).name
    simpa only [H',overwritePalette,ite_eq_right hNot] using hVal
  · have hPin := symbolic_log_named_pin p m u i hu hA
    have hOv : u (.inr i) = v := by
      change (if (pinAt p i).1 = (pinAt p i).1 then v else H (pinAt p i).1 (pinAt p i).2) = v
      exact ite_eq_left rfl
    rw [hOv] at hPin
    rw [hEval]
    exact hPin

end JSP000930.Negative
