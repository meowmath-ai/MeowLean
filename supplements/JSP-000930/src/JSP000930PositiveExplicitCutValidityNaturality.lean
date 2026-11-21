import JSP000930PositiveDistinctMixedTaylorGroundCompletion
import JSP000930PositiveSubmodelTaylorNameTransport

namespace JSP000930.Positive

open JSP000933.BooleanCompletion JSP000930.BooleanAnalysis

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B]
  [NontrivialCompleteBooleanAlgebra C]

def properCutValue (u : RatPresentation → B) : B :=
  (⨆ q,u q) ⊓ ((⨆ q,(u q)ᶜ) ⊓
    ((⨅ q : RatPresentation,⨅ r : RatPresentation,⨅ (_ : q.value ≤ r.value),(u r)ᶜ ⊔ u q) ⊓
      (⨅ q : RatPresentation,(u q)ᶜ ⊔
        (⨆ r : RatPresentation,⨆ (_ : q.value < r.value),u r))))

theorem le_properCutValue_iff (u : RatPresentation → B) (p : B) :
    p ≤ properCutValue u ↔ ProperCutOn p u := by
  unfold properCutValue ProperCutOn
  simp only [le_inf_iff,le_iInf_iff]
  constructor
  · rintro ⟨ha,hb,hc,hd⟩
    refine ⟨ha,hb,?_,?_⟩
    · intro q r h
      exact _root_.deduction.mpr (hc q r h)
    · intro q
      exact _root_.deduction.mpr (hd q)
  · rintro ⟨ha,hb,hc,hd⟩
    refine ⟨ha,hb,?_,?_⟩
    · intro q r h
      exact _root_.deduction.mp (hc q r h)
    · intro q
      exact _root_.deduction.mp (hd q)

theorem completeMap_proof_iSup (F : CompleteValueMap B C) (P : Prop) (b : B) :
    F.toFun (⨆ _ : P,b) = ⨆ _ : P,F.toFun b := by
  by_cases h : P
  · have hEq {D : Type} [CompleteLattice D] (x : D) : (⨆ _ : P,x) = x :=
      le_antisymm (iSup_le (fun _ => le_rfl)) (le_iSup (fun _ : P => x) h)
    rw [hEq b,hEq (F.toFun b)]
  · have hEq {D : Type} [CompleteLattice D] (x : D) : (⨆ _ : P,x) = ⊥ :=
      le_antisymm (iSup_le (fun h' => False.elim (h h'))) bot_le
    rw [hEq b,hEq (F.toFun b),F.map_bot]

theorem completeMap_proof_iInf (F : CompleteValueMap B C) (P : Prop) (b : B) :
    F.toFun (⨅ _ : P,b) = ⨅ _ : P,F.toFun b := by
  by_cases h : P
  · have hEq {D : Type} [CompleteLattice D] (x : D) : (⨅ _ : P,x) = x :=
      le_antisymm (iInf_le _ h) (le_iInf (fun _ => le_rfl))
    rw [hEq b,hEq (F.toFun b)]
  · have hEq {D : Type} [CompleteLattice D] (x : D) : (⨅ _ : P,x) = ⊤ :=
      le_antisymm le_top (le_iInf (fun h' => False.elim (h h')))
    rw [hEq b,hEq (F.toFun b),F.map_top]

theorem properCutValue_map (F : CompleteValueMap B C) (u : RatPresentation → B) :
    F.toFun (properCutValue u) = properCutValue (fun q => F.toFun (u q)) := by
  simp only [properCutValue,F.map_inf,F.map_sup_r93,F.map_compl,F.map_iSup,F.map_iInf,
    completeMap_proof_iSup,completeMap_proof_iInf]

end JSP000930.Positive
