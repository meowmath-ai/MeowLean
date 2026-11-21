import JSP000930NegativeCoefficientGrid
import Mathlib.SetTheory.Cardinal.Order

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def earlierChoiceJoin (h : I → B) (i : I) : B :=
  ⨆ j : {j : I // WellOrderingRel j i}, h j.val

noncomputable def firstChoiceCell (h : I → B) (i : I) : B :=
  h i ⊓ (earlierChoiceJoin h i)ᶜ

theorem firstChoiceCell_le_active (h : I → B) (i : I) : firstChoiceCell h i ≤ h i :=
  inf_le_left

theorem firstChoiceCell_disjoint (h : I → B) {i j : I} (hij : i ≠ j) :
    Disjoint (firstChoiceCell h i) (firstChoiceCell h j) := by
  have earlier {a b : I} (hab : WellOrderingRel a b) :
      Disjoint (firstChoiceCell h a) (firstChoiceCell h b) := by
    have hu : firstChoiceCell h a ≤ earlierChoiceJoin h b :=
      (firstChoiceCell_le_active h a).trans (le_iSup (fun j : {j : I // WellOrderingRel j b} => h j.val) (⟨a,hab⟩ : {j : I // WellOrderingRel j b}))
    have hv : firstChoiceCell h b ≤ (earlierChoiceJoin h b)ᶜ := inf_le_right
    exact disjoint_iff_inf_le.mpr
      ((le_inf (inf_le_left.trans hu) (inf_le_right.trans hv)).trans (by simp))
  by_cases h₁ : WellOrderingRel i j
  · exact earlier h₁
  · have h₂ : WellOrderingRel j i := by
      by_contra h₂
      exact hij (Std.Trichotomous.trichotomous i j h₁ h₂)
    exact (earlier h₂).symm

theorem iSup_firstChoiceCell (h : I → B) :
    (⨆ i,firstChoiceCell h i) = ⨆ i,h i := by
  apply le_antisymm
  · exact iSup_le fun i => (firstChoiceCell_le_active h i).trans (le_iSup _ i)
  · apply iSup_le
    intro t
    refine (IsWellOrder.wf (α := I) (r := WellOrderingRel)).induction (C := fun i => h i ≤ ⨆ j, firstChoiceCell h j) t ?_
    intro i ih
    let x := earlierChoiceJoin h i
    have hx : x ≤ ⨆ i, firstChoiceCell h i := by
      exact iSup_le fun j : {j : I // WellOrderingRel j i} => ih j.val j.property
    calc
      h i = h i ⊓ (x ⊔ xᶜ) := by simp
      _ = (h i ⊓ x) ⊔ firstChoiceCell h i := by
        simp only [firstChoiceCell,x,inf_sup_left]
      _ ≤ _ := sup_le (inf_le_right.trans hx) (le_iSup _ i)

noncomputable def chooseCutBits (h : I → B) (u : I → RatPresentation → B) (q : RatPresentation) : B :=
  ⨆ i,firstChoiceCell h i ⊓ u i q

theorem chooseCutBits_mask (h : I → B) (u : I → RatPresentation → B) (i : I) (q : RatPresentation) :
    firstChoiceCell h i ⊓ chooseCutBits h u q = firstChoiceCell h i ⊓ u i q := by
  unfold chooseCutBits
  rw [inf_iSup_eq]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    by_cases hj : i=j
    · subst j
      exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · have hh : firstChoiceCell h i ⊓ firstChoiceCell h j ≤ ⊥ :=
        disjoint_iff_inf_le.mp (firstChoiceCell_disjoint h hj)
      exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans hh).trans bot_le
  · exact le_iSup_of_le i (le_inf inf_le_left le_rfl)

theorem properCutOn_iSup {T : Type} (p : T → B) (u : RatPresentation → B)
    (h : ∀ t, ProperCutOn (p t) u) : ProperCutOn (⨆ t,p t) u := by
  refine ⟨iSup_le fun t => (h t).1,iSup_le fun t => (h t).2.1,?_,?_⟩
  · intro q r hqr
    rw [iSup_inf_eq]
    exact iSup_le fun t => (h t).2.2.1 q r hqr
  · intro q
    rw [iSup_inf_eq]
    exact iSup_le fun t => (h t).2.2.2 q

noncomputable def chosenPolyCoeff (h : I → B) (f : I → List (ComplexBits B)) (n : ℕ) :
    ComplexBits B :=
  ⟨chooseCutBits h (fun i => (zeroPaddedPoly (f i) n).re),
   chooseCutBits h (fun i => (zeroPaddedPoly (f i) n).im)⟩

theorem chosenPolyCoeff_on_cell (h : I → B) (f : I → List (ComplexBits B)) (n : ℕ) (i : I) :
    sameMaskedComplex (firstChoiceCell h i) (chosenPolyCoeff h f n) (zeroPaddedPoly (f i) n) :=
  ⟨chooseCutBits_mask h (fun i => (zeroPaddedPoly (f i) n).re) i,
   chooseCutBits_mask h (fun i => (zeroPaddedPoly (f i) n).im) i⟩

theorem chosenPolyCoeff_cutOn (h : I → B) (f : I → List (ComplexBits B)) (m : B)
    (hCover : m ≤ ⨆ i,h i) (hf : ∀ i,∀ c ∈ f i,c.CutOn (m ⊓ h i)) (n : ℕ) :
    (chosenPolyCoeff h f n).CutOn m := by
  let p (i : I) := m ⊓ firstChoiceCell h i
  have hM : m ≤ ⨆ i,p i := by
    simp only [p,← inf_iSup_eq,iSup_firstChoiceCell]
    exact le_inf le_rfl hCover
  have hc (i : I) : (zeroPaddedPoly (f i) n).CutOn (p i) :=
    zeroPaddedPoly_cutOn (f i) (p i) (fun a ha =>
      JSP000930.AnalyticSyntax.complexCutOn_mono (inf_le_inf_left _ (firstChoiceCell_le_active h i))
        (hf i a ha)) n
  have hm (i : I) : sameMaskedComplex (p i) (chosenPolyCoeff h f n) (zeroPaddedPoly (f i) n) := by
    obtain ⟨hr,hi⟩ := chosenPolyCoeff_on_cell h f n i
    constructor
    · intro q
      change (m ⊓ firstChoiceCell h i) ⊓ _ = (m ⊓ firstChoiceCell h i) ⊓ _
      rw [inf_assoc,hr q,← inf_assoc]
    · intro q
      change (m ⊓ firstChoiceCell h i) ⊓ _ = (m ⊓ firstChoiceCell h i) ⊓ _
      rw [inf_assoc,hi q,← inf_assoc]
  have hRe (i : I) : ProperCutOn (p i) (chosenPolyCoeff h f n).re :=
    properCutOn_of_same_mask (hc i).1 (fun q => ((hm i).1 q).symm)
  have hIm (i : I) : ProperCutOn (p i) (chosenPolyCoeff h f n).im :=
    properCutOn_of_same_mask (hc i).2 (fun q => ((hm i).2 q).symm)
  exact ⟨JSP000930.BooleanAnalysis.properCutOn_mono hM (properCutOn_iSup p _ hRe),
    JSP000930.BooleanAnalysis.properCutOn_mono hM (properCutOn_iSup p _ hIm)⟩

end JSP000930.Negative
