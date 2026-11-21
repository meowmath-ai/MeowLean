import JSP000930NegativeLocalComplexTrial
import JSP000930NegativeCofinalSiteRequestSchedule

open bSet Lattice Cardinal
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.CantorCodes
  JSP000933.RelativeOCA JSP000933.PreparedModel
  JSP000930.Positive JSP000930.BooleanAnalysis JSP000930.Positive.Cohen

theorem PlacementBook.trialsCover
    {N : Type} (F : PlacementBook N) (Q : ValuedPoset PreparedBA N)
    (hQ : ForcesRelativeCCC Q)
    (z : ComplexBits (TotalBA Q)) (p : TotalBA Q) (hz : z.CutOn p) :
    p ≤ ⨆ i : PlacementTrialIndex,
      (z.name =ᴮ (F.trial Q i).name) ⊓ trialValidity (F.trial Q i) := by
  let x := packRealCut z.re
  let y := packRealCut z.im
  let U (i : PlacementTableIndex) := realEqValue x (F.row Q i)
  let V (j : PlacementTableIndex) := realEqValue y (F.row Q j)
  let m (i j : PlacementTableIndex) := p ⊓ (U i ⊓ V j)
  have hsum : (⨆ i,⨆ j,m i j) = p := by
    have hU : (⨆ i,U i) = ⊤ := F.rowsCover Q hQ x
    have hV : (⨆ j,V j) = ⊤ := F.rowsCover Q hQ y
    change (⨆ i,⨆ j,p ⊓ (U i ⊓ V j)) = p
    simp only [← inf_iSup_eq,hV,inf_top_eq,hU]
  rw [← hsum]
  apply iSup_le
  intro i
  apply iSup_le
  intro j
  apply le_iSup_of_le (i,j)
  let t := F.trial Q (i,j)
  have hm : m i j ≤ p := inf_le_left
  have hU : m i j ≤ U i := inf_le_right.trans inf_le_left
  have hV : m i j ≤ V j := inf_le_right.trans inf_le_right
  letI := taylorSlotEncodable
  have eqr (q : RatPresentation) : m i j ⊓ z.re q = m i j ⊓ t.re q := by
    have h := (le_realEqValue_iff_r126 _ _ _).mp hU (Encodable.encode ((0,false,q) : TaylorSlot))
    change m i j ⊓ realCutRow x q = m i j ⊓ t.re q at h
    simpa only [x,realCutRow_pack] using h
  have eqi (q : RatPresentation) : m i j ⊓ z.im q = m i j ⊓ t.im q := by
    have h := (le_realEqValue_iff_r126 _ _ _).mp hV (Encodable.encode ((0,false,q) : TaylorSlot))
    change m i j ⊓ realCutRow y q = m i j ⊓ t.im q at h
    simpa only [y,realCutRow_pack] using h
  exact le_inf (sameMaskedComplex_name ⟨eqr,eqi⟩)
    ((le_trialValidity_iff _ _).mpr
      ⟨properCutOn_of_same_mask (JSP000930.Positive.properCutOn_mono hm hz.1) eqr,
       properCutOn_of_same_mask (JSP000930.Positive.properCutOn_mono hm hz.2) eqi⟩)

end JSP000930.Negative
