import JSP000930AnalyticRationalOps
import JSP000930AnalyticRealCutTruth
import JSP000930AnalyticCutAdd

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames JSP000933.CantorCodes

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem iSup_ratCrisp_result (y l : ℚ) :
    (⨆ z : RatPresentation, crispTruth B (y = z.value) ⊓
       crispTruth B (l < z.value)) = crispTruth B (l < y) := by
  by_cases h : l < y
  · rw [show crispTruth B (l < y) = ⊤ by simp [crispTruth,h]]
    obtain ⟨z,hz⟩ := ratPresentation_value_surjective y
    apply top_unique
    have hh : crispTruth B (y = z.value) ⊓ crispTruth B (l < z.value) = ⊤ := by
      simp [crispTruth,h,hz]
    exact (le_of_eq hh.symm).trans (le_iSup (fun t : RatPresentation => crispTruth B (y = t.value) ⊓ crispTruth B (l < t.value)) z)
  · rw [show crispTruth B (l < y) = (⊥ : B) by simp [crispTruth,h]]
    apply le_bot_iff.mp
    refine iSup_le fun z => ?_
    by_cases hz : y = z.value
    · simp [crispTruth,← hz,h]
    · simp [crispTruth,hz]

theorem iSup_inf_crisp_ratLower (t : B) (P : Prop) [Decidable P] :
    (t ⊓ crispTruth B P) = ⨆ (_ : P), t := by
  by_cases h : P <;> simp [crispTruth,h]

theorem bTruth_realAddApprox_weighted {n : ℕ} (v : DVec (V B) n)
    (X Y Q : STerm n) (u w : RatPresentation → B) (q : RatPresentation)
    (hX : bTerm v X = weightedRationalSet u) (hY : bTerm v Y = weightedRationalSet w)
    (hQ : bTerm v Q = ratName q) :
    bTruth v (realAddApprox_f X Y Q) = addCutBits u w q := by
  let ta : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let tb : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let tc : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  unfold realAddApprox_f addCutBits
  rw [bTruth_exInWeightedRational v X u hX]
  apply iSup_congr
  intro r
  have hY' : bTerm (DVec.cons (ratName r) v) (up Y) = weightedRationalSet w :=
    (bTerm_up_r181 v (ratName r) Y).trans hY
  rw [bTruth_exInWeightedRational _ (up Y) w hY',inf_iSup_eq]
  apply iSup_congr
  intro s
  rw [bTruth_rationalEx]
  let V1 : DVec (V B) (n+1) := DVec.cons (ratName (B := B) r) v
  let V2 : DVec (V B) (n+2) := DVec.cons (ratName (B := B) s) V1
  let V3 (t : RatPresentation) : DVec (V B) (n+3) := DVec.cons (ratName (B := B) t) V2
  have hmat (t : RatPresentation) :
      bTruth (V3 t) (bd_and (rationalAdd_f (up2 ta) (up tb) tc)
        (rationalLT_f (up3 Q) tc)) =
      crispTruth B (r.value+s.value=t.value) ⊓ crispTruth B (q.value<t.value) := by
    have hAnd : bTruth (V3 t) (bd_and (rationalAdd_f (up2 ta) (up tb) tc)
        (rationalLT_f (up3 Q) tc)) =
        bTruth (V3 t) (rationalAdd_f (up2 ta) (up tb) tc) ⊓ bTruth (V3 t) (rationalLT_f (up3 Q) tc) :=
      boolean_realize_bounded_formula_and
    rw [hAnd]
    have ha : bTerm (V3 t) (up2 ta) = ratName r := by
      simp only [V3,V2,V1,ta,bTerm_up2_r181,bTerm_current_r181]
    have hb : bTerm (V3 t) (up tb) = ratName s := by
      simp only [V3,V2,tb,bTerm_up_r181,bTerm_current_r181]
    have hc : bTerm (V3 t) tc = ratName t :=
      bTerm_current_r181 V2 (ratName t)
    have hq : bTerm (V3 t) (up3 Q) = ratName q := by
      simp only [V3,V2,V1,bTerm_up3_r181,hQ]
    rw [bTruth_rationalAdd_named _ _ _ _ r s t ha hb hc,
      bTruth_rationalLT_named _ _ _ q t hq hc]
  change (u r ⊓ (w s ⊓ (⨆ t : RatPresentation,
    bTruth (V3 t) (bd_and (rationalAdd_f (up2 ta) (up tb) tc)
        (rationalLT_f (up3 Q) tc))))) = _
  simp only [hmat]
  rw [iSup_ratCrisp_result]
  simp only [iSup_inf_crisp_ratLower]
  rw [inf_iSup_eq]

theorem weightedRationalSet_eq_bitEq (β γ : RatPresentation → B) :
    (weightedRationalSet β =ᴮ weightedRationalSet γ) =
      ⨅ q : RatPresentation, bitEq (β q) (γ q) := by
  rw [weightedRationalSet_eq]
  apply le_antisymm
  · refine le_iInf fun q => ?_
    exact le_inf (inf_le_left.trans (iInf_le _ q)) (inf_le_right.trans (iInf_le _ q))
  · exact le_inf (le_iInf fun q => (iInf_le _ q).trans inf_le_left)
      (le_iInf fun q => (iInf_le _ q).trans inf_le_right)

theorem bTruth_realAdd_weighted {n : ℕ} (v : DVec (V B) n)
    (X Y Z : STerm n) (u w s : RatPresentation → B)
    (hX : bTerm v X = weightedRationalSet u) (hY : bTerm v Y = weightedRationalSet w)
    (hZ : bTerm v Z = weightedRationalSet s) :
    bTruth v (realAdd_f X Y Z) = (weightedRationalSet s =ᴮ addCutName u w) := by
  rw [realAdd_f,bTruth_rationalAll,addCutName,weightedRationalSet_eq_bitEq]
  apply iInf_congr
  intro q
  let vq : DVec (V B) (n + 1) := DVec.cons (ratName (B := B) q) v
  let Q : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hXq := (bTerm_up_r181 v (ratName q) X).trans hX
  have hYq := (bTerm_up_r181 v (ratName q) Y).trans hY
  have hZq := (bTerm_up_r181 v (ratName q) Z).trans hZ
  change bTruth vq (bd_biimp (mem' Q (up Z)) (realAddApprox_f (up X) (up Y) Q)) = _
  simp only [boolean_realize_bounded_formula_biimp,equiv_bitEq_r181,
    boolean_realize_bounded_formula_mem',hZq,bTerm_current_r181,
    ratName_mem_weightedRationalSet,
    bTruth_realAddApprox_weighted vq (up X) (up Y) Q u w q hXq hYq
      (bTerm_current_r181 v (ratName q))]
  change bitEq (bTerm vq Q ∈ᴮ bTerm vq (up Z)) (addCutBits u w q) = _
  rw [show bTerm vq Q = ratName q from bTerm_current_r181 v (ratName q), hZq,
    ratName_mem_weightedRationalSet]

end JSP000930.AnalyticSyntax
