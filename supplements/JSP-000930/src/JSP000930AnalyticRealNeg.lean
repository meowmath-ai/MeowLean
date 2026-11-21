import JSP000930AnalyticRealAdd

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

def RatPresentation.opposite (r : RatPresentation) : RatPresentation :=
  ⟨r.neg,r.pos,r.den,r.den_pos⟩

@[simp] theorem RatPresentation.opposite_value (r : RatPresentation) :
    r.opposite.value = - r.value := by
  unfold RatPresentation.opposite RatPresentation.value
  rw [← neg_div]
  ring

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def negCutBits (β : RatPresentation → B) (q : RatPresentation) : B :=
  ⨆ r : RatPresentation, ⨆ (_ : q.value < -r.value), (β r)ᶜ

noncomputable def negCutName (β : RatPresentation → B) : bSet B :=
  weightedRationalSet (negCutBits β)

theorem negCutBits_downward (β : RatPresentation → B) {q t : RatPresentation}
    (h : q.value ≤ t.value) : negCutBits β t ≤ negCutBits β q := by
  unfold negCutBits
  exact iSup_le fun r => iSup_le fun ht => le_iSup_of_le r (le_iSup (fun _ : q.value < -r.value => (β r)ᶜ) (h.trans_lt ht))

theorem negCutBits_rounded (β : RatPresentation → B) (q : RatPresentation) :
    negCutBits β q = ⨆ t : RatPresentation, ⨆ (_ : q.value<t.value), negCutBits β t := by
  apply le_antisymm
  · unfold negCutBits
    refine iSup_le fun r => iSup_le fun hr => ?_
    obtain ⟨t,ht⟩ := ratPresentation_value_surjective ((q.value-r.value)/2)
    have hqt : q.value<t.value := by rw [ht]; linarith
    have htr : t.value < -r.value := by rw [ht]; linarith
    exact le_iSup_of_le t (le_iSup_of_le hqt (le_iSup_of_le r (le_iSup (fun _ : t.value < -r.value => (β r)ᶜ) htr)))
  · exact iSup_le fun t => iSup_le fun hqt => negCutBits_downward β hqt.le

end JSP000930.BooleanAnalysis

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames JSP000933.CantorCodes

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_rationalNeg_named {n : ℕ} (v : DVec (V B) n) (R T : STerm n)
    (r t : RatPresentation) (hR : bTerm v R = ratName r) (hT : bTerm v T = ratName t) :
    bTruth v (rationalNeg_f R T) = crispTruth B (t = r.opposite) := by
  unfold rationalNeg_f
  rw [bTruth_unpackRational_named v R (fun _ : Fin 1 => T) _ r hR]
  let V1 : DVec (V B) (n+1) := DVec.cons (bSet.of_nat r.pos) v
  let V2 : DVec (V B) (n+2) := DVec.cons (bSet.of_nat r.neg) V1
  let V3 : DVec (V B) (n+3) := DVec.cons (bSet.of_nat r.den) V2
  let A : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let C : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  let D : STerm (n+3) := bd_var ⟨0,Nat.succ_pos (n+2)⟩
  change bTruth V3 (bd_equal (up3 T) (pair' (up C) (pair' (up2 A) D))) = _
  have hT' : bTerm V3 (up3 T) = ratName t :=
    (bTerm_up3_r181 v (bSet.of_nat r.pos) (bSet.of_nat r.neg) (bSet.of_nat r.den) T).trans hT
  rw [bTruth_equal_r181, hT']
  exact ratName_eq_crisp t r.opposite

private theorem iSup_crispEquality_select_rat (r : RatPresentation) (F : RatPresentation → B) :
    (⨆ s : RatPresentation, crispTruth B (s = r) ⊓ F s) = F r := by
  apply le_antisymm
  · refine iSup_le fun s => ?_
    by_cases h : s = r
    · subst s
      simp [crispTruth]
    · simp [crispTruth,h]
  · exact (by simpa [crispTruth] using
      (le_iSup (fun s : RatPresentation => crispTruth B (s = r) ⊓ F s) r))

theorem bTruth_realNegApprox_weighted {n : ℕ} (v : DVec (V B) n)
    (X Q : STerm n) (β : RatPresentation → B) (q : RatPresentation)
    (hX : bTerm v X = weightedRationalSet β) (hQ : bTerm v Q = ratName q) :
    bTruth v (realNegApprox_f X Q) = negCutBits β q := by
  simp only [realNegApprox_f,bTruth_rationalEx,negCutBits]
  apply iSup_congr
  intro r
  let vr : DVec (V B) (n+1) := DVec.cons (ratName (B := B) r) v
  let vrt (t : RatPresentation) : DVec (V B) (n+2) := DVec.cons (ratName (B := B) t) vr
  let T1 : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let T2 : STerm (n+2) := bd_var ⟨0,Nat.succ_pos (n+1)⟩
  change (⨆ t : RatPresentation, bTruth (vrt t) (bd_and (rationalNeg_f (up T1) T2)
    (bd_and (bd_not (mem' (up T1) (up2 X))) (rationalLT_f (up2 Q) T2)))) = _
  have ht (t : RatPresentation) : bTerm (vrt t) T2 = ratName t :=
    bTerm_current_r181 vr (ratName t)
  have hr (t : RatPresentation) : bTerm (vrt t) (up T1) = ratName r :=
    (bTerm_up_r181 vr (ratName t) T1).trans (bTerm_current_r181 v (ratName r))
  have hx (t : RatPresentation) : bTerm (vrt t) (up2 X) = weightedRationalSet β :=
    (bTerm_up2_r181 v (ratName r) (ratName t) X).trans hX
  have hq (t : RatPresentation) : bTerm (vrt t) (up2 Q) = ratName q :=
    (bTerm_up2_r181 v (ratName r) (ratName t) Q).trans hQ
  simp only [boolean_realize_bounded_formula_and,boolean_realize_bounded_formula_not,
    boolean_realize_bounded_formula_mem',hr,hx,ratName_mem_weightedRationalSet,
    fun t => bTruth_rationalNeg_named (vrt t) (up T1) T2 r t (hr t) (ht t),
    fun t => bTruth_rationalLT_named (vrt t) (up2 Q) T2 q t (hq t) (ht t),
    iSup_crispEquality_select_rat,RatPresentation.opposite_value,iSup_inf_crisp_ratLower]

theorem bTruth_realNeg_weighted {n : ℕ} (v : DVec (V B) n) (X Y : STerm n)
    (β γ : RatPresentation → B)
    (hX : bTerm v X = weightedRationalSet β) (hY : bTerm v Y = weightedRationalSet γ) :
    bTruth v (realNeg_f X Y) = (weightedRationalSet γ =ᴮ negCutName β) := by
  rw [realNeg_f,bTruth_rationalAll,negCutName,weightedRationalSet_eq_bitEq]
  apply iInf_congr
  intro q
  let vq := DVec.cons (ratName (B := B) q) v
  let Q : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  have hXq := (bTerm_up_r181 v (ratName q) X).trans hX
  have hYq := (bTerm_up_r181 v (ratName q) Y).trans hY
  change bTruth vq (bd_biimp (mem' Q (up Y)) (realNegApprox_f (up X) Q)) = _
  simp only [boolean_realize_bounded_formula_biimp,equiv_bitEq_r181,
    boolean_realize_bounded_formula_mem',hYq,bTerm_current_r181,
    ratName_mem_weightedRationalSet,
    bTruth_realNegApprox_weighted vq (up X) Q β q hXq (bTerm_current_r181 v (ratName q))]
  change bitEq (bTerm vq Q ∈ᴮ bTerm vq (up Y)) (negCutBits β q) = _
  rw [show bTerm vq Q = ratName q from bTerm_current_r181 v (ratName q), hYq,
    ratName_mem_weightedRationalSet]

end JSP000930.AnalyticSyntax
