import JSP000930PositiveCommonNativeEvaluationGroundValues

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000930.Positive JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def realAxisBits (u : RatPresentation → B) : ComplexBits B :=
  ⟨u,checkedRealBits 0⟩

theorem certificate_forces_native_separation
    {ab : ℚ × ℚ} (C : FreshTaylorCertificate ab)
    (U V : TaylorSlot → B) (z : RatPresentation → B) (m : B)
    (hCU : ∀ n,(complexCoeffBits U n).CutOn m)
    (hCV : ∀ n,(complexCoeffBits V n).CutOn m)
    (hz : ProperCutOn m z)
    (hGU : GrowthOn m (complexCoeffBits U)) (hGV : GrowthOn m (complexCoeffBits V))
    (lo hi : RatPresentation) (hlo : lo.value = ab.1) (hhi : hi.value = ab.2)
    (hZ : m ≤ z lo ⊓ (z hi)ᶜ) (hCert : m ≤ C.value U V) :
    m ≤ ((taylorLimitBits (complexCoeffBits U) (realAxisBits z)).name =ᴮ
      (taylorLimitBits (complexCoeffBits V) (realAxisBits z)).name)ᶜ := by
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iff_inf_le.mpr
  let A := complexCoeffBits U
  let D := complexCoeffBits V
  let Z := realAxisBits z
  let p := m ⊓ ((taylorLimitBits A Z).name =ᴮ (taylorLimitBits D Z).name)
  change p ≤ ⊥
  apply le_bot_iff.mpr
  by_contra hn
  have hp : p ≤ m := inf_le_left
  have hA (n : ℕ) : (A n).CutOn p :=
    ⟨JSP000930.Positive.properCutOn_mono hp (hCU n).1,
      JSP000930.Positive.properCutOn_mono hp (hCU n).2⟩
  have hD (n : ℕ) : (D n).CutOn p :=
    ⟨JSP000930.Positive.properCutOn_mono hp (hCV n).1,
      JSP000930.Positive.properCutOn_mono hp (hCV n).2⟩
  have hzp : Z.CutOn p :=
    ⟨JSP000930.Positive.properCutOn_mono hp hz,
      JSP000930.Positive.properCutOn_mono le_top (checkedRealBits_properCut 0)⟩
  obtain ⟨P⟩ := commonTaylorGroundValues_exists A D Z p hn hA hD hzp (hGU.mono hp) (hGV.mono hp)
  have hEq := trace_complex_eq P.antitone P.nonzero P.under
    P.leftValTrace P.rightValTrace (show p ≤ _ from inf_le_right)
  have hC := (P.under 0).trans (hp.trans hCert)
  have hL := finite_complex_boxes_of_decision_traces P.antitone P.nonzero A P.left P.leftTrace
    C.boxesLeft 0 (hC.trans (inf_le_left.trans inf_le_left))
  have hR := finite_complex_boxes_of_decision_traces P.antitone P.nonzero D P.right P.rightTrace
    C.boxesRight 0 (hC.trans (inf_le_left.trans inf_le_right))
  have hzbox := TaylorCoordinateBox.trace_sound P.antitone P.nonzero P.pointTrace.1 ⟨lo,hi⟩
    0 ((P.under 0).trans (hp.trans hZ))
  have hzlo : (ab.1 : ℝ) ≤ P.point.re := by simpa only [TaylorCoordinateBox.realizes,hlo] using hzbox.1
  have hzhi : P.point.re ≤ (ab.2 : ℝ) := by simpa only [TaylorCoordinateBox.realizes,hhi] using hzbox.2
  have hzI : P.point.im = 0 := trace_cut_eq P.antitone P.nonzero P.under
    P.pointTrace.2 (checkedRealBits_traces P.p 0) bv_refl
  have hPoint : P.point = (P.point.re : ℂ) := by
    apply Complex.ext <;> simp [hzI]
  have hTest := C.robust P.left P.right P.point.re hL hR hzlo hzhi
  have hBoundL (n : ℕ) : ‖P.left n‖ * (4 : ℝ)^n ≤ (C.budgetLeft : ℝ) :=
    trace_budget_to_norm (trace_radiusBudget_at P.antitone P.nonzero P.under (P.leftTrace n)
      (hA n) (hC.trans (inf_le_right.trans (inf_le_left.trans (iInf_le _ n)))))
  have hBoundR (n : ℕ) : ‖P.right n‖ * (4 : ℝ)^n ≤ (C.budgetRight : ℝ) :=
    trace_budget_to_norm (trace_radiusBudget_at P.antitone P.nonzero P.under (P.rightTrace n)
      (hD n) (hC.trans (inf_le_right.trans (inf_le_right.trans (iInf_le _ n)))))
  have hNe := evaluate_ne_of_partialSum_separation (R := 4) P.leftRadius P.rightRadius
    hBoundL hBoundR hTest.1.le hTest.2
  exact hNe (by rw [← hPoint,P.leftEval,P.rightEval,hEq])

end JSP000930.Positive.Cohen
