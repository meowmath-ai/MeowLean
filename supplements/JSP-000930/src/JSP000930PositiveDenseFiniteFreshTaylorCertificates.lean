import JSP000930PositiveFiniteNearbyTaylorBoxes
import JSP000930PositiveRationalCertificateTransport

open Filter

namespace JSP000930.Positive.Cohen

open JSP000930.Positive JSP000930.Positive.Dyadic JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure FreshTaylorCertificate (ab : ℚ × ℚ) where
  N : ℕ
  budgetLeft : ℕ
  budgetRight : ℕ
  boxesLeft : TaylorFinBoxes N
  boxesRight : TaylorFinBoxes N
  robust : ∀ (a b : ℕ → ℂ) (x : ℝ), boxesLeft.matches a → boxesRight.matches b →
    (ab.1 : ℝ) ≤ x → x ≤ (ab.2 : ℝ) →
    ‖(x : ℂ)‖ < (4 : ℝ)/2 ∧ tailBudget budgetLeft N + tailBudget budgetRight N <
      ‖partialSum a (x : ℂ) N - partialSum b (x : ℂ) N‖

noncomputable def FreshTaylorCertificate.value {ab : ℚ × ℚ} (C : FreshTaylorCertificate ab)
    (U V : TaylorSlot → B) : B :=
  (C.boxesLeft.mask (complexCoeffBits U) ⊓ C.boxesRight.mask (complexCoeffBits V)) ⊓
    ((⨅ n : ℕ,radiusBudgetBits (complexCoeffBits U n) 4 C.budgetLeft n) ⊓
      (⨅ n : ℕ,radiusBudgetBits (complexCoeffBits V n) 4 C.budgetRight n))

theorem exists_freshTaylorCertificate (U V : TaylorSlot → B)
    (w : List Bool) (m : B) (hm : m ≠ ⊥)
    (hG : m ≤ validDistinctTaylorPair U V ⊓
      (growthValue (complexCoeffBits U) ⊓ growthValue (complexCoeffBits V))) :
    ∃ (ab : ℚ × ℚ) (C : FreshTaylorCertificate ab) (d : B),
      ProperSubinterval w ab ∧ d ≠ ⊥ ∧ d ≤ m ∧ d ≤ C.value U V := by
  obtain ⟨hU,hV,hGU,hGV⟩ := earlier_values_admissible U V m hG
  obtain ⟨P⟩ := pairedEntire_ground_completion U V m hm (hG.trans inf_le_left) hGU hGV
  let s := unitInterval.follow w
  have hs : (s.left : ℝ) < (s.right : ℝ) := by exact_mod_cast s.positive
  obtain ⟨x,hL,hR,he⟩ := exists_real_ne_in_interval P.leftRadius P.rightRadius P.different hs
  have hi := Interval.follow_inside unitInterval w
  have hxL : 0 ≤ x := by
    have h : (0 : ℝ) ≤ (s.left : ℝ) := by exact_mod_cast hi.1
    exact h.trans hL.le
  have hxR : x ≤ 1 := by
    have h : (s.right : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hi.2
    exact hR.le.trans h
  have hRadius : ‖(x : ℂ)‖ < (4 : ℝ)/2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hxL]
    linarith
  have hBudgetL (n : ℕ) : ‖P.left n‖ * (4 : ℝ)^n ≤ ((P.budgets 3).1 : ℝ) :=
    trace_budget_to_norm (trace_radiusBudget_at P.antitone P.nonzero P.under
      (P.leftTrace n) (hU n) (P.leftBudget 3 n))
  have hBudgetR (n : ℕ) : ‖P.right n‖ * (4 : ℝ)^n ≤ ((P.budgets 3).2 : ℝ) :=
    trace_budget_to_norm (trace_radiusBudget_at P.antitone P.nonzero P.under
      (P.rightTrace n) (hV n) (P.rightBudget 3 n))
  obtain ⟨N,hGap⟩ := (eventually_partialSum_separation (R := 4) P.leftRadius P.rightRadius
    hBudgetL hBudgetR hRadius.le he).exists
  obtain ⟨δ,hδ,hStable⟩ := finiteSeparation_stable (R := 4) hRadius hGap
  obtain ⟨L,i,hiL,hLnear⟩ := finite_complex_boxes_select (N := N) P.antitone
    (complexCoeffBits U) P.left P.leftTrace δ hδ
  obtain ⟨R,j,hjR,hRnear⟩ := finite_complex_boxes_select (N := N) P.antitone
    (complexCoeffBits V) P.right P.rightTrace δ hδ
  let e := min δ (min (x-(s.left : ℝ)) ((s.right : ℝ)-x))
  have heP : 0 < e := lt_min hδ (lt_min (sub_pos.mpr hL) (sub_pos.mpr hR))
  have heD : e ≤ δ := min_le_left _ _
  have heL : e ≤ x-(s.left : ℝ) := (min_le_right _ _).trans (min_le_left _ _)
  have heR : e ≤ (s.right : ℝ)-x := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨a,ha,ha'⟩ := exists_rat_btwn (show x-e < x by linarith)
  obtain ⟨b,hb',hb⟩ := exists_rat_btwn (show x < x+e by linarith)
  let C : FreshTaylorCertificate (a,b) := ⟨N,(P.budgets 3).1,(P.budgets 3).2,L,R,by
    intro a' b' y haBox hbBox hyL hyR
    have hy : dist (y : ℂ) (x : ℂ) < δ := by
      rw [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_lt]
      constructor <;> linarith
    exact hStable a' b' (y : ℂ) (hLnear a' haBox) (hRnear b' hbBox) hy⟩
  let K := max i (max j 3)
  refine ⟨(a,b),C,P.p K,?_,P.nonzero K,P.under K,?_⟩
  · have hA : (s.left : ℝ) < (a : ℝ) := by linarith
    have hAB : (a : ℝ) < (b : ℝ) := ha'.trans hb'
    have hB : (b : ℝ) < (s.right : ℝ) := by linarith
    exact ⟨by exact_mod_cast hA,by exact_mod_cast hAB,by exact_mod_cast hB⟩
  · refine le_inf (le_inf ((P.antitone (le_max_left _ _)).trans hiL)
      ((P.antitone ((le_max_left j 3).trans (le_max_right i _))).trans hjR)) ?_
    refine le_inf (le_iInf (fun n => ?_)) (le_iInf (fun n => ?_))
    · exact (P.antitone ((le_max_right j 3).trans (le_max_right i _))).trans (P.leftBudget 3 n)
    · exact (P.antitone ((le_max_right j 3).trans (le_max_right i _))).trans (P.rightBudget 3 n)

end JSP000930.Positive.Cohen
