import JSP000930PositiveExactPointwiseCapWiring

open Fol bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive.Cohen

open JSP000933.SetLanguage JSP000933.PreparedModel JSP000933.BooleanCompletion
  JSP000933.ForcingTransport JSP000930.SetLanguage

set_option backward.isDefEq.respectTransparency false

private theorem wetzel_bTerm_omegaSubsets {n : ℕ} (v : DVec (V WetzelCohenBA) n) :
    bTerm v omegaSubsets = bSet.bv_powerset bSet.omega := by
  change bSet.bv_powerset (bTerm v JSP000933.SetLanguage.omega) = _
  exact congrArg bSet.bv_powerset (boolean_realize_bounded_term_omega' (v := v))

theorem wetzelCohen_forces_haymanBound_of_reserveAnalytic
    (hA : ReserveAnalyticLaw) :
    (⊤ : WetzelCohenBA) ⊩[V WetzelCohenBA] haymanBound_f := by
  change (⊤ : WetzelCohenBA) ≤ bTruth DVec.nil haymanBound_f
  unfold haymanBound_f wetzelBound_f
  rw [bTruth_sAll_r181]
  apply le_iInf
  intro m
  rw [bTruth_imp_r181,← _root_.deduction,top_inf_eq]
  simp only [boolean_realize_bounded_formula_and,bTruth_ordinal_f_r6,bTruth_strictCard_f_r6,
    bTerm_current_r181,boolean_realize_bounded_term_omega',wetzel_bTerm_omegaSubsets]
  let cap : WetzelCohenBA := Ord m ⊓
    ((injects_into bSet.omega m ⊓ (injects_into m bSet.omega)ᶜ) ⊓
      (injects_into m (bv_powerset bSet.omega) ⊓
        (injects_into (bv_powerset bSet.omega) m)ᶜ))
  let u : DVec (V WetzelCohenBA) 1 := DVec.cons m DVec.nil
  let M : STerm 1 := bd_var ⟨0,by decide⟩
  change cap ≤ bTruth u (familyBoundAt_f actualAnalyticSyntax M)
  have hCap := checked_gap_cap_eq_omegaOne m cap inf_le_left
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_right.trans inf_le_right))
    (le_top.trans (checkedOmegaOne_is_nextInitialCard wetzelCohen_boundsOmegaOne))
    (le_top.trans (checkedKappa_is_nextInitialCard
      (totalBaseMap wetzelCohenPoset) wetzelCohen_boundsKappa))
    (le_top.trans wetzelCohen_reals_inject_into_kappa)
  unfold familyBoundAt_f
  rw [bTruth_sAll_r181]
  apply le_iInf
  intro F
  rw [bTruth_imp_r181,← _root_.deduction]
  let v : DVec (V WetzelCohenBA) 2 := DVec.cons F u
  let Fvar : STerm 2 := bd_var ⟨0,by decide⟩
  let p : WetzelCohenBA := cap ⊓
    bTruth v (bd_and (familyEntire_f actualAnalyticSyntax Fvar)
      (pointwiseBound_f actualAnalyticSyntax Fvar (up M)))
  change p ≤ bTruth v (injects_f Fvar (up M))
  rw [bTruth_injects_f_r6]
  simp only [v,u,Fvar,M,bTerm_up_r181,bTerm_current_r181]
  have hp : p ≤ bTruth v (familyEntire_f actualAnalyticSyntax Fvar) ⊓
      bTruth v (pointwiseBound_f actualAnalyticSyntax Fvar (up M)) := by
    have hAnd : bTruth v (bd_and (familyEntire_f actualAnalyticSyntax Fvar)
        (pointwiseBound_f actualAnalyticSyntax Fvar (up M))) = _ :=
      boolean_realize_bounded_formula_and
    exact inf_le_right.trans_eq hAnd
  have hM : bTerm v (up M) = m :=
    (bTerm_up_r181 u F M).trans (bTerm_current_r181 DVec.nil m)
  have hf := actual_pointwise_bound_within_omegaOne hA v Fvar (up M) p
    (hp.trans inf_le_left) (hp.trans inf_le_right)
    (by rw [hM]; exact inf_le_left.trans (hCap.trans inf_le_left))
  have hResult : p ≤ injects_into F (check BaseOmegaOne) := by
    exact hf
  exact injects_into_trans hResult (inf_le_left.trans (hCap.trans inf_le_right))

theorem wetzelCohen_forces_haymanAtAlephTwo_of_reserveAnalytic
    (hA : ReserveAnalyticLaw) :
    (⊤ : WetzelCohenBA) ⊩[V WetzelCohenBA] haymanAtAlephTwo_f := by
  change (⊤ : WetzelCohenBA) ≤ bTruth DVec.nil
    (bd_and continuumAlephTwo_f haymanBound_f)
  have hAnd : bTruth (DVec.nil : DVec (V WetzelCohenBA) 0)
      (bd_and continuumAlephTwo_f haymanBound_f) = _ := boolean_realize_bounded_formula_and
  rw [hAnd]
  exact le_inf wetzelCohen_forces_continuumAlephTwo
    (wetzelCohen_forces_haymanBound_of_reserveAnalytic hA)

end JSP000930.Positive.Cohen
