import JSP000930NegativeLiteralAllComplexPointwiseCap

open Fol bSet Cardinal Flypitch Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.SetLanguage JSP000933.PreparedModel JSP000933.BooleanCompletion
  JSP000930.AnalyticSyntax JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000930.Positive JSP000930.SetLanguage

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedOmegaOne_strictly_below_reals
    (hK : BoundsSmallKappaNames B)
    (hLower : (⊤ : B) ≤ injects_into (check BaseSuccPSet) (bv_powerset bSet.omega)) :
    (⊤ : B) ≤ injects_into (check BaseOmegaOne) (bv_powerset bSet.omega) ⊓
      (injects_into (bv_powerset bSet.omega) (check BaseOmegaOne))ᶜ := by
  refine le_inf (injects_into_trans checkedOmegaOne_injects_into_kappa hLower) ?_
  have hCard : Cardinal.mk BaseOmegaOne.Type < GroundContinuumSucc := by
    rw [baseOmegaOne_type_card_r391]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  have hB : injects_into (bv_powerset bSet.omega) (check BaseOmegaOne : bSet B) ≤ ⊥ := by
    have h := injects_into_trans (le_top.trans hLower)
      (le_refl (injects_into (bv_powerset bSet.omega) (check BaseOmegaOne : bSet B)))
    simpa only [checkedSmall_notInject_kappa hK BaseOmegaOne hCard] using h
  rw [le_bot_iff.mp hB,compl_bot]

theorem NamedPaletteSchedule.forces_haymanRefutation (S : NamedPaletteSchedule B)
    (F₀ : CompleteValueMap PreparedBA B)
    (hω : BoundsCountableOmegaOneNames B) (hκ : BoundsSmallKappaNames B)
    (hLower : (⊤ : B) ≤ injects_into (check BaseSuccPSet) (bv_powerset bSet.omega)) :
    (⊤ : B) ⊩[V B] haymanRefutation_f := by
  let m : bSet B := check BaseOmegaOne
  let v₁ : DVec (V B) 1 := DVec.cons m DVec.nil
  let M : STerm 1 := bd_var ⟨0,by decide⟩
  let cap : SForm 1 := bd_and (ordinal_f M)
      (bd_and (strictCard_f omega M) (strictCard_f M omegaSubsets))
  have hM : bTerm v₁ M = m := bTerm_current_r181 DVec.nil m
  have hOm : bTerm v₁ omega = bSet.omega := boolean_realize_bounded_term_omega'
  have hReals : bTerm v₁ omegaSubsets = bSet.bv_powerset bSet.omega := by
    exact (boolean_realize_bounded_term_Powerset' (v := v₁) JSP000933.SetLanguage.omega).trans
      (congrArg bv_powerset hOm)
  have hCap : (⊤ : B) ≤ bTruth v₁ cap := by
    simp only [cap,bTruth_and_eq,bTruth_ordinal_f_r6,
      bTruth_strictCard_f_r6,hM,hOm,hReals]
    have h := checkedOmegaOne_is_nextInitialCard (B := B) hω
    exact le_inf (h.trans inf_le_left)
      (le_inf (h.trans (inf_le_right.trans inf_le_left))
        (checkedOmegaOne_strictly_below_reals hκ hLower))
  let p := bTruth (B := B) DVec.nil haymanBound_f
  have hFalse : p = ⊥ := by
    have hp : p ≤ bTruth DVec.nil haymanBound_f := le_rfl
    unfold haymanBound_f wetzelBound_f at hp
    rw [bTruth_sAll_r181] at hp
    have hGuard := hp.trans (iInf_le _ m)
    change p ≤ bTruth v₁ (bd_imp cap (familyBoundAt_f actualAnalyticSyntax M)) at hGuard
    rw [bTruth_imp_r181] at hGuard
    have hFam := (le_inf hGuard (le_top.trans hCap)).trans Lattice.bv_imp_elim
    unfold familyBoundAt_f at hFam
    rw [bTruth_sAll_r181] at hFam
    have hFor := hFam.trans (iInf_le _ S.family)
    let v₂ : DVec (V B) 2 := DVec.cons S.family v₁
    let F : STerm 2 := bd_var ⟨0,by decide⟩
    change p ≤ bTruth v₂ (bd_imp (bd_and (familyEntire_f actualAnalyticSyntax F)
      (pointwiseBound_f actualAnalyticSyntax F (up M))) (injects_f F (up M))) at hFor
    rw [bTruth_imp_r181,bTruth_and_eq,bTruth_injects_f_r6] at hFor
    have hF : bTerm v₂ F = S.family := bTerm_current_r181 v₁ S.family
    have hM' : bTerm v₂ (up M) = m := (bTerm_up_r181 v₁ S.family M).trans hM
    have hExact : p ≤ imp (bTruth v₂ (familyEntire_f actualAnalyticSyntax F) ⊓
        bTruth v₂ (pointwiseBound_f actualAnalyticSyntax F (up M)))
        (injects_into (bTerm v₂ F) (bTerm v₂ (up M))) := hFor
    have hInj := (le_inf hExact (le_inf
      (le_top.trans (S.family_forces_entire v₂ F hF))
      (le_top.trans (S.forces_pointwiseBound F₀ v₂ F (up M) hF hM')))).trans Lattice.bv_imp_elim
    rw [hF,hM',S.family_notInject_omegaOne hκ] at hInj
    exact le_bot_iff.mp hInj
  change (⊤ : B) ≤ bTruth DVec.nil (bd_not haymanBound_f)
  have hNot : bTruth (B := B) DVec.nil (bd_not haymanBound_f) = pᶜ :=
    boolean_realize_bounded_formula_not
  rw [hNot]
  rw [hFalse,compl_bot]

end JSP000930.Negative
