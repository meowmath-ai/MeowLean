import JSP000933ActualBadFaceErrorTransfer

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def namedFaceBadValue (G F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ)
    (a z : ℕ → B) : B :=
  ⨅ y : ℕ → B, (eventuallySmallError true k (G (namedFacePoint a z y))
    (F (bitsMeet c (namedFacePoint a z y))))ᶜ

noncomputable def badChildFaceValue (G F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ)
    (a z b w : ℕ → B) : B :=
  faceRefinementValue a z b w⊓(actualLongBlockLarge b⊓namedFaceBadValue G F c k b w)

theorem noUniform_has_actualBadChild_refinement_r325 {p q : B}
    (F : CoherentSelectedIso B p) (hF : NameMapExt F.toName)
    (G : (ℕ → B) → ℕ → B) (hG : NamedContinuousOn p G)
    (c d z : ℕ → B) (k : ℕ) (hk : k≠0) (hq : q≠⊥) (hqp : q≤p)
    (hNo : q≤(existsLargeUniformCapValue F.toName c k)ᶜ)
    (hD : q≤bitsBelowValue d c) (hL : q≤actualLongBlockLarge d) :
    ∃ (r : B) (a w : ℕ → B), r≠⊥ ∧ r≤q ∧ r≤badChildFaceValue G F.toName c (64*k) d z a w := by
  classical
  obtain ⟨S,hS⟩ := exists_actualLarge_split_r308 d hL
  let a := actualCoordinateFace d S false
  let b := actualCoordinateFace d S true
  have hAB (m : ℕ) : a m⊓b m=⊥ := actualCoordinateFace_disjoint_r308 d S m
  have hJoin (m : ℕ) : a m⊔b m=d m := actualCoordinateFace_join_r308 d S m
  have hAc : q≤bitsBelowValue a c := bitsBelowValue_trans_r324
    (bitsBelowValue_of_pointwise_r272 (actualCoordinateFace_le_r308 d S false)) hD
  let H (x y : ℕ → B) := bitsMeet (F.toName a) (G (namedSplitMerge a b z x y))
  let R (x : ℕ → B) := F.toName (bitsMeet a x)
  have hH : NamedTwoArgContinuous q H :=
    ⟨fun y => NamedContinuousOn.meet_fixed_r297
        ((hG.restrict_r314 hqp).comp_prefix_r305 (namedSplitMerge_first_prefix_r322 a b z y)) (F.toName a),
      fun x => NamedContinuousOn.meet_fixed_r297
        ((hG.restrict_r314 hqp).comp_prefix_r305 (namedSplitMerge_second_prefix_r322 a b z x)) (F.toName a)⟩
  have hBad : ∃ x : ℕ → B, ¬ q≤robustGoodTails (goodTailCodesAt H R (32*k) x) := by
    by_contra hn
    have hGood (x : ℕ → B) : q≤robustGoodTails (goodTailCodesAt H R (4*(8*k)) x) := by
      rw [show 4*(8*k)=32*k by omega]
      by_contra hx
      exact hn ⟨x,hx⟩
    obtain ⟨f,⟨hReg⟩,hApprox⟩ := robustGoodTails_has_regularApprox_r320 hH R (8*k) hGood
    have hU : q≤existsNamedUniformValue F.toName a k :=
      actualRegularUniform_to_continuous_r321 (F.restrictCoherent_r321 hqp) a k hk f hReg hApprox
    have hV : q≤existsLargeUniformCapValue F.toName c k :=
      le_iSup_of_le a (le_inf hAc (le_inf (hS false) hU))
    exact hq (le_bot_iff.mp ((le_inf hV hNo).trans_eq inf_compl_eq_bot'))
  obtain ⟨x,hx⟩ := hBad
  let C := goodTailCodesAt H R (32*k) x
  let t := q⊓(robustGoodTails C)ᶜ
  have ht : t≠⊥ := by
    intro he
    exact hx ((le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr he.le)).trans_eq (compl_compl _))
  obtain ⟨r,u,hr,hrt,hBad⟩ := not_robustGoodTails_has_bad_cylinder_r304 C ht
    (show t≤(robustGoodTails C)ᶜ from inf_le_right)
  have hrq : r≤q := hrt.trans inf_le_left
  obtain ⟨P,hLarge,hSection⟩ := exists_actual_section_preserving_large_r307 b u C false
    (hrq.trans (hS true)) hBad
  let e := bitsMeet b (sectionFreeBits P false)
  let w := refinedFaceFixed a b z x P false
  refine ⟨r,e,w,hr,hrq,le_inf ?_ (le_inf hLarge ?_)⟩
  · unfold faceRefinementValue
    apply le_inf (bitsBelowValue_of_pointwise_r272 (fun m => inf_le_left.trans
      (actualCoordinateFace_le_r308 d S true m)))
    apply le_iInf
    intro m
    have hw : (d m)ᶜ⊓w m=(d m)ᶜ⊓z m := by
      have he := congrFun (refinedFaceFixed_eq_merge_zero_r322 a b z x P false) m
      calc
        (d m)ᶜ⊓w m=(d m)ᶜ⊓namedSplitMerge a b z x (actualSectionPoint P false (fun _ => ⊥)) m :=
          congrArg (fun v : B => (d m)ᶜ⊓v) he
        _=(d m)ᶜ⊓z m := by simpa only [hJoin m] using
          namedSplitMerge_outside_mask_r322 a b z x (actualSectionPoint P false (fun _ => ⊥)) m
    exact (le_bitEq_iff_r126 _ _ _).mpr (congrArg (fun v : B => r⊓v) hw.symm)
  · unfold namedFaceBadValue
    apply le_iInf
    intro y
    let v := actualSectionPoint P false y
    have hBadR : r≤(eventuallySmallError true (32*k) (H x v) (R x))ᶜ :=
      namedBadTails_from_allOpen_r324 (hH.2 x) hrq (R x) (32*k) v (hSection y).2
    have hf := namedBadMasked_forces_originalFailure_r324 F hF (hrq.trans hqp) G c a b z x v k hk
      (hrq.trans hAc) hAB hBadR
    have he := namedSplitMerge_section_eq_face_r322 a b z x P y false hAB
    simpa only [v,he,e,w] using hf

end SetLanguage
end JSP000933
