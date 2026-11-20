import JSP000933ActualBadChildRefinement

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem faceRefinement_child_mask_r326 (a z : ℕ → B) {q : B} {b b' w w' : ℕ → B}
    (hb : q≤realEqValue b b') (hw : q≤realEqValue w w') :
    q⊓faceRefinementValue a z b w=q⊓faceRefinementValue a z b' w' := by
  unfold faceRefinementValue
  apply mask_inf_congr_r126 (bitsBelowValue_mask_r256 hb (le_top.trans_eq (realEqValue_refl_r127 a).symm))
  apply mask_iInf_congr_r126
  intro m
  exact mask_bitEq_congr_r257 rfl (mask_inf_congr_r126 rfl ((le_realEqValue_iff_r126 _ _ _).mp hw m))

theorem badChildFace_mask_r326 {p q : B} {G F : (ℕ → B) → ℕ → B}
    (hG : NamedContinuousOn p G) (hF : NameMapExt F) (hqp : q≤p)
    (c a z : ℕ → B) (k : ℕ) {b b' w w' : ℕ → B}
    (hb : q≤realEqValue b b') (hw : q≤realEqValue w w') :
    q⊓badChildFaceValue G F c k a z b w=q⊓badChildFaceValue G F c k a z b' w' := by
  unfold badChildFaceValue namedFaceBadValue
  apply mask_inf_congr_r126 (faceRefinement_child_mask_r326 a z hb hw)
  apply mask_inf_congr_r126 (actualLongBlockLarge_ext_r314 q b b' hb)
  apply mask_iInf_congr_r126
  intro y
  have hm := namedFacePoint_mask_r323 hb hw (le_top.trans_eq (realEqValue_refl_r127 y).symm)
  have hP := realEqValue_bitsMeet_mask_r251 (le_top.trans_eq (realEqValue_refl_r127 c).symm) hm
  exact mask_compl_congr_r126 (eventuallySmallError_mask_r313 true k
    (hG.realEq_mask_r323 hqp hm) (hF q _ _ hP))

theorem noUniform_has_actualBadChild_r326 {p q : B}
    (F : CoherentSelectedIso B p) (hF : NameMapExt F.toName)
    (G : (ℕ → B) → ℕ → B) (hG : NamedContinuousOn p G)
    (c d z : ℕ → B) (k : ℕ) (hk : k≠0) (hqp : q≤p)
    (hNo : q≤(existsLargeUniformCapValue F.toName c k)ᶜ)
    (hD : q≤bitsBelowValue d c) (hL : q≤actualLongBlockLarge d) :
    ∃ a w : ℕ → B, q≤badChildFaceValue G F.toName c (64*k) d z a w := by
  let W (t : ℕ → B) := q⊓badChildFaceValue G F.toName c (64*k) d z (crossCap t) (crossPay t)
  have hExt : RealTestExt W := by
    intro r x y h
    let s := r⊓q
    have hX : s≤realEqValue x y := inf_le_left.trans h
    have hM := badChildFace_mask_r326 hG hF (show s≤p from inf_le_right.trans hqp) c d z (64*k)
      (extract4_mask_r240 hX 0) (extract4_mask_r240 hX 1)
    simp only [s,inf_assoc] at hM
    exact hM
  have hW : q≤⨆ t : ℕ → B, W t := by
    apply le_of_dense_named_refinements_r219
    intro r hr hrq
    obtain ⟨s,a,w,hs,hsr,hBad⟩ := noUniform_has_actualBadChild_refinement_r325 F hF G hG c d z k hk hr
      (hrq.trans hqp) (hrq.trans hNo) (hrq.trans hD) (hrq.trans hL)
    let t := interleaveCrossQuad a w (fun _ => ⊥) (fun _ => ⊥)
    have ht : s≤W t := by
      simpa only [W,t,crossCap_interleaveCrossQuad_r271,crossPay_interleaveCrossQuad_r271] using
        (le_inf (hsr.trans hrq) hBad)
    exact ⟨s,hs,hsr,le_iSup_of_le t ht⟩
  obtain ⟨t,ht⟩ := exists_realName_maximum_r138 W hExt q hW
  exact ⟨crossCap t,crossPay t,ht.trans inf_le_right⟩

end SetLanguage
end JSP000933
