import JSP000933PreparedShortProfiles

open Cardinal

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

noncomputable def positiveCut (s : SmallDiamondCondition) (a : PreparedBA) : Set CollapseBasicCondition :=
  {p | imageCondition ((p,s) : PreparedCondition)≤a}

noncomputable def decodeCut (S : Set CollapseBasicCondition) : CHBase :=
  ⨆ p : S,basicValue p.val

noncomputable def booleanAgree (a b : PreparedBA) : PreparedBA := (a⇨b)⊓(b⇨a)

theorem prepared_positiveCut_agrees_of_decided_r405 (p : CollapseBasicCondition)
    (s t : SmallDiamondCondition) (hts : t ≤ s) (a : PreparedBA)
    (h : Decides ((p,s) : PreparedCondition) a) :
    imageCondition ((p,t) : PreparedCondition)≤
      booleanAgree a (embedCollapse (decodeCut (positiveCut s a))) := by
  rcases h with hp | hn
  · have hP : p∈positiveCut s a := hp
    have h1 := (imageCondition_mono_r50
      (show ((p,t) : PreparedCondition)≤(p,s) from ⟨le_rfl,hts⟩)).trans hp
    have h2 := productImage_le_embedCollapse_r403 ((p,t) : PreparedCondition)
      (decodeCut (positiveCut s a)) (le_iSup (fun r : positiveCut s a => basicValue r.val) ⟨p,hP⟩)
    simp only [booleanAgree,himp_eq]
    exact le_inf (h2.trans le_sup_left) (h1.trans le_sup_left)
  · have hNe (r : positiveCut s a) : Disjoint (basicValue p) (basicValue r.val) := by
      by_contra hN
      obtain ⟨u,hup,hur⟩ := basicValue_pair_compatible_r401 p r.val hN
      have he1 : imageCondition ((u,s) : PreparedCondition)≤a :=
        (imageCondition_mono_r50 (show ((u,s) : PreparedCondition)≤(r.val,s) from
          ⟨hur,le_rfl⟩)).trans r.property
      have he2 : imageCondition ((u,s) : PreparedCondition)≤aᶜ :=
        (imageCondition_mono_r50 (show ((u,s) : PreparedCondition)≤(p,s) from
          ⟨hup,le_rfl⟩)).trans hn
      exact imageCondition_ne_bot_r50 ((u,s) : PreparedCondition)
        (disjoint_compl_right.out _ he1 he2)
    have hd : Disjoint (basicValue p) (decodeCut (positiveCut s a)) := by
      apply disjoint_iff_inf_le.mpr
      rw [decodeCut,inf_iSup_eq]
      exact iSup_le (fun r => (disjoint_iff_inf_le.mp (hNe r)))
    have h1 := (imageCondition_mono_r50
      (show ((p,t) : PreparedCondition)≤(p,s) from ⟨le_rfl,hts⟩)).trans hn
    have h2 : imageCondition ((p,t) : PreparedCondition)≤
        (embedCollapse (decodeCut (positiveCut s a)))ᶜ := by
      rw [← embedCollapse_compl_r403]
      exact productImage_le_embedCollapse_r403 ((p,t) : PreparedCondition) _
        (le_compl_iff_disjoint_right.mpr hd)
    simp only [booleanAgree,himp_eq]
    exact le_inf (h1.trans le_sup_right) (h2.trans le_sup_right)

theorem prepared_shortProfiles_decoded_r405 {I : Type} (hI : Cardinal.mk I<GroundContinuumSucc)
    (A : I→PreparedBA) (p : CollapseBasicCondition) (q : SmallDiamondCondition) :
    ∃ s≤q,∀ t ≤ s,∀ i,imageCondition ((p,t) : PreparedCondition)≤
      booleanAgree (A i) (embedCollapse (decodeCut (positiveCut t (A i)))) := by
  classical
  let Index := I×{r : CollapseBasicCondition // r≤p}
  let Q (i : Index) (t : SmallDiamondCondition) := ∃ r≤ i.2.val,
    Decides ((r,t) : PreparedCondition) (A i.1)
  have hDown (i : Index) {t u : SmallDiamondCondition} (htu : u≤t) (h : Q i t) : Q i u := by
    obtain ⟨r,hr,hD⟩ := h
    exact ⟨r,hr,hD.of_stronger_r51 ⟨le_rfl,htu⟩⟩
  have hDense (i : Index) (t : SmallDiamondCondition) (_ : t≤q) : ∃ u≤t,Q i u := by
    obtain ⟨new,hNew,h⟩ := exists_stronger_decides_r51
      ((i.2.val,t) : PreparedCondition) (A i.1)
    exact ⟨new.2,hNew.2,new.1,hNew.1,h⟩
  obtain ⟨s,hs,hS⟩ := smallDiamond_simultaneous_wellOrder_r402
    (smallBaseProducts_r404 hI p) Q hDown q hDense
  refine ⟨s,hs,fun t ht i => ?_⟩
  apply productImage_le_of_dense_r403
  intro u hu
  obtain ⟨r,hr,hR⟩ := hS (i,⟨u.1,hu.1⟩)
  have hT : Decides ((r,t) : PreparedCondition) (A i) :=
    hR.of_stronger_r51 ⟨le_rfl,ht⟩
  exact ⟨(r,u.2),⟨hr,le_rfl⟩,prepared_positiveCut_agrees_of_decided_r405 r t u.2 hu.2 (A i) hT⟩

end PreparedModel
end JSP000933
