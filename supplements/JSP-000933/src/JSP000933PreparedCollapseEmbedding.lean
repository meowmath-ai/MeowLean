import JSP000933PreparedProduct
import JSP000933BooleanDecisions

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

theorem productImage_le_of_dense_r403 (p : PreparedCondition) (b : PreparedBA)
    (h : ∀ r≤p,∃ s≤r,imageCondition s≤b) : imageCondition p≤b := by
  classical
  by_contra hn
  have hd : imageCondition p⊓bᶜ≠⊥ := by
    intro he
    exact hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨r,hr,hR⟩ := exists_stronger_below_of_meet_r51 p bᶜ hd
  obtain ⟨s,hs,hS⟩ := h r hr
  exact imageCondition_ne_bot_r50 s (disjoint_compl_right.out _
    hS ((imageCondition_mono_r50 hs).trans hR))

noncomputable def embedCollapse (b : CHBase) : PreparedBA :=
  ⨆ p : {p : CollapseBasicCondition // basicValue p≤b},
    imageCondition ((p.val,emptySmallDiamond) : PreparedCondition)

theorem productImage_le_embedCollapse_r403 (p : PreparedCondition) (b : CHBase)
    (h : basicValue p.1≤b) : imageCondition p≤embedCollapse b :=
  (imageCondition_mono_r50 (show p≤(p.1,emptySmallDiamond) from
    ⟨le_rfl,smallDiamond_le_empty_r399 p.2⟩)).trans (le_iSup (fun q : {q : CollapseBasicCondition // basicValue q ≤ b} =>
      imageCondition ((q.val,emptySmallDiamond) : PreparedCondition)) ⟨p.1,h⟩)

theorem embedCollapse_disjoint_r403 {a b : CHBase} (h : Disjoint a b) :
    Disjoint (embedCollapse a) (embedCollapse b) := by
  apply disjoint_iff_inf_le.mpr
  simp only [embedCollapse,iSup_inf_iSup]
  refine iSup_le fun ⟨p,q⟩ => disjoint_iff_inf_le.mp ?_
  by_contra hn
  obtain ⟨s,hs,hq⟩ := (compatible_iff_not_disjoint_r50
    ((p.val,emptySmallDiamond) : PreparedCondition) (q.val,emptySmallDiamond)).mpr hn
  have hsp : basicValue s.1 ≤ basicValue p.val := hs.1
  have hsq : basicValue s.1 ≤ basicValue q.val := hq.1
  exact basicValue_ne_bot_r401 s.1 (h.out _ (hsp.trans p.property) (hsq.trans q.property))

theorem embedCollapse_image_iff_r403 (p : PreparedCondition) (b : CHBase) :
    imageCondition p≤embedCollapse b ↔ basicValue p.1≤b := by
  constructor
  · intro h
    by_contra hn
    have hNB : basicValue p.1⊓bᶜ≠⊥ := by
      intro he
      exact hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    obtain ⟨r,hr⟩ := basicValue_dense_r401 _ hNB
    let s : PreparedCondition := (r,p.2)
    have hs : s≤p := ⟨hr.trans inf_le_left,le_rfl⟩
    exact imageCondition_ne_bot_r50 s ((embedCollapse_disjoint_r403
      (disjoint_compl_right : Disjoint b bᶜ)).out _
      ((imageCondition_mono_r50 hs).trans h)
      (productImage_le_embedCollapse_r403 s _ (hr.trans inf_le_right)))
  · exact productImage_le_embedCollapse_r403 p b

theorem embedCollapse_mono_r403 : Monotone embedCollapse := by
  intro a b hab
  apply iSup_le
  intro p
  exact le_iSup (fun q : {q : CollapseBasicCondition // basicValue q ≤ b} =>
    imageCondition ((q.val,emptySmallDiamond) : PreparedCondition)) ⟨p.val,p.property.trans hab⟩

theorem embedCollapse_joins_r403 {I : Type*} (a : I→CHBase) :
    embedCollapse (⨆ i,a i)=⨆ i,embedCollapse (a i) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    let cell : PreparedCondition := (p.val,emptySmallDiamond)
    apply productImage_le_of_dense_r403 cell
    intro r hr
    have hrMask : basicValue r.1 ≤ basicValue p.val := hr.1
    have h : basicValue r.1≤⨆ i,a i := hrMask.trans p.property
    have hOne : ∃ i,basicValue r.1⊓a i≠⊥ := by
      by_contra hn
      have hEach (i : I) : basicValue r.1⊓a i=⊥ := by
        by_contra hi
        exact hn ⟨i,hi⟩
      apply basicValue_ne_bot_r401 r.1
      calc
        basicValue r.1 = basicValue r.1⊓(⨆ i,a i) := (inf_eq_left.mpr h).symm
        _ = ⨆ i,basicValue r.1⊓a i := inf_iSup_eq _ _
        _ = ⊥ := by simp only [hEach,iSup_bot]
    obtain ⟨i,hi⟩ := hOne
    obtain ⟨s,hs⟩ := basicValue_dense_r401 _ hi
    exact ⟨(s,r.2),⟨hs.trans inf_le_left,le_rfl⟩,
      le_iSup_of_le i (productImage_le_embedCollapse_r403 _ _ (hs.trans inf_le_right))⟩
  · exact iSup_le (fun i => embedCollapse_mono_r403 (le_iSup a i))

theorem embedCollapse_top_r403 : embedCollapse ⊤=⊤ := by
  apply top_unique
  by_contra hn
  have hb : (embedCollapse ⊤)ᶜ≠⊥ := fun h => hn (compl_eq_bot.mp h).ge
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hb
  exact imageCondition_ne_bot_r50 p (disjoint_compl_right.out _
    (productImage_le_embedCollapse_r403 p ⊤ le_top) hp)

theorem embedCollapse_compl_r403 (a : CHBase) : embedCollapse aᶜ=(embedCollapse a)ᶜ := by
  symm
  apply IsCompl.compl_eq
  refine ⟨embedCollapse_disjoint_r403 disjoint_compl_right,?_⟩
  apply codisjoint_iff_le_sup.mpr
  classical
  let f (i : Bool) : CHBase := if i then aᶜ else a
  have hf : (⨆ i,f i)=⊤ := by
    apply top_unique
    have ha : a≤⨆ i,f i := le_iSup_of_le false (by simp [f])
    have hb : aᶜ≤⨆ i,f i := le_iSup_of_le true (by simp [f])
    exact (sup_compl_eq_top (x := a)).symm.trans_le (sup_le ha hb)
  calc
    (⊤ : PreparedBA) = embedCollapse (⊤ : CHBase) := embedCollapse_top_r403.symm
    _ = embedCollapse (⨆ i,f i) := congrArg embedCollapse hf.symm
    _ = ⨆ i,embedCollapse (f i) := embedCollapse_joins_r403 f
    _ ≤ _ := by
      apply iSup_le
      intro i
      cases i
      · simpa [f] using (le_sup_left : embedCollapse a≤embedCollapse a⊔embedCollapse aᶜ)
      · simpa [f] using (le_sup_right : embedCollapse aᶜ≤embedCollapse a⊔embedCollapse aᶜ)

end PreparedModel
end JSP000933
