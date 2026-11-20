import JSP000933MarkedTotalForcing
import JSP000933BooleanDecisions

namespace JSP000933
namespace MarkedForcing

open BooleanCompletion

variable {B N : Type} [CompleteBooleanAlgebra B]

abbrev TotalBA (Q : ValuedPoset B N) := RO (TotalCondition Q)

theorem totalImage_le_of_dense_r427 {Q : ValuedPoset B N} (p : TotalCondition Q)
    (x : TotalBA Q)
    (h : ∀ r≤p,∃ s≤r,imageCondition s≤x) :
    imageCondition p≤x := by
  classical
  by_contra hn
  have hNZ : imageCondition p⊓xᶜ≠⊥ := fun he =>
    hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨r,hr,hR⟩ := exists_stronger_below_of_meet_r51 p xᶜ hNZ
  obtain ⟨s,hs,hS⟩ := h r hr
  exact imageCondition_ne_bot_r50 s (disjoint_compl_right.out _ hS
    ((imageCondition_mono_r50 hs).trans hR))

noncomputable def baseEmbed (Q : ValuedPoset B N) (b : B) : TotalBA Q :=
  ⨆ p : {p : TotalCondition Q // p.mask≤b},imageCondition p.val

theorem image_le_baseEmbed_r427 {Q : ValuedPoset B N} (p : TotalCondition Q) (b : B)
    (h : p.mask≤b) : imageCondition p≤baseEmbed Q b := le_iSup (fun s : {r : TotalCondition Q // r.mask ≤ b} => imageCondition s.val) ⟨p,h⟩

theorem baseEmbed_disjoint_r427 (Q : ValuedPoset B N) {a b : B} (h : Disjoint a b) :
    Disjoint (baseEmbed Q a) (baseEmbed Q b) := by
  apply disjoint_iff_inf_le.mpr
  simp only [baseEmbed,iSup_inf_iSup]
  refine iSup_le fun ⟨p,q⟩ => disjoint_iff_inf_le.mp ?_
  by_contra hn
  obtain ⟨r,hrp,hrq⟩ := (compatible_iff_not_disjoint_r50 p.val q.val).mpr hn
  exact r.nonzero (h.out _ (hrp.1.trans p.property) (hrq.1.trans q.property))

theorem baseEmbed_reflects_mask_r427 {Q : ValuedPoset B N}
    (p : TotalCondition Q) (b : B) :
    imageCondition p≤baseEmbed Q b ↔ p.mask≤b := by
  constructor
  · intro h
    by_contra hn
    have hN : p.mask⊓bᶜ≠⊥ := fun he =>
      hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    let q := intersectMask p bᶜ hN
    have h1 : imageCondition q≤baseEmbed Q b :=
      (imageCondition_mono_r50 (intersectMask_le_r426 p bᶜ hN)).trans h
    have h2 : imageCondition q≤baseEmbed Q bᶜ := image_le_baseEmbed_r427 q bᶜ inf_le_right
    exact imageCondition_ne_bot_r50 q
      ((baseEmbed_disjoint_r427 Q (disjoint_compl_right : Disjoint b bᶜ)).out _ h1 h2)
  · exact image_le_baseEmbed_r427 p b

theorem baseEmbed_mono_r427 (Q : ValuedPoset B N) : Monotone (baseEmbed Q) := by
  intro a b hab
  apply iSup_le
  intro p
  exact image_le_baseEmbed_r427 p.val b (p.property.trans hab)

theorem baseEmbed_joins_r427 (Q : ValuedPoset B N) {I : Type*} (v : I→B) :
    baseEmbed Q (⨆ i,v i)=⨆ i,baseEmbed Q (v i) := by
  apply le_antisymm
  · apply iSup_le
    intro p
    apply totalImage_le_of_dense_r427 p.val
    intro r hr
    have hR : r.mask≤⨆ i,v i := hr.1.trans p.property
    have hSome : ∃ i,r.mask⊓v i≠⊥ := by
      by_contra hn
      have he (i : I) : r.mask⊓v i=⊥ := by
        by_contra h
        exact hn ⟨i,h⟩
      apply r.nonzero
      calc
        r.mask = r.mask⊓(⨆ i,v i) := (inf_eq_left.mpr hR).symm
        _ = ⨆ i,r.mask⊓v i := inf_iSup_eq _ _
        _ = ⊥ := by simp only [he,iSup_bot]
    obtain ⟨i,hi⟩ := hSome
    exact ⟨intersectMask r (v i) hi,intersectMask_le_r426 r (v i) hi,
      le_iSup_of_le i (image_le_baseEmbed_r427 _ (v i) inf_le_right)⟩
  · exact iSup_le (fun i => baseEmbed_mono_r427 Q (le_iSup v i))

theorem baseEmbed_top_r427 (Q : ValuedPoset B N) : baseEmbed Q ⊤=⊤ := by
  apply top_unique
  by_contra hn
  have hNZ : (baseEmbed Q ⊤)ᶜ≠⊥ := fun h => hn (compl_eq_bot.mp h).ge
  obtain ⟨p,hP⟩ := imageCondition_dense_r50 _ hNZ
  exact imageCondition_ne_bot_r50 p
    (disjoint_compl_right.out _ (image_le_baseEmbed_r427 p ⊤ le_top) hP)

theorem baseEmbed_bot_r427 (Q : ValuedPoset B N) : baseEmbed Q ⊥=⊥ := by
  apply le_bot_iff.mp
  apply iSup_le
  intro p
  exact False.elim (p.val.nonzero (le_bot_iff.mp p.property))

theorem baseEmbed_compl_r427 (Q : ValuedPoset B N) (b : B) :
    baseEmbed Q bᶜ=(baseEmbed Q b)ᶜ := by
  symm
  apply IsCompl.compl_eq
  refine ⟨baseEmbed_disjoint_r427 Q disjoint_compl_right,?_⟩
  apply codisjoint_iff_le_sup.mpr
  classical
  let f (i : Bool) : B := if i then bᶜ else b
  have hf : (⨆ i,f i)=⊤ := by
    apply top_unique
    have hb : b≤⨆ i,f i := le_iSup_of_le false (by simp [f])
    have hn : bᶜ≤⨆ i,f i := le_iSup_of_le true (by simp [f])
    exact (sup_compl_eq_top (x := b)).symm.trans_le (sup_le hb hn)
  calc
    (⊤ : TotalBA Q) = baseEmbed Q (⊤ : B) := (baseEmbed_top_r427 Q).symm
    _ = baseEmbed Q (⨆ i,f i) := congrArg (baseEmbed Q) hf.symm
    _ = ⨆ i,baseEmbed Q (f i) := baseEmbed_joins_r427 Q f
    _ ≤ _ := by
      apply iSup_le
      intro i
      cases i
      · simpa [f] using (le_sup_left : baseEmbed Q b≤baseEmbed Q b⊔baseEmbed Q bᶜ)
      · simpa [f] using (le_sup_right : baseEmbed Q bᶜ≤baseEmbed Q b⊔baseEmbed Q bᶜ)

end MarkedForcing
end JSP000933
