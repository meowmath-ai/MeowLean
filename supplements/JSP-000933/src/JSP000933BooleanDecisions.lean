import JSP000933BooleanCompletion

namespace JSP000933
namespace BooleanCompletion

variable {P : Type*} [Preorder P]

def Decides (p : P) (a : RO P) : Prop :=
  imageCondition p ≤ a ∨ imageCondition p ≤ aᶜ

theorem Decides.of_stronger_r51 {p q : P} {a : RO P} (h : Decides p a) (hqp : q ≤ p) :
    Decides q a := by
  have hm : imageCondition q ≤ imageCondition p := imageCondition_mono_r50 hqp
  exact h.elim (fun hp => Or.inl (hm.trans hp)) (fun hp => Or.inr (hm.trans hp))

theorem exists_stronger_below_of_meet_r51 (p : P) (a : RO P)
    (h : imageCondition p ⊓ a ≠ ⊥) :
    ∃ q : P, q ≤ p ∧ imageCondition q ≤ a := by
  obtain ⟨r,hr⟩ := imageCondition_dense_r50 (imageCondition p ⊓ a) h
  have hrp : imageCondition r ≤ imageCondition p := hr.trans inf_le_left
  have hra : imageCondition r ≤ a := hr.trans inf_le_right
  have hNon : ¬ Disjoint (imageCondition r) (imageCondition p) := by
    intro hd
    have h1 : imageCondition r ≤ imageCondition r ⊓ imageCondition p :=
      le_inf le_rfl hrp
    exact imageCondition_ne_bot_r50 r
      (le_bot_iff.mp (h1.trans (disjoint_iff_inf_le.mp hd)))
  obtain ⟨q,hqr,hqp⟩ := (compatible_iff_not_disjoint_r50 r p).mpr hNon
  exact ⟨q,hqp,(imageCondition_mono_r50 hqr).trans hra⟩

theorem exists_stronger_decides_r51 (p : P) (a : RO P) : ∃ q : P, q ≤ p ∧ Decides q a := by
  classical
  by_cases h : imageCondition p ⊓ a = ⊥
  · have hd : Disjoint (imageCondition p) a := disjoint_iff_inf_le.mpr h.le
    exact ⟨p,le_rfl,Or.inr (le_compl_iff_disjoint_right.mpr hd)⟩
  · obtain ⟨q,hqp,hq⟩ := exists_stronger_below_of_meet_r51 p a h
    exact ⟨q,hqp,Or.inl hq⟩

theorem exists_stronger_below_indexedSup_r51 {ι : Type*} (p : P) (a : ι → RO P)
    (h : imageCondition p ≤ ⨆ i, a i) :
    ∃ i : ι, ∃ q : P, q ≤ p ∧ imageCondition q ≤ a i := by
  classical
  have hOne : ∃ i, imageCondition p ⊓ a i ≠ ⊥ := by
    by_contra hn
    have hComp (i : ι) : a i ≤ (imageCondition p)ᶜ := by
      by_cases he : imageCondition p ⊓ a i = ⊥
      · exact le_compl_iff_disjoint_left.mpr (disjoint_iff_inf_le.mpr he.le)
      · exact False.elim (hn ⟨i,he⟩)
    have he : imageCondition p ≤ (imageCondition p)ᶜ := h.trans (iSup_le hComp)
    have hd := le_compl_iff_disjoint_left.mp he
    exact imageCondition_ne_bot_r50 p (disjoint_self.mp hd)
  obtain ⟨i,hi⟩ := hOne
  obtain ⟨q,hqp,hq⟩ := exists_stronger_below_of_meet_r51 p (a i) hi
  exact ⟨i,q,hqp,hq⟩

end BooleanCompletion
end JSP000933
