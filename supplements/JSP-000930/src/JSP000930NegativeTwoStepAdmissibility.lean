import JSP000933RelativeTraceEnumeration
import JSP000933DenseForcingMap

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.ForcingTransport

variable {B N M : Type} [CompleteBooleanAlgebra B]

noncomputable def augmentedAdmissible (Q : ValuedPoset B N)
    (n : N) (X : TotalBA Q) : B :=
  (supportProjection Q (traceValue Q n ⊓ Xᶜ))ᶜ

theorem le_augmentedAdmissible_iff (Q : ValuedPoset B N)
    (n : N) (X : TotalBA Q) (b : B) :
    b ≤ augmentedAdmissible Q n X ↔ traceRectangle Q n b ≤ X := by
  unfold augmentedAdmissible
  rw [le_compl_iff_disjoint_right,disjoint_iff_inf_le,inf_comm b,
    le_bot_iff,← supportProjection_meet_base_r428,
    supportProjection_zero_iff_r428]
  have h : (traceValue Q n ⊓ Xᶜ) ⊓ baseEmbed Q b = traceRectangle Q n b ⊓ Xᶜ := by
    unfold traceRectangle
    ac_rfl
  rw [h,← le_bot_iff,← disjoint_iff_inf_le,disjoint_compl_right_iff]

theorem augmentedAdmissible_top (Q : ValuedPoset B N) (n : N) :
    augmentedAdmissible Q n ⊤ = ⊤ :=
  top_unique ((le_augmentedAdmissible_iff Q n ⊤ ⊤).mpr le_top)

theorem augmented_rectangle_image (Q : ValuedPoset B N)
    (n : N) {b : B} (hb : b ≠ ⊥) (hV : b ≤ Q.valid n) :
    traceRectangle Q n b = imageCondition (⟨b,n,hb,hV⟩ : TotalCondition Q) :=
  (image_eq_base_meet_trace_r429 (⟨b,n,hb,hV⟩ : TotalCondition Q)).symm

theorem augmented_rectangle_mono_first (Q : ValuedPoset B N)
    {n n' : N} {b : B} (h : b ≤ Q.refines n n') :
    traceRectangle Q n b ≤ traceRectangle Q n' b := by
  by_cases hb : b = ⊥
  · simp only [hb,traceRectangle_zero_r464,le_rfl]
  have hV := h.trans (Q.refine_valid n n')
  rw [augmented_rectangle_image Q n hb (hV.trans inf_le_left),
    augmented_rectangle_image Q n' hb (hV.trans inf_le_right)]
  exact imageCondition_mono_r50 ⟨le_rfl,h⟩

noncomputable def augmentedValid (Q : ValuedPoset B N)
    (S : ValuedPoset (TotalBA Q) M) (p : N × M) : B :=
  Q.valid p.1 ⊓ augmentedAdmissible Q p.1 (S.valid p.2)

noncomputable def augmentedQ (Q : ValuedPoset B N) (S : ValuedPoset (TotalBA Q) M) :
    ValuedPoset B (N × M) where
  valid := augmentedValid Q S
  refines p q := (augmentedValid Q S p ⊓ augmentedValid Q S q) ⊓
    (Q.refines p.1 q.1 ⊓ augmentedAdmissible Q p.1 (S.refines p.2 q.2))
  refine_valid _ _ := inf_le_left
  refl p := by
    refine le_inf (le_inf le_rfl le_rfl) (le_inf (inf_le_left.trans (Q.refl _)) ?_)
    apply (le_augmentedAdmissible_iff _ _ _ _).mpr
    exact ((le_augmentedAdmissible_iff Q p.1 (S.valid p.2) _).mp inf_le_right).trans (S.refl _)
  trans p q r := by
    let v (p q : N × M) := (augmentedValid Q S p ⊓ augmentedValid Q S q) ⊓
      (Q.refines p.1 q.1 ⊓ augmentedAdmissible Q p.1 (S.refines p.2 q.2))
    let b := v p q ⊓ v q r
    change b ≤ v p r
    have hPQ : b ≤ Q.refines p.1 q.1 := inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hQR : b ≤ Q.refines q.1 r.1 := inf_le_right.trans (inf_le_right.trans inf_le_left)
    have hp : traceRectangle Q p.1 b ≤ S.refines p.2 q.2 :=
      (le_augmentedAdmissible_iff _ _ _ _).mp
        (inf_le_left.trans (inf_le_right.trans inf_le_right))
    have hq : traceRectangle Q q.1 b ≤ S.refines q.2 r.2 :=
      (le_augmentedAdmissible_iff _ _ _ _).mp
        (inf_le_right.trans (inf_le_right.trans inf_le_right))
    refine le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
      (inf_le_right.trans (inf_le_left.trans inf_le_right)))
      (le_inf ((le_inf hPQ hQR).trans (Q.trans _ _ _)) ?_)
    apply (le_augmentedAdmissible_iff _ _ _ _).mpr
    exact (le_inf hp ((augmented_rectangle_mono_first Q hPQ).trans hq)).trans (S.trans _ _ _)
  weakest := (Q.weakest,S.weakest)
  weakest_valid := by
    change Q.valid Q.weakest ⊓ augmentedAdmissible Q Q.weakest (S.valid S.weakest) = ⊤
    simp only [Q.weakest_valid,S.weakest_valid,augmentedAdmissible_top,inf_top_eq]
  weaker p := by
    have hW : augmentedValid Q S (Q.weakest,S.weakest) = ⊤ := by
      simp only [augmentedValid,Q.weakest_valid,S.weakest_valid,augmentedAdmissible_top,inf_top_eq]
    refine le_inf (le_inf le_rfl (le_top.trans hW.ge)) (le_inf (inf_le_left.trans (Q.weaker _)) ?_)
    apply (le_augmentedAdmissible_iff _ _ _ _).mpr
    exact ((le_augmentedAdmissible_iff Q p.1 (S.valid p.2) _).mp inf_le_right).trans (S.weaker _)

end JSP000930.Negative
