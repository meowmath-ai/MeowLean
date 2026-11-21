import JSP000930MixedRankAvoidance

namespace JSP000930
namespace MixedPalettes

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

structure RankSystem (I B : Type) [LinearOrder I] [CompleteBooleanAlgebra B] where
  strict : ∀ a : I, {b : I // b < a} → Label B
  strict_separates : ∀ a, SeparatesRanks (strict a)
  weak : ∀ a : I, {b : I // b ≤ a} → Label B
  weak_separates : ∀ a, SeparatesRanks (weak a)

section

variable {I : Type} [LinearOrder I] [WellFoundedLT I]

private noncomputable def rowStep (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) (a : I) (prev : ∀ b : I, b < a → I → Label B) :
    I → Label B := by
  classical
  exact fun x =>
    if hx : x < a then
      Classical.choose (choose_label_avoiding_mixed_rank_cut hB (R.strict a)
        (fun b => prev b.1 b.2 x) (R.strict_separates a) (R.strict a ⟨x,hx⟩))
    else R.weak x ⟨a, le_of_not_gt hx⟩

noncomputable def rows (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) : I → I → Label B :=
  wellFounded_lt.fix (C := fun (_ : I) => I → Label B) (rowStep hB R)

private theorem rows_eq (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) (a : I) :
    rows hB R a = rowStep hB R a (fun b _ => rows hB R b) := by
  unfold rows
  exact WellFounded.fix_eq _ _ _

theorem rows_tail (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) {a x : I} (hax : a ≤ x) :
    rows hB R a x = R.weak x ⟨a,hax⟩ := by
  have he := congrFun (rows_eq hB R a) x
  simpa only [rowStep, dite_eq_right (not_lt_of_ge hax)] using he

theorem rows_tail_disjoint (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) {a b x : I} (hab : b < a) (hax : a ≤ x)
    (y : OmegaOneIndex) :
    Disjoint ((rows hB R a x).value y) ((rows hB R b x).value y) := by
  rw [rows_tail hB R hax, rows_tail hB R (hab.le.trans hax)]
  exact R.weak_separates x _ _ (fun he => (ne_of_gt hab) (congrArg Subtype.val he)) y

theorem rows_avoid_prior_rank (hB : BoundsCountableOmegaOneNames B)
    (R : RankSystem I B) {a b x : I} (hab : b < a) (hxa : x < a)
    {t c : OmegaOneIndex} (ht : t ≤ c) (y : OmegaOneIndex) :
    Disjoint ((rows hB R a x).value y)
      ((R.strict a ⟨x,hxa⟩).value c ⊓ (R.strict a ⟨b,hab⟩).value t ⊓
        (rows hB R b x).value y) := by
  let E := choose_label_avoiding_mixed_rank_cut hB (R.strict a)
    (fun b => rows hB R b.1 x) (R.strict_separates a) (R.strict a ⟨x,hxa⟩)
  have he : rows hB R a x = Classical.choose E := by
    have h := congrFun (rows_eq hB R a) x
    simpa only [rowStep, dite_eq_left hxa, E] using h
  rw [he]
  exact Classical.choose_spec E ⟨b,hab⟩ ht y

end

end MixedPalettes
end JSP000930
