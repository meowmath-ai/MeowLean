import JSP000933ActualRefinedFaceGeometry

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem NamedContinuousOn.realEq_mask_r323 {p q : B} {f : (ℕ → B) → ℕ → B}
    (h : NamedContinuousOn p f) (hq : q≤p) {x y : ℕ → B} (he : q≤realEqValue x y) :
    q≤realEqValue (f x) (f y) := by
  let g := namedTableOutput (actualFunctionBitTable f)
  have hX : p≤realEqValue (g x) (f x) := h.actualBitTable_mask_r311 x
  have hY : p≤realEqValue (g y) (f y) := h.actualBitTable_mask_r311 y
  have hG : q≤realEqValue (g x) (g y) := namedTableOutput_ext_r311 _ q x y he
  have hx : q≤realEqValue (f x) (g x) := (hq.trans hX).trans_eq (realEqValue_symm_r127 _ _)
  exact (le_inf ( (le_inf hx hG).trans (realEqValue_trans_r127 (f x) (g x) (g y))) (hq.trans hY)).trans
    (realEqValue_trans_r127 (f x) (g y) (f y))

theorem realEqValue_trans_le_r323 {p : B} {x y z : ℕ → B}
    (h : p≤realEqValue x y) (j : p≤realEqValue y z) : p≤realEqValue x z :=
  (le_inf h j).trans (realEqValue_trans_r127 x y z)

theorem namedFacePoint_mask_r323 {p : B} {a b z w x y : ℕ → B}
    (ha : p≤realEqValue a b) (hz : p≤realEqValue z w) (hx : p≤realEqValue x y) :
    p≤realEqValue (namedFacePoint a z x) (namedFacePoint b w y) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  have hA := (le_realEqValue_iff_r126 _ _ _).mp ha m
  exact mask_sup_congr_r211 (mask_inf_congr_r126 hA ((le_realEqValue_iff_r126 _ _ _).mp hx m))
    (mask_inf_congr_r126 (mask_compl_congr_r126 hA) ((le_realEqValue_iff_r126 _ _ _).mp hz m))

noncomputable def faceMembershipValue (a z x : ℕ → B) : B :=
  realEqValue (namedFacePoint a z x) x

noncomputable def faceRefinementValue (a z b w : ℕ → B) : B :=
  bitsBelowValue b a⊓(⨅ m : ℕ, bitEq ((a m)ᶜ⊓z m) ((a m)ᶜ⊓w m))

theorem namedSplitMerge_payload_first_mask_r323 (c a b z x y : ℕ → B) {p : B}
    (hA : p≤bitsBelowValue a c) (hD : ∀ m, a m⊓b m=⊥) :
    p≤realEqValue (bitsMeet a (bitsMeet c (namedSplitMerge a b z x y))) (bitsMeet a x) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  let M := namedSplitMerge a b z x y m
  have hC : (p⊓a m)⊓c m=p⊓a m := inf_eq_left.mpr (bitsBelowValue_apply_r256 hA m)
  change p⊓(a m⊓(c m⊓M))=p⊓(a m⊓x m)
  calc
    p⊓(a m⊓(c m⊓M))=((p⊓a m)⊓c m)⊓M := by ac_rfl
    _=(p⊓a m)⊓M := by rw [hC]
    _=p⊓(a m⊓M) := inf_assoc _ _ _
    _=p⊓(a m⊓x m) := congrArg (fun b : B => p⊓b) (namedSplitMerge_first_mask_r322 a b z x y m (hD m))

theorem namedFacePoint_partition_r323 (a z x : ℕ → B) (m : ℕ) :
    (a m⊓namedFacePoint a z x m)⊔((a m)ᶜ⊓namedFacePoint a z x m)=namedFacePoint a z x m := by
  rw [← inf_sup_right,sup_compl_eq_top,top_inf_eq]

end SetLanguage
end JSP000933
