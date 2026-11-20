import JSP000933ActualNeatCrossingFiniteTest

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure CrossingRank where
  i : ℕ
  j : ℕ
  atPrefix : ℕ

noncomputable def crossingRankWidth (e : ℕ ↪ Word) (r : CrossingRank) : ℕ :=
  max (max (r.i+1) (r.j+1)) (max (commonLabelBound e r.i r.j) r.atPrefix)

noncomputable def finiteCrossRankTest (e : ℕ ↪ Word) (k : ℕ)
    (r : CrossingRank) (x y : ℕ → B) : B :=
  crispTruth B (labelsIncomp (e r.i) (e r.j)) ⊓
    (crossCap x r.i ⊓ (crossCap y r.j ⊓ (finiteSourceCrossValue e r.i r.j x y ⊓
      (nameBudgetValue true (realBitsName (outputCrossError x y)) (realBitsName (fun _ => ⊥))
        k r.atPrefix)ᶜ)))

theorem mask_bitEq_congr_r257 {p a a' b b' : B}
    (ha : p⊓a=p⊓a') (hb : p⊓b=p⊓b') : p⊓bitEq a b=p⊓bitEq a' b' :=
  mask_inf_congr_r126 (mask_sup_congr_r211 (mask_compl_congr_r126 ha) hb)
    (mask_sup_congr_r211 (mask_compl_congr_r126 hb) ha)

theorem mask_xor_congr_r257 {p a a' b b' : B}
    (ha : p⊓a=p⊓a') (hb : p⊓b=p⊓b') :
    p⊓((a⊓bᶜ)⊔(aᶜ⊓b))=p⊓((a'⊓(b')ᶜ)⊔((a')ᶜ⊓b')) :=
  mask_sup_congr_r211 (mask_inf_congr_r126 ha (mask_compl_congr_r126 hb))
    (mask_inf_congr_r126 (mask_compl_congr_r126 ha) hb)

theorem extract4_maskAt_r257 {p : B} {x y : ℕ → B} {N : ℕ}
    (h : ∀ m<4*N, p⊓x m=p⊓y m) (i : Fin 4) (m : ℕ) (hm : m<N) :
    p⊓extract4 x i m=p⊓extract4 y i m := by
  apply h
  have hi := i.isLt
  omega

theorem finiteCrossRankTest_mask_r257 (e : ℕ ↪ Word) (k : ℕ) (r : CrossingRank)
    {p : B} {x x' y y' : ℕ → B}
    (hx : ∀ m<4*crossingRankWidth e r, p⊓x m=p⊓x' m)
    (hy : ∀ m<4*crossingRankWidth e r, p⊓y m=p⊓y' m) :
    p⊓finiteCrossRankTest e k r x y=p⊓finiteCrossRankTest e k r x' y' := by
  have hi : r.i<crossingRankWidth e r :=
    (Nat.lt_succ_self _).trans_le ((le_max_left _ _).trans (le_max_left _ _))
  have hj : r.j<crossingRankWidth e r :=
    (Nat.lt_succ_self _).trans_le ((le_max_right _ _).trans (le_max_left _ _))
  have hLb : commonLabelBound e r.i r.j≤crossingRankWidth e r :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hN : r.atPrefix≤crossingRankWidth e r := (le_max_right _ _).trans (le_max_right _ _)
  have hS : p⊓finiteSourceCrossValue e r.i r.j x y=p⊓finiteSourceCrossValue e r.i r.j x' y' := by
    unfold finiteSourceCrossValue
    apply mask_iInf_congr_r126
    intro m
    have hm := (lt_commonLabelBound_r255 e r.i r.j m.val m.property).trans_le hLb
    exact mask_bitEq_congr_r257
      (mask_inf_congr_r126 (extract4_maskAt_r257 hx 0 m.val hm) (extract4_maskAt_r257 hy 1 m.val hm))
      (mask_inf_congr_r126 (extract4_maskAt_r257 hy 0 m.val hm) (extract4_maskAt_r257 hx 1 m.val hm))
  have hErr (m : ℕ) (hm : m<r.atPrefix) :
      p⊓membershipBits (realBitsName (outputCrossError x y)) m =
      p⊓membershipBits (realBitsName (outputCrossError x' y')) m := by
    rw [membershipBits_realBitsName_r128,membershipBits_realBitsName_r128]
    have hm' := hm.trans_le hN
    exact mask_xor_congr_r257
      (mask_inf_congr_r126 (extract4_maskAt_r257 hx 2 m hm') (extract4_maskAt_r257 hy 3 m hm'))
      (mask_inf_congr_r126 (extract4_maskAt_r257 hy 2 m hm') (extract4_maskAt_r257 hx 3 m hm'))
  have hB := nameBudgetValue_mask_r226 (C := realBitsName (fun _ => ⊥))
    (C' := realBitsName (fun _ => ⊥)) hErr (fun _ _ => rfl) true k
  exact mask_inf_congr_r126 rfl (mask_inf_congr_r126 (extract4_maskAt_r257 hx 0 r.i hi)
    (mask_inf_congr_r126 (extract4_maskAt_r257 hy 0 r.j hj)
      (mask_inf_congr_r126 hS (mask_compl_congr_r126 hB))))

end SetLanguage
end JSP000933
