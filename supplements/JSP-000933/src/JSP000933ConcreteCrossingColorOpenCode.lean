import JSP000933FiniteCrossingRankTests

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def paddedWordBits (w : Word) (m : ℕ) : B := truthBit (wordBit w m)

theorem cylinder_fixes_paddedBits_r258 {p : B} {x : ℕ → B} {w : Word}
    (h : p≤cylinderValue x w) (m : ℕ) (hm : m<w.length) :
    p⊓x m=p⊓paddedWordBits w m := by
  apply (le_bitEq_iff_r126 _ _ _).mp
  simp only [paddedWordBits,wordBit,dite_eq_left hm,bitEq_truthBit_r175]
  exact h.trans (iInf_le _ (⟨m,hm⟩ : Fin w.length))

noncomputable def concreteCrossColorTable (e : ℕ ↪ Word) (k : ℕ) : Word × Word → B :=
  fun uv => ⨆ r : {r : CrossingRank //
      4*crossingRankWidth e r≤uv.1.length ∧ 4*crossingRankWidth e r≤uv.2.length},
    finiteCrossRankTest e k r.1 (paddedWordBits uv.1) (paddedWordBits uv.2)

noncomputable def concreteCrossTestValue (e : ℕ ↪ Word) (k : ℕ) (x y : ℕ → B) : B :=
  ⨆ r : CrossingRank, finiteCrossRankTest e k r x y

theorem concreteCrossColorTable_value_r258 (e : ℕ ↪ Word) (k : ℕ) (x y : ℕ → B) :
    colorValue (concreteCrossColorTable e k) x y = concreteCrossTestValue e k x y := by
  apply le_antisymm
  · apply le_of_dense_named_refinements_r219
    intro p hp hP
    obtain ⟨uv,q,hq,hqp,hUV⟩ := exists_nonzero_below_choice_r135 p hp
      (fun uv : Word × Word => concreteCrossColorTable e k uv ⊓
        (cylinderValue x uv.1 ⊓ cylinderValue y uv.2)) hP
    obtain ⟨r,t,ht,htq,hT⟩ := exists_nonzero_below_choice_r135 q hq
      (fun r : {r : CrossingRank // 4*crossingRankWidth e r≤uv.1.length ∧
        4*crossingRankWidth e r≤uv.2.length} =>
          finiteCrossRankTest e k r.1 (paddedWordBits uv.1) (paddedWordBits uv.2)) (hUV.trans inf_le_left)
    have hX := htq.trans (hUV.trans (inf_le_right.trans inf_le_left))
    have hY := htq.trans (hUV.trans (inf_le_right.trans inf_le_right))
    have hEq := finiteCrossRankTest_mask_r257 e k r.1
      (fun m hm => cylinder_fixes_paddedBits_r258 hX m (hm.trans_le r.2.1))
      (fun m hm => cylinder_fixes_paddedBits_r258 hY m (hm.trans_le r.2.2))
    exact ⟨t,ht,htq.trans hqp,le_iSup_of_le r.1
      (((le_inf le_rfl hT).trans_eq hEq.symm).trans inf_le_right)⟩
  · apply le_of_dense_named_refinements_r219
    intro p hp hP
    obtain ⟨r,q,hq,hqp,hQ⟩ := exists_nonzero_below_choice_r135 p hp
      (fun r => finiteCrossRankTest e k r x y) hP
    let N := 4*crossingRankWidth e r
    obtain ⟨u,hu,s,hs,hsq,hS⟩ := exists_decided_initialWord_r136 x N q hq
    obtain ⟨v,hv,t,ht,hts,hT⟩ := exists_decided_initialWord_r136 y N s hs
    have hX := hts.trans hS
    have hEq := finiteCrossRankTest_mask_r257 e k r
      (fun m hm => cylinder_fixes_paddedBits_r258 hX m (hu.symm ▸ hm))
      (fun m hm => cylinder_fixes_paddedBits_r258 hT m (hv.symm ▸ hm))
    have hTest : t≤finiteCrossRankTest e k r (paddedWordBits u) (paddedWordBits v) :=
      ((le_inf le_rfl (hts.trans (hsq.trans hQ))).trans_eq hEq).trans inf_le_right
    have hC : t≤concreteCrossColorTable e k (u,v) :=
      le_iSup_of_le ⟨r,hu.ge,hv.ge⟩ hTest
    exact ⟨t,ht,hts.trans (hsq.trans hqp),edgeBox_suffices_r136 _ x y (u,v) hC hX hT⟩

end SetLanguage
end JSP000933
