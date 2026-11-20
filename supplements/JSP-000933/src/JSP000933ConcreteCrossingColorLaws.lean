import JSP000933ConcreteCrossingColorOpenCode

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem outputCrossError_comm_r259 (x y : ℕ → B) :
    outputCrossError x y = outputCrossError y x := by
  funext m
  simp only [outputCrossError,bitsSymmDiff,bitsJoin,bitsMeet,bitsComplement,inf_comm,sup_comm]

theorem finiteSourceCross_comm_r259 (e : ℕ ↪ Word) (i j : ℕ) (x y : ℕ → B) :
    finiteSourceCrossValue e i j x y = finiteSourceCrossValue e j i y x := by
  unfold finiteSourceCrossValue
  rw [sharedLabelIndices_comm_r255 e i j]
  exact congrArg iInf (funext (fun _ => inf_comm _ _))

def CrossingRank.swap (r : CrossingRank) : CrossingRank := ⟨r.j,r.i,r.atPrefix⟩

theorem finiteCrossRankTest_swap_r259 (e : ℕ ↪ Word) (k : ℕ) (r : CrossingRank) (x y : ℕ → B) :
    finiteCrossRankTest e k r x y = finiteCrossRankTest e k r.swap y x := by
  have hc : crispTruth B (labelsIncomp (e r.i) (e r.j)) =
      crispTruth B (labelsIncomp (e r.j) (e r.i)) :=
    crispTruth_propext_r188 ⟨fun h he => h (labelsComparable_symm_r255 he),
      fun h he => h (labelsComparable_symm_r255 he)⟩
  simp only [finiteCrossRankTest,CrossingRank.swap]
  rw [hc,finiteSourceCross_comm_r259 e r.i r.j x y,outputCrossError_comm_r259 x y]
  ac_rfl

theorem concreteCrossColorTable_symm_r259 (e : ℕ ↪ Word) (k : ℕ) (x y : ℕ → B) :
    colorValue (concreteCrossColorTable e k) x y = colorValue (concreteCrossColorTable e k) y x := by
  simp only [concreteCrossColorTable_value_r258,concreteCrossTestValue]
  exact le_antisymm
    (iSup_le (fun r => (finiteCrossRankTest_swap_r259 e k r x y).le.trans (le_iSup (fun s => finiteCrossRankTest e k s y x) r.swap)))
    (iSup_le (fun r => (finiteCrossRankTest_swap_r259 e k r y x).le.trans (le_iSup (fun s => finiteCrossRankTest e k s x y) r.swap)))

theorem concreteCrossColorValue_symmGraph_r259 (e : ℕ ↪ Word) (k : ℕ) (D : (ℕ → B) → B) :
    (⊤ : B) ≤ symmetricGraphValue D (concreteCrossColorTable e k) := by
  unfold symmetricGraphValue
  apply le_iInf
  intro x
  apply le_iInf
  intro y
  apply (le_materialImp_iff_r126 _ _ _).mpr
  exact (inf_le_right.trans inf_le_right).trans_eq (concreteCrossColorTable_symm_r259 e k x y)

theorem concreteCrossColorValue_noLoop_r259 (e : ℕ ↪ Word) (k : ℕ) (x : ℕ → B)
    {p : B} (hN : p≤capNeatValue e (crossCap x)) :
    p ⊓ colorValue (concreteCrossColorTable e k) x x ≤ ⊥ := by
  rw [concreteCrossColorTable_value_r258]
  apply le_of_dense_named_refinements_r219
  intro q hq hQ
  obtain ⟨r,t,ht,htq,hT⟩ := exists_nonzero_below_choice_r135 q hq
    (fun r => finiteCrossRankTest e k r x x) (hQ.trans inf_le_right)
  have hI : labelsIncomp (e r.i) (e r.j) :=
    prop_of_le_crisp_nonzero_r190 ht (hT.trans inf_le_left)
  have hC : labelsComparable (e r.i) (e r.j) :=
    prop_of_le_crisp_nonzero_r190 ht (capNeatValue_test_r256 e (crossCap x)
      (htq.trans (hQ.trans (inf_le_left.trans hN))) r.i r.j
      (hT.trans (inf_le_right.trans inf_le_left))
      (hT.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))))
  exact (hI hC).elim

theorem concreteCrossColorValue_edge_r259 (e : ℕ ↪ Word) (k : ℕ) (x y : ℕ → B)
    {p : B} (hX : p≤capNeatValue e (crossCap x)) (hY : p≤capNeatValue e (crossCap y))
    (hBx : p≤bitsBelowValue (crossPay x) (crossCap x))
    (hBy : p≤bitsBelowValue (crossPay y) (crossCap y)) :
    p ⊓ colorValue (concreteCrossColorTable e k) x y ≤
      sourceCrossEq x y ⊓ (smallAllPrefixes true k (outputCrossError x y))ᶜ := by
  rw [concreteCrossColorTable_value_r258]
  apply le_of_dense_named_refinements_r219
  intro q hq hQ
  obtain ⟨r,t,ht,htq,hT⟩ := exists_nonzero_below_choice_r135 q hq
    (fun r => finiteCrossRankTest e k r x y) (hQ.trans inf_le_right)
  have hp : t≤p := htq.trans (hQ.trans inf_le_left)
  have hI : labelsIncomp (e r.i) (e r.j) :=
    prop_of_le_crisp_nonzero_r190 ht (hT.trans inf_le_left)
  have hi : t≤crossCap x r.i := hT.trans (inf_le_right.trans inf_le_left)
  have hj : t≤crossCap y r.j := hT.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have hs : t≤finiteSourceCrossValue e r.i r.j x y :=
    hT.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
  have hb : t≤(nameBudgetValue true (realBitsName (outputCrossError x y))
      (realBitsName (fun _ => ⊥)) k r.atPrefix)ᶜ :=
    hT.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
  have hCross := finiteSourceCross_suffices_r256 e r.i r.j x y hI
    (hp.trans hX) (hp.trans hY) (hp.trans hBx) (hp.trans hBy) hi hj hs
  have hPref : smallAllPrefixes true k (outputCrossError x y)≤
      nameBudgetValue true (realBitsName (outputCrossError x y))
        (realBitsName (fun _ => ⊥)) k r.atPrefix := iInf_le _ r.atPrefix
  exact ⟨t,ht,htq,le_inf hCross (hb.trans (compl_le_compl hPref))⟩

end SetLanguage
end JSP000933
