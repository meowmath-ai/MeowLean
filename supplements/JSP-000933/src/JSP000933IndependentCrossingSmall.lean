import JSP000933ActualBranchLabelIncompatibility

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem sourceCrossEq_le_finite_r270 (e : ℕ ↪ Word) (i j : ℕ) (x y : ℕ → B) :
    sourceCrossEq x y≤finiteSourceCrossValue e i j x y := by
  unfold sourceCrossEq realEqValue finiteSourceCrossValue
  exact le_iInf (fun m => iInf_le _ m.val)

theorem noConcreteCrossing_small_r270 (e : ℕ ↪ Word) (k : ℕ) (x y : ℕ → B)
    {p : B} (hI : p≤actualIncompCaps e (crossCap x) (crossCap y)) (hSrc : p ≤ sourceCrossEq x y)
    (hN : p≤(colorValue (concreteCrossColorTable e k) x y)ᶜ) :
    p ≤ smallAllPrefixes true k (outputCrossError x y) := by
  unfold smallAllPrefixes
  apply le_iInf
  intro n
  let V := nameBudgetValue true (realBitsName (outputCrossError x y)) (realBitsName (fun _ => ⊥)) k n
  change p≤V
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨i,s,hs,hsq,hS⟩ := exists_nonzero_below_choice_r135 q hq
    (fun i => ⨆ j, crispTruth B (labelsIncomp (e i) (e j))⊓(crossCap x i⊓crossCap y j)) (hqp.trans hI)
  obtain ⟨j,t,ht,hts,hT⟩ := exists_nonzero_below_choice_r135 s hs
    (fun j => crispTruth B (labelsIncomp (e i) (e j))⊓(crossCap x i⊓crossCap y j)) hS
  have htq := hts.trans hsq
  have htp := htq.trans hqp
  let r : CrossingRank := ⟨i,j,n⟩
  have hRank : t⊓Vᶜ≤finiteCrossRankTest e k r x y := by
    unfold finiteCrossRankTest
    exact le_inf (inf_le_left.trans (hT.trans inf_le_left))
      (le_inf (inf_le_left.trans (hT.trans (inf_le_right.trans inf_le_left)))
        (le_inf (inf_le_left.trans (hT.trans (inf_le_right.trans inf_le_right)))
          (le_inf (inf_le_left.trans (htp.trans (hSrc.trans (sourceCrossEq_le_finite_r270 e i j x y))))
            inf_le_right)))
  have hColor : t⊓Vᶜ≤colorValue (concreteCrossColorTable e k) x y :=
    (le_iSup_of_le r hRank).trans_eq (concreteCrossColorTable_value_r258 e k x y).symm
  have hBot : t⊓Vᶜ≤⊥ :=
    (le_inf hColor (inf_le_left.trans (htp.trans hN))).trans_eq inf_compl_eq_bot'
  exact ⟨t,ht,htq,
    (le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hBot)).trans_eq (compl_compl V)⟩

theorem sourceCrossEq_of_prefix_and_late_disjoint_r270 (x y : ℕ → B) (r : ℕ)
    {p : B} (hPre : ∀ m<4*r, p⊓x m=p⊓y m)
    (hD : p≤afterCutDisjointValue (crossCap y) (crossCap x) r)
    (hX : p≤bitsBelowValue (crossPay x) (crossCap x))
    (hY : p≤bitsBelowValue (crossPay y) (crossCap y)) : p ≤ sourceCrossEq x y := by
  unfold sourceCrossEq
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  by_cases hm : m<r
  · have hC := extract4_maskAt_r257 hPre 0 m hm
    have hP := extract4_maskAt_r257 hPre 1 m hm
    exact mask_inf_congr_r126 hC hP.symm
  · have h := afterCutDisjointValue_apply_r268 hD m (Nat.le_of_not_gt hm)
    have hL : p⊓(crossCap x m⊓crossPay y m)≤⊥ :=
      (le_inf inf_le_left (le_inf
        ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans (bitsBelowValue_apply_r256 hY m))
        (inf_le_right.trans inf_le_left))).trans h
    have hR : p⊓(crossCap y m⊓crossPay x m)≤⊥ :=
      (le_inf inf_le_left (le_inf (inf_le_right.trans inf_le_left)
        ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans
          (bitsBelowValue_apply_r256 hX m)))).trans h
    exact (le_bot_iff.mp hL).trans (le_bot_iff.mp hR).symm

end SetLanguage
end JSP000933
