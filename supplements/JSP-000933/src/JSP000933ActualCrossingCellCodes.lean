import JSP000933CrossingCellBudgetBound

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def crossCap (x : ℕ → B) : ℕ → B := extract4 x 0
def crossPay (x : ℕ → B) : ℕ → B := extract4 x 1
def crossOutCap (x : ℕ → B) : ℕ → B := extract4 x 2
def crossOutPay (x : ℕ → B) : ℕ → B := extract4 x 3

def anchoredError (H x : ℕ → B) : ℕ → B :=
  bitsSymmDiff (bitsMeet H (crossOutCap x)) (crossOutPay x)

def outputCrossError (x y : ℕ → B) : ℕ → B :=
  bitsSymmDiff (bitsMeet (crossOutCap x) (crossOutPay y))
    (bitsMeet (crossOutCap y) (crossOutPay x))

abbrev CrossCellCode := {uv : Word × Word // uv.2.length = uv.1.length}

noncomputable def crossingCellValue (H : ℕ → B) (k : ℕ) (uv : CrossCellCode) (x : ℕ → B) : B :=
  smallTailPrefixes true (2*k) uv.1.1.length (anchoredError H x) ⊓
    (cylinderValue (crossOutCap x) uv.1.1 ⊓ cylinderValue (crossOutPay x) uv.1.2)

theorem realEqValue_bitsMeet_mask_r251 {p : B} {x x' y y' : ℕ → B}
    (hx : p≤realEqValue x x') (hy : p≤realEqValue y y') :
    p≤realEqValue (bitsMeet x y) (bitsMeet x' y') :=
  (le_realEqValue_iff_r126 _ _ _).mpr (fun i => mask_inf_congr_r126
    ((le_realEqValue_iff_r126 _ _ _).mp hx i) ((le_realEqValue_iff_r126 _ _ _).mp hy i))

theorem realEqValue_bitsSymmDiff_mask_r251 {p : B} {x x' y y' : ℕ → B}
    (hx : p≤realEqValue x x') (hy : p≤realEqValue y y') :
    p≤realEqValue (bitsSymmDiff x y) (bitsSymmDiff x' y') := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro i
  have hX := (le_realEqValue_iff_r126 _ _ _).mp hx i
  have hY := (le_realEqValue_iff_r126 _ _ _).mp hy i
  exact mask_sup_congr_r211 (mask_inf_congr_r126 hX (mask_compl_congr_r126 hY))
    (mask_inf_congr_r126 (mask_compl_congr_r126 hX) hY)

theorem smallTailPrefixes_mask_r251 {p : B} {x y : ℕ → B} (he : p≤realEqValue x y)
    (h : Bool) (k N : ℕ) :
    p ⊓ smallTailPrefixes h k N x = p ⊓ smallTailPrefixes h k N y := by
  apply mask_iInf_congr_r126
  intro n
  have hx (i : ℕ) (hi : i<n) : p ⊓ membershipBits (realBitsName x) i =
      p ⊓ membershipBits (realBitsName y) i := by
    simpa only [membershipBits_realBitsName_r128] using (le_realEqValue_iff_r126 _ _ _).mp he i
  exact mask_sup_congr_r211 rfl
    (nameBudgetValue_mask_r226 (C := realBitsName (fun _ => ⊥)) (C' := realBitsName (fun _ => ⊥))
      hx (fun _ _ => rfl) h k)

theorem crossingCell_ext_r251 (H : ℕ → B) (k : ℕ) (uv : CrossCellCode) :
    RealTestExt (crossingCellValue H k uv) := by
  intro p x y he
  have hC : p≤realEqValue (crossOutCap x) (crossOutCap y) := extract4_mask_r240 he 2
  have hP : p≤realEqValue (crossOutPay x) (crossOutPay y) := extract4_mask_r240 he 3
  have hH : p≤realEqValue H H := (le_realEqValue_iff_r126 _ _ _).mpr (fun _ => rfl)
  have hE : p≤realEqValue (anchoredError H x) (anchoredError H y) :=
    realEqValue_bitsSymmDiff_mask_r251 (realEqValue_bitsMeet_mask_r251 hH hC) hP
  exact mask_inf_congr_r126 (smallTailPrefixes_mask_r251 hE true (2*k) uv.1.1.length)
    (mask_inf_congr_r126 (mask_cylinder_congr_r127 hC uv.1.1)
      (mask_cylinder_congr_r127 hP uv.1.2))

theorem crossingCells_cover_of_null_r251 (H x : ℕ → B) (k : ℕ) (hk : k≠0) {p : B}
    (hN : LocalLE true p (anchoredError H x) (fun _ => ⊥)) :
    p≤⨆ uv : CrossCellCode, crossingCellValue H k uv x := by
  have h2 : 2*k≠0 := by omega
  have hTail : p≤⨆ N : ℕ, smallTailPrefixes true (2*k) N (anchoredError H x) :=
    hN.trans (nameOrder_positiveTails_r229 true _ _ (2*k) h2)
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨N,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq
    (fun N => smallTailPrefixes true (2*k) N (anchoredError H x)) (hqp.trans hTail)
  obtain ⟨u,hu,s,hs,hsr,hS⟩ := exists_decided_initialWord_r136 (crossOutCap x) N r hr
  obtain ⟨v,hv,t,ht,hts,hT⟩ := exists_decided_initialWord_r136 (crossOutPay x) N s hs
  let uv : CrossCellCode := ⟨(u,v),hv.trans hu.symm⟩
  refine ⟨t,ht,hts.trans (hsr.trans hrq),le_iSup_of_le uv ?_⟩
  exact le_inf ((hts.trans (hsr.trans hR)).trans_eq (by rw [hu]))
    (le_inf (hts.trans hS) hT)

theorem crossingCells_pairError_small_r251 (H x y : ℕ → B) (k : ℕ) (uv : CrossCellCode)
    {p : B} (hx : p≤crossingCellValue H k uv x) (hy : p≤crossingCellValue H k uv y) :
    p ≤ smallAllPrefixes true k (outputCrossError x y) :=
  anchor_crossError_smallAll_r250 true H (crossOutCap x) (crossOutPay x) (crossOutCap y) (crossOutPay y)
    k uv.1.1 uv.1.2 uv.2 (hx.trans (inf_le_right.trans inf_le_left))
    (hy.trans (inf_le_right.trans inf_le_left)) (hx.trans (inf_le_right.trans inf_le_right))
    (hy.trans (inf_le_right.trans inf_le_right)) (hx.trans inf_le_left) (hy.trans inf_le_left)

end SetLanguage
end JSP000933
