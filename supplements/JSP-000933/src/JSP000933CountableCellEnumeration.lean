import JSP000933ActualCrossingCellCodes
import Mathlib.Logic.Equiv.List

open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem namedCountable_of_countableCells_r252 {I : Type} [Countable I] (C : bSet B) (p : B)
    (cell : I → (ℕ → B) → B) (hExt : ∀ i, RealTestExt (cell i))
    (hR : p≤namedAllRealsValue C)
    (hCov : ∀ x : ℕ → B, p ⊓ (realBitsName x ∈ᴮ C) ≤ ⨆ i, cell i x)
    (hU : ∀ i (x y : ℕ → B),
      p ⊓ ((realBitsName x ∈ᴮ C) ⊓ ((realBitsName y ∈ᴮ C) ⊓ (cell i x ⊓ cell i y))) ≤ realEqValue x y) :
    p≤weakCountabilityValue C := by
  classical
  obtain ⟨e,he⟩ := Set.countable_iff_exists_injOn.mp (Set.countable_univ (α := I))
  have hInj : Function.Injective e := fun _ _ hh => he (Set.mem_univ _) (Set.mem_univ _) hh
  let d (n : ℕ) (x : ℕ → B) := ⨆ i : {i : I // e i=n}, cell i.1 x
  have hD (n : ℕ) : RealTestExt (d n) := by
    intro q x y hq
    exact mask_iSup_congr_r126 (fun i : {i : I // e i=n} => hExt i.1 q x y hq)
  refine namedCountable_of_cells_r245 C p d hD hR ?_ ?_
  · intro x
    apply (hCov x).trans
    apply iSup_le
    intro i
    exact le_iSup_of_le (e i) (le_iSup (fun j : {j : I // e j=e i} => cell j.1 x) ⟨i,rfl⟩)
  · intro n x y
    apply le_of_dense_named_refinements_r219
    intro q hq hQ
    have hX : q≤d n x := hQ.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_left)))
    have hY : q≤d n y := hQ.trans (inf_le_right.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))
    obtain ⟨i,r,hr,hrq,hRi⟩ := exists_nonzero_below_choice_r135 q hq
      (fun i : {i : I // e i=n} => cell i.1 x) hX
    obtain ⟨j,s,hs,hsr,hSj⟩ := exists_nonzero_below_choice_r135 r hr
      (fun i : {i : I // e i=n} => cell i.1 y) (hrq.trans hY)
    have heq : i.1=j.1 := hInj (i.2.trans j.2.symm)
    have hsQ := hsr.trans (hrq.trans hQ)
    refine ⟨s,hs,hsr.trans hrq,?_⟩
    have hsP : s ≤ p := hsQ.trans inf_le_left
    have hsX : s ≤ realBitsName x ∈ᴮ C := hsQ.trans (inf_le_right.trans inf_le_left)
    have hsY : s ≤ realBitsName y ∈ᴮ C :=
      hsQ.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have hsCellY : s ≤ cell i.val y := hSj.trans_eq (congrArg (fun j => cell j y) heq.symm)
    exact (le_inf hsP (le_inf hsX (le_inf hsY (le_inf (hsr.trans hRi) hsCellY)))).trans (hU i.val x y)

theorem crossCellCode_countable_r252 : Countable CrossCellCode := inferInstance

end SetLanguage
end JSP000933
