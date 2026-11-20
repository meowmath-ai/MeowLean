import JSP000933NamedOpenEdge

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def closedCoverName (c : CoverCode B) : bSet B :=
  familyName (fun nw : ℕ × Word => bSet.pair (bSet.of_nat nw.1) (wordName nw.2))
    (fun nw => c nw.1 nw.2)

noncomputable def namedSectionOpen (H i A : bSet B) : B :=
  ⨆ w : bSet B, (bSet.pair i w ∈ᴮ H) ⊓ nameWordCylinderValue w A

noncomputable def namedSectionClosed (H i A : bSet B) : B :=
  (namedSectionOpen H i A)ᶜ

theorem namedSectionClosed_unfold_r178 (H i A : bSet B) :
    namedSectionClosed H i A =
      ⨅ w : bSet B, imp (bSet.pair i w ∈ᴮ H) (nameWordCylinderValue w A)ᶜ := by
  simp only [namedSectionClosed,namedSectionOpen,compl_iSup,compl_inf,_root_.imp]

theorem mask_nameWordCylinder_r178 (w A : bSet B) (u : Word) {p : B}
    (hp : p ≤ w =ᴮ wordName u) :
    p ⊓ nameWordCylinderValue w A = p ⊓ cylinderValue (membershipBits A) u := by
  rw [nameWordCylinder_eq_coded_r176]
  apply le_antisymm
  · apply Lattice.bv_cases_right
    intro v
    by_cases hv : v = u
    · subst v
      exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · have hh : p ⊓ ((w =ᴮ wordName v) ⊓ cylinderValue (membershipBits A) v) ≤
          (wordName v : bSet B) =ᴮ wordName u :=
        bSet.bv_trans ((inf_le_right.trans inf_le_left).trans_eq bSet.bv_eq_symm) (inf_le_left.trans hp)
      exact (hh.trans_eq (wordNames_separated_r175 hv)).trans bot_le
  · apply le_inf inf_le_left
    apply le_iSup_of_le u
    exact le_inf (inf_le_left.trans hp) inf_le_right

theorem closedCoverName_open_eq_r178 (c : CoverCode B) (n : ℕ) (A : bSet B) :
    namedSectionOpen (closedCoverName c) (bSet.of_nat n) A =
      openValue (c n) (membershipBits A) := by
  apply le_antisymm
  · unfold namedSectionOpen
    apply iSup_le
    intro w
    unfold closedCoverName
    rw [mem_familyName_r70]
    apply Lattice.bv_cases_left
    intro i
    let q := (c i.1 i.2 ⊓
      (bSet.pair (bSet.of_nat n) w =ᴮ bSet.pair (bSet.of_nat i.1) (wordName i.2))) ⊓
      nameWordCylinderValue w A
    by_cases hn : n = i.1
    · have hEq : q ≤ w =ᴮ wordName i.2 :=
        (inf_le_left.trans inf_le_right).trans bSet.eq_of_eq_pair_right
      have hCyl : q ≤ cylinderValue (membershipBits A) i.2 :=
        ((le_inf le_rfl (show q ≤ nameWordCylinderValue w A from inf_le_right)).trans_eq
          (mask_nameWordCylinder_r178 w A i.2 hEq)).trans inf_le_right
      refine le_iSup_of_le i.2 (le_inf ?_ hCyl)
      exact (show q ≤ c i.1 i.2 from inf_le_left.trans inf_le_left).trans_eq
        (congrArg (fun n => c n i.2) hn).symm
    · have hZero : q ≤ (⊥ : B) :=
        ((inf_le_left.trans inf_le_right).trans bSet.eq_of_eq_pair_left).trans_eq
          (checkedNat_eq_bot_r174 hn)
      exact hZero.trans bot_le
  · unfold openValue
    apply iSup_le
    intro u
    apply le_iSup_of_le (wordName u)
    refine le_inf ?_ ?_
    · exact inf_le_left.trans
        (bSet.mem_mk
          (fun nw : ℕ × Word => bSet.pair (bSet.of_nat nw.1) (wordName nw.2))
          (fun nw => c nw.1 nw.2) (n,u))
    · rw [nameWordCylinder_eq_coded_r176]
      exact le_iSup_of_le u (le_inf bSet.bv_refl inf_le_right)

theorem closedCoverName_closed_eq_r178 (c : CoverCode B) (n : ℕ) (A : bSet B) :
    namedSectionClosed (closedCoverName c) (bSet.of_nat n) A =
      ClosedMember c n (membershipBits A) :=
  congrArg (fun b : B => bᶜ) (closedCoverName_open_eq_r178 c n A)

theorem namedSectionClosed_index_mask_r178 (H A : bSet B) {i j : bSet B} {p : B}
    (he : p ≤ i =ᴮ j) :
    p ⊓ namedSectionClosed H i A = p ⊓ namedSectionClosed H j A := by
  apply mask_compl_congr_r126
  unfold namedSectionOpen
  rw [inf_iSup_eq,inf_iSup_eq]
  apply congrArg (fun f : bSet B → B => iSup f)
  funext w
  apply mask_inf_congr_r126 _ rfl
  exact maskedMem_left_r175 (bSet.pair_congr he bSet.bv_refl)

end BooleanNames
end JSP000933
