import JSP000933ActualGraphCodeName

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def coverTableOfName (H : bSet B) : CoverCode B :=
  fun n u => bSet.pair (bSet.of_nat n) (wordName u) ∈ᴮ H

theorem namedSectionOpen_to_table_r242 (H A : bSet B) (n : ℕ) :
    namedSectionOpen H (bSet.of_nat n) A = openValue (coverTableOfName H n) (membershipBits A) := by
  apply le_antisymm
  · unfold namedSectionOpen
    apply iSup_le
    intro w
    rw [nameWordCylinder_eq_coded_r176]
    apply Lattice.bv_cases_right
    intro u
    let p := (bSet.pair (bSet.of_nat n) w ∈ᴮ H) ⊓
      ((w =ᴮ wordName u) ⊓ cylinderValue (membershipBits A) u)
    have hEq : p ≤ bSet.pair (bSet.of_nat n) w =ᴮ bSet.pair (bSet.of_nat n) (wordName u) :=
      bSet.pair_congr bSet.bv_refl (inf_le_right.trans inf_le_left)
    have hMem : p ≤ coverTableOfName H n u := bSet.subst_congr_mem_left' hEq inf_le_left
    exact le_iSup_of_le u (le_inf hMem (inf_le_right.trans inf_le_right))
  · unfold openValue
    apply iSup_le
    intro u
    apply le_iSup_of_le (wordName u)
    refine le_inf inf_le_left ?_
    rw [nameWordCylinder_eq_coded_r176]
    exact le_iSup_of_le u (le_inf bSet.bv_refl inf_le_right)

theorem namedSectionClosed_to_table_r242 (H A : bSet B) (n : ℕ) :
    namedSectionClosed H (bSet.of_nat n) A = ClosedMember (coverTableOfName H) n (membershipBits A) :=
  congrArg (fun b : B => bᶜ) (namedSectionOpen_to_table_r242 H A n)

end SetLanguage
end JSP000933
