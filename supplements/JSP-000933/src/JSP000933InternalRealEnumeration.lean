import JSP000933BooleanFunctionalGraphs
import JSP000933FiniteOrdinalLabels
import JSP000933SmallRealNames

open scoped Flypitch Cardinal
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open BooleanCompletion OpenGraphForcing

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def realBitsName (g : ℕ → B) : bSet B :=
  familyName (fun k : ULift ℕ => bSet.of_nat k.down) (fun k => g k.down)

theorem realBitsName_top_r103 :
    realBitsName (fun _ : ℕ => (⊤ : B)) = (bSet.omega : bSet B) := rfl

theorem realBitsName_subset_r103 (g : ℕ → B) :
    (⊤ : B) ≤ realBitsName g ⊆ᴮ bSet.omega := by
  rw [← realBitsName_top_r103 (B := B)]
  exact (familyName_subset_ambient_r70
    (fun k : ULift ℕ => bSet.of_nat k.down) (fun k => g k.down)).ge

theorem realBitsName_represents_r103 (x : bSet B) {p : B} (h : p ≤ x ⊆ᴮ bSet.omega) :
    p ≤ x =ᴮ realBitsName (fun n => bSet.of_nat n ∈ᴮ x) := by
  rw [← realBitsName_top_r103 (B := B)] at h
  exact familyName_represents_subset_r70 (fun k : ULift ℕ => bSet.of_nat k.down) x p h

theorem exists_surjection_checked_omegaOne_r103
    (e : OmegaOneIndex → ℕ → B) (he : Function.Surjective e) :
    (⊤ : B) ≤ bSet.surjects_onto (bSet.check (PSet.ordinalMk ((ℵ₁ : Cardinal).ord)))
      (bSet.bv_powerset bSet.omega) := by
  let a : OmegaOneIndex → bSet B := omegaOneCheckName
  let y (i : OmegaOneIndex) := realBitsName (e i)
  let D := familyName a (fun _ => ⊤)
  let R : bSet B := bSet.bv_powerset bSet.omega
  let F := functionalGraphName a y
  rw [check_omegaOne_eq_family_r83]
  apply le_iSup_of_le F
  refine le_inf (le_inf ?_ ?_) ?_
  · exact functionValue_functionalGraph_r102 a y (fun _ _ h => omegaOneCheck_eq_bot_r83 h)
  · exact totalValue_functionalGraph_r102 a y R (fun i =>
      bSet.bv_powerset_spec.mp (realBitsName_subset_r103 (e i)))
  · apply le_iInf
    intro z
    rw [← _root_.deduction,top_inf_eq]
    let p := z ∈ᴮ R
    obtain ⟨i,hi⟩ := he (fun n => bSet.of_nat n ∈ᴮ z)
    have hEq : p ≤ z =ᴮ y i := by
      have hSub : p ≤ z ⊆ᴮ bSet.omega := bSet.bv_powerset_spec.mpr le_rfl
      have hh := realBitsName_represents_r103 z hSub
      simpa only [y,hi] using hh
    have ha : (⊤ : B) ≤ a i ∈ᴮ D := bSet.mem_mk a (fun _ => ⊤) i
    apply le_iSup_of_le (a i)
    apply le_inf (le_top.trans ha)
    have hp : p ≤ bSet.pair (a i) (y i) =ᴮ bSet.pair (a i) z :=
      bSet.pair_congr bSet.bv_refl (hEq.trans_eq bSet.bv_eq_symm)
    exact bSet.subst_congr_mem_left' hp (le_top.trans (pair_mem_functionalGraph_self_r102 a y i))

theorem properStage_checked_omegaOne_surjects_reals_r103 {P : Type} [Preorder P] [Nonempty P]
    (hCCC : BooleanCCC (RO P)) (hSize : Cardinal.mk P ≤ ℵ₁)
    (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    (⊤ : RO P) ≤ bSet.surjects_onto (bSet.check (PSet.ordinalMk ((ℵ₁ : Cardinal).ord)))
      (bSet.bv_powerset bSet.omega) := by
  obtain ⟨e,he⟩ := exists_omegaOneEnumeration_of_bits_r99 hCCC hSize CH
  exact exists_surjection_checked_omegaOne_r103 e he

end BooleanNames
end JSP000933
