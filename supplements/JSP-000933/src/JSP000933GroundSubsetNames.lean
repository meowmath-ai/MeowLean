import JSP000933CountablyClosedNoReals
import JSP000933CheckedNaturals
import JSP000933CouplingForcing
import JSP000933BooleanNamedCliqueStage

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace PositiveForcing

open CantorCodes BooleanNames BooleanCompletion Erdos1123

noncomputable def groundSubsetBits (B : Type) [CompleteBooleanAlgebra B] (a : Set ℕ) : ℕ → B := by
  classical
  exact fun n => if n ∈ a then ⊤ else ⊥

noncomputable def groundSubsetName (B : Type) [NontrivialCompleteBooleanAlgebra B] (a : Set ℕ) : bSet B :=
  realBitsName (groundSubsetBits B a)

theorem realCode_value_is_groundBits_r186 (B : Type) [CompleteBooleanAlgebra B] (x : ℕ → Bool) :
    (fun n => (truthBit (x n) : B)) = groundSubsetBits B {n | x n = true} := by
  classical
  funext n
  by_cases h : x n = true <;> simp [truthBit,groundSubsetBits,h]

theorem omegaSubset_le_iSup_ground_r186 {P : Type} [Preorder P] [Nonempty P]
    (hP : IsCountablyClosed P) (x : bSet (RO P)) :
    (x ⊆ᴮ bSet.omega) ≤ ⨆ a : Set ℕ, x =ᴮ groundSubsetName (RO P) a := by
  let B := RO P
  let p := x ⊆ᴮ bSet.omega
  have hR : p ≤ x =ᴮ realBitsName (membershipBits x) := realBitsName_represents_r103 x le_rfl
  have hG := groundBitNames_join_top_r185 hP (membershipBits x)
  calc
    p = p ⊓ (⨆ b : ℕ → Bool, realEqValue (membershipBits x) (fun n => truthBit (b n))) := by
      rw [hG,inf_top_eq]
    _ ≤ _ := by
      rw [inf_iSup_eq]
      apply iSup_le
      intro b
      rw [realCode_value_is_groundBits_r186 B b]
      apply le_iSup_of_le ({n | b n = true} : Set ℕ)
      exact bSet.bv_trans (inf_le_left.trans hR)
        (inf_le_right.trans_eq (realBitsName_eq_r128 _ _).symm)

theorem coupling_countablyClosed_r186 {W V : WeightSequence ℕ} :
    IsCountablyClosed (CouplingCondition W V) :=
  descending_lower_r183

end PositiveForcing
end JSP000933
