import JSP000933CanonicalWordCylinder
import JSP000933OffDiagonalTable

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def symPairMem (W u v : bSet B) : B :=
  (bSet.pair u v ∈ᴮ W) ⊔ (bSet.pair v u ∈ᴮ W)

noncomputable def namedRawColorCode (W : bSet B) : Word × Word → B :=
  fun uv => symPairMem W (wordName uv.1) (wordName uv.2)

noncomputable def namedOpenColorCode (W : bSet B) : Word × Word → B :=
  offDiagonalTable (namedRawColorCode W)

noncomputable def namedRawEdgeValue (W A Z : bSet B) : B :=
  ⨆ u : bSet B, ⨆ v : bSet B,
    symPairMem W u v ⊓ (nameWordCylinderValue u A ⊓ nameWordCylinderValue v Z)

noncomputable def namedOpenEdgeValue (W A Z : bSet B) : B :=
  (A =ᴮ Z)ᶜ ⊓ namedRawEdgeValue W A Z

theorem transport_symPairMem_r177 {p : B} {W u v s t : bSet B}
    (hu : p ≤ u =ᴮ s) (hv : p ≤ v =ᴮ t) (h : p ≤ symPairMem W u v) :
    p ≤ symPairMem W s t := by
  unfold symPairMem at h ⊢
  apply (le_inf le_rfl h).trans
  rw [inf_sup_left]
  apply sup_le
  · exact (bSet.subst_congr_mem_left'
      (inf_le_left.trans (bSet.pair_congr hu hv)) inf_le_right).trans le_sup_left
  · exact (bSet.subst_congr_mem_left'
      (inf_le_left.trans (bSet.pair_congr hv hu)) inf_le_right).trans le_sup_right

theorem namedRawEdge_eq_color_r177 (W A Z : bSet B) :
    namedRawEdgeValue W A Z =
      colorValue (namedRawColorCode W) (membershipBits A) (membershipBits Z) := by
  apply le_antisymm
  · unfold namedRawEdgeValue
    apply iSup_le
    intro u
    apply iSup_le
    intro v
    apply le_of_dense_refinement_r176
    intro p hp hP
    have hU := hP.trans (inf_le_right.trans inf_le_left)
    have hV := hP.trans (inf_le_right.trans inf_le_right)
    rw [nameWordCylinder_eq_coded_r176] at hU hV
    obtain ⟨s,q,hq,hqp,hqS⟩ := exists_nonzero_below_choice_r135 p hp
      (fun s : Word => (u =ᴮ wordName s) ⊓ cylinderValue (membershipBits A) s) hU
    obtain ⟨t,r,hr,hrq,hrT⟩ := exists_nonzero_below_choice_r135 q hq
      (fun t : Word => (v =ᴮ wordName t) ⊓ cylinderValue (membershipBits Z) t) (hqp.trans hV)
    have hrp := hrq.trans hqp
    have hCode := transport_symPairMem_r177 (hrq.trans (hqS.trans inf_le_left))
      (hrT.trans inf_le_left) (hrp.trans (hP.trans inf_le_left))
    exact ⟨r,hr,hrp,edgeBox_suffices_r136 _ _ _ (s,t) hCode
      (hrq.trans (hqS.trans inf_le_right)) (hrT.trans inf_le_right)⟩
  · unfold colorValue
    apply iSup_le
    intro st
    apply le_iSup_of_le (wordName st.1)
    apply le_iSup_of_le (wordName st.2)
    refine le_inf inf_le_left (le_inf ?_ ?_)
    · rw [nameWordCylinder_eq_coded_r176]
      exact le_iSup_of_le st.1 (le_inf bSet.bv_refl (inf_le_right.trans inf_le_left))
    · rw [nameWordCylinder_eq_coded_r176]
      exact le_iSup_of_le st.2 (le_inf bSet.bv_refl (inf_le_right.trans inf_le_right))

theorem symPairMem_symm_r177 (W u v : bSet B) : symPairMem W u v = symPairMem W v u :=
  sup_comm _ _

theorem namedRawEdge_symm_r177 (W A Z : bSet B) :
    namedRawEdgeValue W A Z = namedRawEdgeValue W Z A := by
  unfold namedRawEdgeValue
  apply le_antisymm <;> apply iSup_le <;> intro u <;> apply iSup_le <;> intro v
  all_goals
    apply le_iSup_of_le v
    apply le_iSup_of_le u
    rw [symPairMem_symm_r177 W u v,inf_comm (nameWordCylinderValue u _)]

theorem namedOpenEdge_symm_r177 (W A Z : bSet B) :
    namedOpenEdgeValue W A Z = namedOpenEdgeValue W Z A := by
  unfold namedOpenEdgeValue
  rw [bSet.bv_eq_symm,namedRawEdge_symm_r177 W A Z]

theorem nameEq_mask_of_subsets_r177 {p : B} {A Z : bSet B}
    (hA : p ≤ A ⊆ᴮ bSet.omega) (hZ : p ≤ Z ⊆ᴮ bSet.omega) :
    p ⊓ (A =ᴮ Z) = p ⊓ realEqValue (membershipBits A) (membershipBits Z) := by
  apply le_antisymm
  · exact le_inf inf_le_left (le_realEq_of_nameEq_r128 inf_le_right)
  · exact le_inf inf_le_left (le_nameEq_of_realEq_for_subsets_r128
      (inf_le_left.trans hA) (inf_le_left.trans hZ) inf_le_right)

theorem namedOpenEdge_mask_eq_r177 (W : bSet B) {p : B} {A Z : bSet B}
    (hA : p ≤ A ⊆ᴮ bSet.omega) (hZ : p ≤ Z ⊆ᴮ bSet.omega) :
    p ⊓ namedOpenEdgeValue W A Z =
      p ⊓ colorValue (namedOpenColorCode W) (membershipBits A) (membershipBits Z) := by
  unfold namedOpenEdgeValue namedOpenColorCode
  rw [offDiagonalTable_color_r173,namedRawEdge_eq_color_r177]
  rw [inf_comm (colorValue (namedRawColorCode W) _ _)]
  exact mask_inf_congr_r126 (mask_compl_congr_r126 (nameEq_mask_of_subsets_r177 hA hZ)) rfl

theorem namedOpenEdge_canonical_r177 (W : bSet B) (x y : ℕ → B) :
    namedOpenEdgeValue W (realBitsName x) (realBitsName y) =
      colorValue (namedOpenColorCode W) x y := by
  simpa only [top_inf_eq,membershipBits_realBitsName_r128] using
    namedOpenEdge_mask_eq_r177 W (realBitsName_subset_r103 x) (realBitsName_subset_r103 y)

theorem namedOpenColor_valid_r177 (D : (ℕ → B) → B) (W : bSet B) :
    irreflexiveGraphValue D (namedOpenColorCode W) ⊓
      symmetricGraphValue D (namedOpenColorCode W) = (⊤ : B) := by
  apply top_unique
  apply le_inf
  · apply le_iInf
    intro x
    rw [← namedOpenEdge_canonical_r177]
    have h : ((realBitsName x : bSet B) =ᴮ realBitsName x) = (⊤ : B) :=
      top_unique bSet.bv_refl
    simp only [namedOpenEdgeValue,h,compl_top,bot_inf_eq,compl_bot,sup_top_eq,le_rfl]
  · apply le_iInf
    intro x
    apply le_iInf
    intro y
    rw [← namedOpenEdge_canonical_r177 W x y,← namedOpenEdge_canonical_r177 W y x]
    apply (le_materialImp_iff_r126 _ _ _).mpr
    rw [top_inf_eq,← namedOpenEdge_symm_r177 W (realBitsName x) (realBitsName y)]
    exact inf_le_right

end BooleanNames
end JSP000933
