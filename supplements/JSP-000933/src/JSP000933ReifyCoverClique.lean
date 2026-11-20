import JSP000933ClosedCoverName
import JSP000933WeakCountability

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes FiniteSupport

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def namedAllRealsValue (X : bSet B) : B :=
  ⨅ A : bSet B, imp (A ∈ᴮ X) (A ⊆ᴮ bSet.omega)

noncomputable def namedCliqueValue (X W C : bSet B) : B :=
  (C ⊆ᴮ X) ⊓ ((weakCountabilityValue C)ᶜ ⊓
    (⨅ A : bSet B, ⨅ Z : bSet B,
      imp ((A ∈ᴮ C) ⊓ ((Z ∈ᴮ C) ⊓ (A =ᴮ Z)ᶜ)) (namedOpenEdgeValue W A Z)))

noncomputable def namedCoverValue (X W H : bSet B) : B :=
  (⨅ A : bSet B, imp (A ∈ᴮ X)
      (⨆ i : bSet B, (i ∈ᴮ bSet.omega) ⊓ namedSectionClosed H i A)) ⊓
  (⨅ i : bSet B, ⨅ A : bSet B, ⨅ Z : bSet B,
    imp ((i ∈ᴮ bSet.omega) ⊓ ((A ∈ᴮ X) ⊓ ((Z ∈ᴮ X) ⊓
      (namedSectionClosed H i A ⊓ namedSectionClosed H i Z)))) (namedOpenEdgeValue W A Z)ᶜ)

theorem nativeDomain_ext_r179 (X : bSet B) :
    RealTestExt (fun x => realBitsName x ∈ᴮ X) := by
  intro p x y h
  apply maskedMem_left_r175
  exact h.trans_eq (realBitsName_eq_r128 x y).symm

theorem in_named_subset_bitName_r179 {X A : bSet B} {p : B}
    (hX : p ≤ namedAllRealsValue X) (hA : p ≤ A ∈ᴮ X) :
    p ≤ A ⊆ᴮ bSet.omega ∧ p ≤ realBitsName (membershipBits A) ∈ᴮ X := by
  have hs : p ≤ A ⊆ᴮ bSet.omega := _root_.context_imp_elim (hX.trans (iInf_le _ A)) hA
  exact ⟨hs,bSet.subst_congr_mem_left' (realBitsName_represents_r103 A hs) hA⟩

theorem named_cover_of_goodCode_r179 (X W : bSet B) (c : CoverCode B) (p : B)
    (hX : p ≤ namedAllRealsValue X)
    (hc : p ≤ goodCoverValue id (fun x => realBitsName x ∈ᴮ X) (namedOpenColorCode W) c) :
    p ≤ namedCoverValue X W (closedCoverName c) := by
  let H := closedCoverName c
  let D (x : ℕ → B) := realBitsName x ∈ᴮ X
  let K := namedOpenColorCode W
  have hcov : p ≤ coverValue id D c := hc.trans inf_le_left
  have hind : p ≤ independentValue id D K c := hc.trans inf_le_right
  refine le_inf ?_ ?_
  · apply le_iInf
    intro A
    rw [← _root_.deduction]
    let q := p ⊓ (A ∈ᴮ X)
    have hD := (in_named_subset_bitName_r179 (inf_le_left.trans hX)
      (show q ≤ A ∈ᴮ X from inf_le_right)).2
    have h := (le_materialImp_iff_r126 p (D (membershipBits A))
      (⨆ n, ClosedMember c n (membershipBits A))).mp (hcov.trans (iInf_le _ (membershipBits A)))
    apply ((le_inf (show q ≤ p from inf_le_left) hD).trans h).trans
    apply iSup_le
    intro n
    apply le_iSup_of_le (bSet.of_nat n)
    exact le_inf bSet.omega_definite ((closedCoverName_closed_eq_r178 c n A).symm.le)
  · apply le_iInf
    intro i
    apply le_iInf
    intro A
    apply le_iInf
    intro Z
    rw [← _root_.deduction]
    apply le_of_dense_refinement_r176
    intro s hs hS
    have hi : s ≤ i ∈ᴮ bSet.omega := hS.trans (inf_le_right.trans inf_le_left)
    obtain ⟨n,q,hq,hqs,he⟩ := exists_nonzero_below_choice_r135 s hs
      (fun n : ℕ => i =ᴮ bSet.of_nat n) (hi.trans_eq (memberOmega_cases_r174 i))
    have hqS := hqs.trans hS
    have hqp : q ≤ p := hqS.trans inf_le_left
    have hAnte := hqS.trans inf_le_right
    have hA : q ≤ A ∈ᴮ X := hAnte.trans (inf_le_right.trans inf_le_left)
    have hZ : q ≤ Z ∈ᴮ X := hAnte.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))
    have hCl : q ≤ namedSectionClosed H i A ⊓ namedSectionClosed H i Z :=
      hAnte.trans (inf_le_right.trans (inf_le_right.trans inf_le_right))
    obtain ⟨hAs,hAD⟩ := in_named_subset_bitName_r179 (hqp.trans hX) hA
    obtain ⟨hZs,hZD⟩ := in_named_subset_bitName_r179 (hqp.trans hX) hZ
    have hCA : q ≤ ClosedMember c n (membershipBits A) :=
      (((le_inf le_rfl (hCl.trans inf_le_left)).trans_eq
        (namedSectionClosed_index_mask_r178 H A he)).trans inf_le_right).trans_eq
          (closedCoverName_closed_eq_r178 c n A)
    have hCZ : q ≤ ClosedMember c n (membershipBits Z) :=
      (((le_inf le_rfl (hCl.trans inf_le_right)).trans_eq
        (namedSectionClosed_index_mask_r178 H Z he)).trans inf_le_right).trans_eq
          (closedCoverName_closed_eq_r178 c n Z)
    let P := (D (membershipBits A) ⊓ D (membershipBits Z)) ⊓
      (ClosedMember c n (membershipBits A) ⊓ ClosedMember c n (membershipBits Z))
    have hImp : p ≤ Pᶜ ⊔ (colorValue K (membershipBits A) (membershipBits Z))ᶜ :=
      hind.trans (iInf_le _ (n,membershipBits A,membershipBits Z))
    have hK := (le_inf hqp (le_inf (le_inf hAD hZD) (le_inf hCA hCZ))).trans
      ((le_materialImp_iff_r126 _ _ _).mp hImp)
    refine ⟨q,hq,hqs,?_⟩
    exact ((le_inf le_rfl hK).trans_eq
      (mask_compl_congr_r126 (namedOpenEdge_mask_eq_r177 W hAs hZs)).symm).trans inf_le_right

theorem named_clique_of_weighted_r179 (X W : bSet B) (x : OpenGraphForcing.OmegaOneIndex → ℕ → B)
    (g : OpenGraphForcing.OmegaOneIndex → B) (p : B) (hX : p ≤ namedAllRealsValue X)
    (h : p ≤ weightedCliqueValue (fun x => realBitsName x ∈ᴮ X) (namedOpenColorCode W) x g) :
    ∃ C : bSet B, p ≤ namedCliqueValue X W C := by
  let K := namedOpenColorCode W
  obtain ⟨C,hC,hE,hN⟩ := realize_weightedClique_r172 X K x g p h
  refine ⟨C,le_inf (le_top.trans hC) (le_inf hN ?_)⟩
  apply le_iInf
  intro A
  apply le_iInf
  intro Z
  rw [← _root_.deduction]
  let q := p ⊓ ((A ∈ᴮ C) ⊓ ((Z ∈ᴮ C) ⊓ (A =ᴮ Z)ᶜ))
  have hA : q ≤ A ∈ᴮ C := inf_le_right.trans inf_le_left
  have hZ : q ≤ Z ∈ᴮ C := inf_le_right.trans (inf_le_right.trans inf_le_left)
  have hne : q ≤ (A =ᴮ Z)ᶜ := inf_le_right.trans (inf_le_right.trans inf_le_right)
  have hqX : q ≤ namedAllRealsValue X := inf_le_left.trans hX
  have hAs := (in_named_subset_bitName_r179 hqX (bSet.mem_of_mem_subset (le_top.trans hC) hA)).1
  have hZs := (in_named_subset_bitName_r179 hqX (bSet.mem_of_mem_subset (le_top.trans hC) hZ)).1
  have hE' : q ≤ imp ((A ∈ᴮ C) ⊓ (Z ∈ᴮ C))
      ((A =ᴮ Z) ⊔ colorValue K (membershipBits A) (membershipBits Z)) :=
    ((le_top : q ≤ ⊤).trans_eq hE.symm).trans ((iInf_le _ A).trans (iInf_le _ Z))
  have hu := _root_.context_imp_elim hE' (le_inf hA hZ)
  have hcol : q ≤ colorValue K (membershipBits A) (membershipBits Z) := by
    apply _root_.context_imp_elim (show q ≤ imp (A =ᴮ Z)ᶜ _ from ?_) hne
    simpa only [_root_.imp,compl_compl] using hu
  exact ((le_inf le_rfl hcol).trans_eq
    (namedOpenEdge_mask_eq_r177 W hAs hZs).symm).trans inf_le_right

end BooleanNames
end JSP000933
