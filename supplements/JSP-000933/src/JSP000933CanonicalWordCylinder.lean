import JSP000933FiniteWordNames
import JSP000933FiniteOpenRectangleWitnesses

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem le_of_dense_refinement_r176 (a b : B)
    (h : ∀ p : B, p ≠ ⊥ → p ≤ a → ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ≤ b) : a ≤ b := by
  classical
  by_contra hn
  let p := a ⊓ bᶜ
  have hp : p ≠ ⊥ := by
    intro hz
    have hd : Disjoint a bᶜ := disjoint_iff_inf_le.mpr hz.le
    exact hn (by simpa only [compl_compl] using (le_compl_iff_disjoint_right.mpr hd))
  obtain ⟨q,hq,hqp,hqb⟩ := h p hp inf_le_left
  exact hq (le_bot_iff.mp ((le_inf hqb (hqp.trans inf_le_right)).trans_eq (inf_compl_eq_bot' (x := b))))

theorem agreement_transport_set_r176 {p : B} {m S T A : bSet B}
    (he : p ≤ S =ᴮ T) (h : p ≤ wordAgreementValue m S A) :
    p ≤ wordAgreementValue m T A := by
  apply le_iInf
  intro i
  rw [← _root_.deduction]
  let q := p ⊓ (i ∈ᴮ m)
  apply (le_bitEq_iff_r126 q _ _).mpr
  have hFirst : q ≤ bitEq (i ∈ᴮ A) (i ∈ᴮ S) :=
    _root_.context_imp_elim (inf_le_left.trans (h.trans (iInf_le _ i))) inf_le_right
  have hMask : q ⊓ (i ∈ᴮ S) = q ⊓ (i ∈ᴮ T) := by
    apply le_antisymm
    · exact le_inf inf_le_left (bSet.subst_congr_mem_right'
        (inf_le_left.trans (inf_le_left.trans he)) inf_le_right)
    · exact le_inf inf_le_left (bSet.subst_congr_mem_right'
        (inf_le_left.trans (inf_le_left.trans (he.trans_eq bSet.bv_eq_symm))) inf_le_right)
  exact ((le_bitEq_iff_r126 q _ _).mp hFirst).trans hMask

theorem decide_wordSetName_r176 (S : bSet B) (n : ℕ) (p : B) (hp : p ≠ ⊥)
    (hS : p ≤ S ⊆ᴮ bSet.of_nat n) :
    ∃ u : Word, u.length = n ∧ ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ≤ S =ᴮ wordSetName u := by
  obtain ⟨u,hu,q,hq,hqp,hW⟩ := exists_decided_initialWord_r136 (membershipBits S) n p hp
  refine ⟨u,hu,q,hq,hqp,?_⟩
  have hSub : q ≤ S ⊆ᴮ bSet.of_nat u.length := hu.symm ▸ (hqp.trans hS)
  have hSubω : q ≤ S ⊆ᴮ bSet.omega :=
    bSet.subset_trans' hSub (le_top.trans (checkedNat_subsetOmega_r174 u.length))
  apply le_nameEq_of_realEq_for_subsets_r128 hSubω (le_top.trans (realBitsName_subset_r103 _))
  apply (le_realEqValue_iff_r126 q _ _).mpr
  intro i
  have hw := congrFun (membershipBits_realBitsName_r128 (wordBits u : ℕ → B)) i
  change q ⊓ membershipBits S i = q ⊓ membershipBits (realBitsName (wordBits u)) i
  rw [hw]
  by_cases hi : i < u.length
  · have hLit := hW.trans (iInf_le _ (⟨i,hi⟩ : Fin u.length))
    apply (le_bitEq_iff_r126 q _ _).mp
    simpa only [wordBits,wordBit,dite_eq_left hi,bitEq_truthBit_r175] using hLit
  · have hMem : q ⊓ membershipBits S i ≤ (bSet.of_nat i : bSet B) ∈ᴮ bSet.of_nat u.length :=
      bSet.mem_of_mem_subset (inf_le_left.trans hSub) inf_le_right
    rw [checkedNat_mem_r174,ite_eq_right hi] at hMem
    have hz := le_bot_iff.mp hMem
    simpa [wordBits,wordBit,hi,truthBit] using hz

theorem nameWordCylinder_eq_coded_r176 (w A : bSet B) :
    nameWordCylinderValue w A =
      ⨆ u : Word, (w =ᴮ wordName u) ⊓ cylinderValue (membershipBits A) u := by
  apply le_antisymm
  · unfold nameWordCylinderValue
    apply iSup_le
    intro m
    apply iSup_le
    intro S
    apply le_of_dense_refinement_r176
    intro p hp hP
    have hM : p ≤ ⨆ n : ℕ, m =ᴮ bSet.of_nat n := by
      exact (hP.trans inf_le_left).trans_eq (memberOmega_cases_r174 m)
    obtain ⟨n,q,hq,hqp,hEq⟩ := exists_nonzero_below_choice_r135 p hp
      (fun n : ℕ => m =ᴮ bSet.of_nat n) hM
    have hS : q ≤ S ⊆ᴮ bSet.of_nat n :=
      (le_inf (hqp.trans (hP.trans (inf_le_right.trans inf_le_left))) hEq).trans
        bSet.subst_congr_subset_right
    obtain ⟨u,hu,r,hr,hrq,hEqS⟩ := decide_wordSetName_r176 S n q hq hS
    have hEqM : r ≤ m =ᴮ bSet.of_nat u.length := hu.symm ▸ (hrq.trans hEq)
    have hrp := hrq.trans hqp
    have hPair : r ≤ w =ᴮ wordName u :=
      bSet.bv_trans (hrp.trans (hP.trans (inf_le_right.trans (inf_le_right.trans inf_le_left))))
        (bSet.pair_congr hEqM hEqS)
    have hAgr := agreement_transport_set_r176 hEqS
      (agreement_transport_ordinal_r175 hEqM
        (hrp.trans (hP.trans (inf_le_right.trans (inf_le_right.trans inf_le_right)))))
    refine ⟨r,hr,hrp,le_iSup_of_le u (le_inf hPair ?_)⟩
    exact hAgr.trans_eq (wordAgreement_canonical_r175 u A)
  · apply iSup_le
    intro u
    apply le_iSup_of_le (bSet.of_nat u.length)
    apply le_iSup_of_le (wordSetName u)
    exact le_inf bSet.omega_definite (le_inf (le_top.trans (wordSetName_subset_ord_r175 u))
      (le_inf inf_le_left (inf_le_right.trans_eq (wordAgreement_canonical_r175 u A).symm)))

end BooleanNames
end JSP000933
