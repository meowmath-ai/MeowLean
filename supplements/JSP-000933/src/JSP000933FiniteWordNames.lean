import JSP000933CheckedNaturals

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def wordBit (w : Word) (i : ℕ) : Bool :=
  if hi : i < w.length then w[i]'hi else false

def wordBits (w : Word) (i : ℕ) : B :=
  truthBit (wordBit w i)

def wordSetName (w : Word) : bSet B :=
  realBitsName (wordBits w)

noncomputable def wordName (w : Word) : bSet B :=
  bSet.pair (bSet.of_nat w.length) (wordSetName w)

noncomputable def wordAgreementValue (m S A : bSet B) : B :=
  ⨅ i : bSet B, imp (i ∈ᴮ m) (bitEq (i ∈ᴮ A) (i ∈ᴮ S))

noncomputable def nameWordCylinderValue (w A : bSet B) : B :=
  ⨆ m : bSet B, ⨆ S : bSet B,
    (m ∈ᴮ bSet.omega) ⊓ ((S ⊆ᴮ m) ⊓ ((w =ᴮ bSet.pair m S) ⊓ wordAgreementValue m S A))

theorem bitEq_truthBit_r175 (x : B) (b : Bool) : bitEq x (truthBit b) = literal x b := by
  cases b <;> simp [bitEq,truthBit,literal]

theorem wordSetName_subset_ord_r175 (w : Word) :
    (⊤ : B) ≤ wordSetName w ⊆ᴮ bSet.of_nat w.length := by
  rw [bSet.subset_unfold]
  change (⊤ : B) ≤ ⨅ i : ULift ℕ, imp (wordBits w i.down)
    ((bSet.of_nat i.down : bSet B) ∈ᴮ bSet.of_nat w.length)
  apply le_iInf
  intro i
  rw [← _root_.deduction,top_inf_eq,checkedNat_mem_r174]
  by_cases hi : i.down < w.length
  · rw [ite_eq_left hi]
    exact le_top
  · rw [ite_eq_right hi]
    simp [wordBits,wordBit,hi,truthBit]

theorem maskedMem_left_r175 {p : B} {i j S : bSet B} (h : p ≤ i =ᴮ j) :
    p ⊓ (i ∈ᴮ S) = p ⊓ (j ∈ᴮ S) := by
  apply le_antisymm
  · exact le_inf inf_le_left (bSet.subst_congr_mem_left' (inf_le_left.trans h) inf_le_right)
  · exact le_inf inf_le_left (bSet.subst_congr_mem_left'
      (inf_le_left.trans (h.trans_eq bSet.bv_eq_symm)) inf_le_right)

theorem wordAgreement_index_ext_r175 (S A : bSet B) :
    bSet.B_ext (fun i => bitEq (i ∈ᴮ A) (i ∈ᴮ S)) := by
  intro i j
  let p := (i =ᴮ j) ⊓ bitEq (i ∈ᴮ A) (i ∈ᴮ S)
  apply (le_bitEq_iff_r126 p _ _).mpr
  have hi := (le_bitEq_iff_r126 p (i ∈ᴮ A) (i ∈ᴮ S)).mp inf_le_right
  exact ((maskedMem_left_r175 (S := A) (show p ≤ i =ᴮ j from inf_le_left)).symm.trans hi).trans
    (maskedMem_left_r175 (S := S) (show p ≤ i =ᴮ j from inf_le_left))

theorem wordAgreement_checked_r175 (n : ℕ) (S A : bSet B) :
    wordAgreementValue (bSet.of_nat n) S A =
      ⨅ i : Fin n, bitEq (membershipBits A i.val) (membershipBits S i.val) :=
  checkedNat_forall_r174 n _ (wordAgreement_index_ext_r175 S A)

theorem wordAgreement_canonical_r175 (w : Word) (A : bSet B) :
    wordAgreementValue (bSet.of_nat w.length) (wordSetName w) A =
      cylinderValue (membershipBits A) w := by
  rw [wordAgreement_checked_r175]
  unfold cylinderValue
  refine congrArg iInf (funext fun i => ?_)
  have he := congrFun (membershipBits_realBitsName_r128 (wordBits w : ℕ → B)) i.val
  change bitEq (membershipBits A i.val) (membershipBits (realBitsName (wordBits w)) i.val) =
    literal (membershipBits A i.val) (w[i.val])
  rw [he]
  simp only [wordBits,wordBit,dite_eq_left i.isLt,bitEq_truthBit_r175]

theorem agreement_transport_ordinal_r175 {p : B} {m n S A : bSet B}
    (hmn : p ≤ m =ᴮ n) (h : p ≤ wordAgreementValue m S A) :
    p ≤ wordAgreementValue n S A := by
  apply le_iInf
  intro i
  rw [← _root_.deduction]
  let q := p ⊓ (i ∈ᴮ n)
  have hMem : q ≤ i ∈ᴮ m := bSet.subst_congr_mem_right'
    (inf_le_left.trans (hmn.trans_eq bSet.bv_eq_symm)) inf_le_right
  exact _root_.context_imp_elim (inf_le_left.trans (h.trans (iInf_le _ i))) hMem

theorem wordNames_separated_r175 {u v : Word} (hne : u ≠ v) :
    ((wordName u : bSet B) =ᴮ wordName v) = ⊥ := by
  apply le_bot_iff.mp
  by_cases hl : u.length = v.length
  · classical
    have hd : ∃ i : ℕ, ∃ hi : i < u.length, ∃ hj : i < v.length, u[i]'hi ≠ v[i]'hj := by
      by_contra hn
      apply hne
      apply List.ext_getElem hl
      intro i hi hj
      by_contra hh
      exact hn ⟨i,hi,hj,hh⟩
    obtain ⟨i,hi,hj,hd⟩ := hd
    let p : B := (wordName u : bSet B) =ᴮ wordName v
    have hEq : p ≤ (wordSetName u : bSet B) =ᴮ wordSetName v := bSet.eq_of_eq_pair_right
    have hh := (le_realEqValue_iff_r126 p _ _).mp (le_realEq_of_nameEq_r128 hEq) i
    have hx : membershipBits (wordSetName u : bSet B) i = truthBit (u[i]'hi) := by
      have he := congrFun (membershipBits_realBitsName_r128 (wordBits u : ℕ → B)) i
      simpa only [wordSetName,wordBits,wordBit,dite_eq_left hi] using he
    have hy : membershipBits (wordSetName v : bSet B) i = truthBit (v[i]'hj) := by
      have he := congrFun (membershipBits_realBitsName_r128 (wordBits v : ℕ → B)) i
      simpa only [wordSetName,wordBits,wordBit,dite_eq_left hj] using he
    rw [hx,hy] at hh
    cases hu : u[i]'hi <;> cases hv : v[i]'hj <;> rw [hu,hv] at hd hh
    · exact False.elim (hd rfl)
    · exact (show p = ⊥ by simpa [truthBit] using hh.symm).le
    · exact (show p = ⊥ by simpa [truthBit] using hh).le
    · exact False.elim (hd rfl)
  · exact bSet.eq_of_eq_pair_left.trans_eq (checkedNat_eq_bot_r174 hl)

end BooleanNames
end JSP000933
