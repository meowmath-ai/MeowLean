import JSP000933RealNameExtensionality

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem checkedNat_mem_r174 (i n : ℕ) :
    ((bSet.of_nat i : bSet B) ∈ᴮ bSet.of_nat n) =
      if i < n then (⊤ : B) else ⊥ := by
  by_cases h : i < n
  · rw [ite_eq_left h]
    exact top_unique (bSet.check_mem (PSet.ofNat_mem_of_lt h))
  · rw [ite_eq_right h]
    exact bSet.not_check_mem_iff.mp (fun hm => h (PSet.lt_of_ofNat_mem hm))

theorem checkedNat_eq_bot_r174 {i j : ℕ} (h : i ≠ j) :
    ((bSet.of_nat i : bSet B) =ᴮ bSet.of_nat j) = ⊥ :=
  bSet.check_bv_eq_bot_of_not_equiv (PSet.ofNat_inj h)

theorem memberOmega_cases_r174 (x : bSet B) :
    (x ∈ᴮ (bSet.omega : bSet B)) = ⨆ k : ℕ, x =ᴮ bSet.of_nat k := by
  rw [bSet.mem_unfold]
  change (⨆ k : ULift ℕ, (⊤ : B) ⊓ (x =ᴮ bSet.of_nat k.down)) = _
  simp only [top_inf_eq]
  exact le_antisymm (iSup_le (fun k : ULift ℕ => le_iSup (fun j : ℕ => x =ᴮ bSet.of_nat j) k.down))
    (iSup_le (fun k => le_iSup (fun j : ULift ℕ => x =ᴮ bSet.of_nat j.down) ⟨k⟩))

theorem memberCheckedNat_cases_r174 (n : ℕ) (x : bSet B) :
    (x ∈ᴮ (bSet.of_nat n : bSet B)) = ⨆ k : Fin n, x =ᴮ bSet.of_nat k.val := by
  apply le_antisymm
  · rw [bSet.mem_unfold]
    apply iSup_le
    intro i
    change (bSet.of_nat n : bSet B).bval i ⊓
      (x =ᴮ (bSet.of_nat n : bSet B).func i) ≤ _
    let t := (PSet.ofNat n).Func (bSet.check_cast (x := PSet.ofNat n) i)
    have ht : t ∈ PSet.ofNat n :=
      ⟨bSet.check_cast (x := PSet.ofNat n) i,PSet.Equiv.refl _⟩
    obtain ⟨k,hk⟩ := PSet.ofNat_of_mem_ofNat ht
    have hkLt : k < n := PSet.lt_of_ofNat_mem ((PSet.Mem.congr_left hk).mp ht)
    have hFunc : (bSet.of_nat n : bSet B).func i = bSet.check t := bSet.check_func
    have he : (⊤ : B) ≤ (bSet.of_nat n : bSet B).func i =ᴮ bSet.of_nat k := by
      rw [hFunc]
      exact bSet.check_bv_eq hk
    apply le_iSup_of_le (⟨k,hkLt⟩ : Fin n)
    exact bSet.bv_trans inf_le_right (le_top.trans he)
  · apply iSup_le
    intro i
    have hi : (⊤ : B) ≤ (bSet.of_nat i.val : bSet B) ∈ᴮ bSet.of_nat n :=
      bSet.check_mem (PSet.ofNat_mem_of_lt i.isLt)
    exact bSet.subst_congr_mem_left' (le_rfl.trans_eq bSet.bv_eq_symm) (le_top.trans hi)

theorem checkedNat_subsetOmega_r174 (n : ℕ) :
    (⊤ : B) ≤ (bSet.of_nat n : bSet B) ⊆ᴮ bSet.omega := by
  rw [bSet.subset_unfold']
  apply le_iInf
  intro x
  rw [← _root_.deduction,top_inf_eq,memberCheckedNat_cases_r174]
  apply iSup_le
  intro i
  rw [memberOmega_cases_r174]
  exact le_iSup (fun k : ℕ => x =ᴮ bSet.of_nat k) i.val

theorem checkedNat_forall_r174 (n : ℕ) (F : bSet B → B) (hF : bSet.B_ext F) :
    (⨅ x : bSet B, imp (x ∈ᴮ bSet.of_nat n) (F x)) = ⨅ i : Fin n, F (bSet.of_nat i.val) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    refine (iInf_le _ (bSet.of_nat i.val)).trans_eq ?_
    rw [checkedNat_mem_r174,ite_eq_left i.isLt,_root_.top_imp]
  · apply le_iInf
    intro x
    rw [← _root_.deduction,memberCheckedNat_cases_r174]
    apply Lattice.bv_cases_right
    intro i
    exact (le_inf (inf_le_right.trans_eq bSet.bv_eq_symm)
      (inf_le_left.trans (iInf_le _ i))).trans (hF _ _)

theorem omega_forall_r174 (F : bSet B → B) (hF : bSet.B_ext F) :
    (⨅ x : bSet B, imp (x ∈ᴮ bSet.omega) (F x)) = ⨅ i : ℕ, F (bSet.of_nat i) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    have ho : ((bSet.of_nat i : bSet B) ∈ᴮ bSet.omega) = ⊤ :=
      top_unique bSet.omega_definite
    exact (iInf_le _ (bSet.of_nat i)).trans_eq (by rw [ho,_root_.top_imp])
  · apply le_iInf
    intro x
    rw [← _root_.deduction,memberOmega_cases_r174]
    apply Lattice.bv_cases_right
    intro i
    exact (le_inf (inf_le_right.trans_eq bSet.bv_eq_symm)
      (inf_le_left.trans (iInf_le _ i))).trans (hF _ _)

end BooleanNames
end JSP000933
