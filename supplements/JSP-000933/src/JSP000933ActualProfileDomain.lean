import JSP000933SelectedIsoSymmetricDiff
import JSP000933ReifyCoverClique

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def profileDomainName (D : (ℕ → B) → B) : bSet B :=
  familyName realBitsName D

theorem profileDomainName_mem_bits_r240 (D : (ℕ → B) → B) (hD : RealTestExt D) (x : ℕ → B) :
    (realBitsName x ∈ᴮ profileDomainName D) = D x := by
  unfold profileDomainName
  rw [mem_familyName_r70]
  apply le_antisymm
  · apply iSup_le
    intro y
    rw [realBitsName_eq_r128]
    have h := hD (D y ⊓ realEqValue x y) x y inf_le_right
    exact ((le_inf le_rfl inf_le_left).trans_eq h.symm).trans inf_le_right
  · exact bSet.mem_mk realBitsName D x

theorem profileDomainName_allReals_r240 (D : (ℕ → B) → B) :
    (⊤ : B) ≤ namedAllRealsValue (profileDomainName D) := by
  apply le_iInf
  intro u
  rw [← _root_.deduction,top_inf_eq]
  change u ∈ᴮ familyName realBitsName D ≤ u ⊆ᴮ bSet.omega
  rw [mem_familyName_r70]
  apply iSup_le
  intro x
  exact (le_inf (le_top.trans (realBitsName_subset_r103 x)) inf_le_right).trans bSet.subst_congr_subset_left

theorem profileDomainName_mem_r240 (D : (ℕ → B) → B) (hD : RealTestExt D) (x : bSet B) :
    (x ∈ᴮ profileDomainName D) = (x ⊆ᴮ bSet.omega) ⊓ D (membershipBits x) := by
  let X := profileDomainName D
  let a := realBitsName (membershipBits x)
  have h₀ : (x ∈ᴮ X) ≤ x ⊆ᴮ bSet.omega := by
    have hh : (⊤ : B) ≤ imp (x ∈ᴮ X) (x ⊆ᴮ bSet.omega) :=
      (profileDomainName_allReals_r240 D).trans (iInf_le _ x)
    exact _root_.context_imp_elim (le_top.trans hh) le_rfl
  apply le_antisymm
  · have he : (x ∈ᴮ X) ≤ x =ᴮ a := realBitsName_represents_r103 x h₀
    exact le_inf h₀ ((bSet.subst_congr_mem_left' he le_rfl).trans_eq
      (profileDomainName_mem_bits_r240 D hD (membershipBits x)))
  · have he : ((x ⊆ᴮ bSet.omega) ⊓ D (membershipBits x)) ≤ x =ᴮ a :=
      realBitsName_represents_r103 x inf_le_left
    exact bSet.subst_congr_mem_left' (he.trans_eq bSet.bv_eq_symm)
      (inf_le_right.trans_eq (profileDomainName_mem_bits_r240 D hD (membershipBits x)).symm)

def interleave4 (x : Fin 4 → ℕ → B) (n : ℕ) : B :=
  x ⟨n%4,Nat.mod_lt _ (by decide)⟩ (n/4)

def extract4 (x : ℕ → B) (i : Fin 4) (n : ℕ) : B :=
  x (4*n+i.val)

@[simp] theorem extract4_interleave4_r240 (x : Fin 4 → ℕ → B) (i : Fin 4) :
    extract4 (interleave4 x) i = x i := by
  funext n
  have hm : (4*n+i.val)%4=i.val := by omega
  have hd : (4*n+i.val)/4=n := by omega
  have he : (⟨(4*n+i.val)%4,Nat.mod_lt _ (by decide)⟩ : Fin 4) = i := Fin.ext hm
  unfold extract4 interleave4
  rw [he,hd]

@[simp] theorem interleave4_extract4_r240 (x : ℕ → B) :
    interleave4 (extract4 x) = x := by
  funext n
  unfold interleave4 extract4
  apply congrArg x
  change 4 * (n / 4) + n % 4 = n
  omega

theorem extract4_mask_r240 {p : B} {x y : ℕ → B} (h : p ≤ realEqValue x y) (i : Fin 4) :
    p ≤ realEqValue (extract4 x i) (extract4 y i) :=
  (le_realEqValue_iff_r126 _ _ _).mpr (fun n =>
    (le_realEqValue_iff_r126 _ _ _).mp h (4*n+i.val))

end SetLanguage
end JSP000933
