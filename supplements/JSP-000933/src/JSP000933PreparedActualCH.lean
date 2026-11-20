import JSP000933PreparedCollapseEnumeration
import JSP000933GroundSubsetNames

open bSet Cardinal Fol Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanNames PositiveForcing

noncomputable def groundRealPSet (a : Set ℕ) : PSet.{0} :=
  PSet.mk {i : ULift ℕ // i.down∈a} (fun i => PSet.omega.Func i.val)

theorem groundRealPSet_subset_r414 (a : Set ℕ) : groundRealPSet a⊆PSet.omega := by
  intro i
  exact ⟨i.val,PSet.Equiv.refl _⟩

theorem groundRealPSet_check_mem_r414 {B : Type} [NontrivialCompleteBooleanAlgebra B]
    (a : Set ℕ) (x : bSet B) :
    (x∈ᴮ groundSubsetName B a)=(x∈ᴮ check (groundRealPSet a)) := by
  classical
  rw [groundSubsetName,realBitsName,mem_familyName_r70,check_unfold,mem_unfold]
  change (⨆ i : ULift ℕ,groundSubsetBits B a i.down⊓
      (x=ᴮ check (PSet.omega.Func i)))=
    ⨆ i : {i : ULift ℕ // i.down∈a},(⊤ : B)⊓(x=ᴮ check (PSet.omega.Func i.val))
  apply le_antisymm
  · apply iSup_le
    intro i
    by_cases hi : i.down∈a
    · apply le_iSup_of_le ⟨i,hi⟩
      simp only [groundSubsetBits,ite_eq_left hi,le_rfl]
    · simp only [groundSubsetBits,ite_eq_right hi,bot_inf_eq,bot_le]
  · apply iSup_le
    intro i
    apply le_iSup_of_le i.val
    simp only [groundSubsetBits,ite_eq_left i.property,le_rfl]

theorem groundRealPSet_check_eq_r414 {B : Type} [NontrivialCompleteBooleanAlgebra B] (a : Set ℕ) :
    (⊤ : B)≤groundSubsetName B a =ᴮ check (groundRealPSet a) := by
  rw [eq_iff_subset_subset,subset_unfold',subset_unfold']
  apply le_inf
  · apply le_iInf
    intro u
    rw [← _root_.deduction,top_inf_eq,groundRealPSet_check_mem_r414]
  · apply le_iInf
    intro u
    rw [← _root_.deduction,top_inf_eq,groundRealPSet_check_mem_r414]

theorem prepared_powerset_subset_checked_r414 :
    (⊤ : PreparedBA)≤(bv_powerset (bSet.omega : bSet PreparedBA))⊆ᴮ check BaseGroundReals := by
  rw [subset_unfold']
  apply le_iInf
  intro x
  rw [← _root_.deduction,top_inf_eq]
  have hx : (x∈ᴮ bv_powerset bSet.omega)≤x⊆ᴮ bSet.omega := bSet.bv_powerset_spec.mpr le_rfl
  apply (hx.trans (omegaSubset_le_iSup_ground_r186 preparedProduct_countablyClosed_r401 x)).trans
  apply iSup_le
  intro a
  let y : bSet PreparedBA := check (groundRealPSet a)
  have hY : (⊤ : PreparedBA)≤y∈ᴮ (check BaseGroundReals : bSet PreparedBA) :=
    check_mem (PSet.mem_powerset.mpr (groundRealPSet_subset_r414 a))
  exact subst_congr_mem_left'
    ((bv_trans le_rfl (le_top.trans (groundRealPSet_check_eq_r414 a))).trans_eq bv_eq_symm) (le_top.trans hY)

theorem prepared_actualPowerset_r414 :
    (⊤ : PreparedBA)≤(check BaseGroundReals : bSet PreparedBA)=ᴮ bv_powerset bSet.omega := by
  rw [eq_iff_subset_subset]
  exact le_inf (check_powerset_subset_powerset PSet.omega) prepared_powerset_subset_checked_r414

theorem prepared_omegaOne_covers_checkedReals_r414 :
    (⊤ : PreparedBA)≤larger_than (check BaseOmegaOne : bSet PreparedBA) (check BaseGroundReals) := by
  apply bv_use (check BaseOmegaOne)
  apply bv_use productCollapseEnumeration
  rw [inf_assoc]
  exact le_inf subset_self productCollapseEnumeration_spec_r413

theorem prepared_top_CH_r414 : (⊤ : PreparedBA) ⊩[V PreparedBA] CH_f := by
  rw [CH_f_sound]
  apply CH_iff_CH₂.mp
  apply CH_true_aux
  · intro Γ
    apply bv_rw' (le_top.trans prepared_checkedOmegaOne_r413)
    · exact B_ext_le_of_omega_lt
    · exact aleph_one_le_of_omega_lt
  · intro Γ
    simp only [compl_compl]
    rw [← compl_compl (larger_than (check BaseOmegaOne) (bv_powerset bSet.omega)),
      ← imp_bot,← _root_.deduction]
    apply bv_absurd (larger_than (check BaseOmegaOne) (check BaseGroundReals))
    · exact le_top.trans prepared_omegaOne_covers_checkedReals_r414
    · exact inf_le_right.trans (bSet_lt_of_lt_of_le le_rfl
        (le_top.trans (injects_into_of_subset prepared_powerset_subset_checked_r414)))

end PreparedModel
end JSP000933
