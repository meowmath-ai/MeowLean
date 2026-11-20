import JSP000933PreparedCollapseEmbedding
import JSP000933CheckedOmegaUncountability

open bSet Cardinal Flypitch
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

noncomputable def checkIndexBetween_r413 (B D : Type)
    [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra D] (x : PSet.{0}) :
    (check x : bSet B).type≃(check x : bSet D).type where
  toFun i := check_cast_symm (check_cast i)
  invFun i := check_cast_symm (check_cast i)
  left_inv i := by cases x; rfl
  right_inv i := by cases x; rfl

theorem generic_iSup_equiv_r413 {I J L : Type*} [CompleteLattice L]
    (e : I≃J) (f : J→L) : (⨆ i,f (e i))=⨆ j,f j := by
  apply le_antisymm
  · exact iSup_le (fun i => le_iSup f (e i))
  · apply iSup_le
    intro j
    apply le_iSup_of_le (e.symm j)
    rw [e.apply_symm_apply]

noncomputable def productCollapseArray :
    (check BaseOmegaOne : bSet PreparedBA).type→
      (check BaseGroundReals : bSet PreparedBA).type→PreparedBA :=
  fun i j => embedCollapse (collapse_algebra.π_af
    (checkIndexBetween_r413 PreparedBA CHBase BaseOmegaOne i)
    (checkIndexBetween_r413 PreparedBA CHBase BaseGroundReals j))

theorem productCollapseArray_tall_r413 (i : (check BaseOmegaOne : bSet PreparedBA).type) :
    (⨆ j,productCollapseArray i j)=⊤ := by
  unfold productCollapseArray
  rw [← embedCollapse_joins_r403]
  rw [generic_iSup_equiv_r413 (checkIndexBetween_r413 PreparedBA CHBase BaseGroundReals)]
  rw [collapse_algebra.π_af_tall,embedCollapse_top_r403]

theorem productCollapseArray_wide_r413 (j : (check BaseGroundReals : bSet PreparedBA).type) :
    (⨆ i,productCollapseArray i j)=⊤ := by
  unfold productCollapseArray
  rw [← embedCollapse_joins_r403]
  rw [generic_iSup_equiv_r413 (checkIndexBetween_r413 PreparedBA CHBase BaseOmegaOne)
    (fun i => collapse_algebra.π_af i (checkIndexBetween_r413 PreparedBA CHBase BaseGroundReals j))]
  rw [collapse_algebra.π_af_wide,embedCollapse_top_r403]

theorem productCollapseArray_anti_r413 (i : (check BaseOmegaOne : bSet PreparedBA).type)
    {j k : (check BaseGroundReals : bSet PreparedBA).type} (h : j≠k) :
    productCollapseArray i j⊓productCollapseArray i k≤⊥ := by
  let e := checkIndexBetween_r413 PreparedBA CHBase BaseGroundReals
  have he : e j≠e k := fun h' => h (e.injective h')
  exact disjoint_iff_inf_le.mp (embedCollapse_disjoint_r403
    (disjoint_iff_inf_le.mpr (collapse_algebra.π_af_anti _ _ _ he)))

theorem preparedOmegaOne_pset_inj_r413 (i j : BaseOmegaOne.Type) (h : i≠j) :
    ¬PSet.Equiv (BaseOmegaOne.Func i) (BaseOmegaOne.Func j) :=
  PSet.ordinalMk_inj (Cardinal.aleph 1).ord i j h

theorem productOmegaOne_name_inj_r413 (i j : (check BaseOmegaOne : bSet PreparedBA).type)
    (h : ⊥<((check BaseOmegaOne : bSet PreparedBA).func i =ᴮ
      (check BaseOmegaOne : bSet PreparedBA).func j)) : i=j := by
  by_contra hne
  have hcast : (check_cast i : BaseOmegaOne.Type)≠check_cast j := by
    intro he
    apply hne
    simpa only [check_cast,cast_inj] using he
  rw [check_func,check_func,checkedDistinct_eq_bot_r412 BaseOmegaOne
    preparedOmegaOne_pset_inj_r413 hcast] at h
  exact lt_irrefl _ h

noncomputable def productCollapseEnumeration : bSet PreparedBA :=
  rel_of_array (check BaseOmegaOne) (check BaseGroundReals) productCollapseArray

theorem productCollapseEnumeration_spec_r413 :
    (⊤ : PreparedBA)≤ is_func' (check BaseOmegaOne) (check BaseGroundReals) productCollapseEnumeration⊓
      is_surj (check BaseOmegaOne) (check BaseGroundReals) productCollapseEnumeration :=
  le_inf (rel_of_array_is_func' _ _ _ (fun _ => check_bval_top _) productCollapseArray_tall_r413
    (fun i j k h => productCollapseArray_anti_r413 i h) productOmegaOne_name_inj_r413)
    (rel_of_array_surj _ _ _ (fun _ => check_bval_top _) (fun _ => check_bval_top _)
      productCollapseArray_wide_r413)

theorem prepared_checkedOmegaOne_r413 :
    (⊤ : PreparedBA)≤((check BaseOmegaOne : bSet PreparedBA) =ᴮ (aleph_one (𝔹 := PreparedBA))) := by
  apply aleph_one_check_is_aleph_one_of_omega_lt
  have hNo : (surjects_onto bSet.omega (check BaseOmegaOne) : PreparedBA)=⊥ :=
    countablyClosed_checked_noOmegaSurj_r412 preparedProduct_countablyClosed_r401 BaseOmegaOne
      preparedOmegaOne_pset_inj_r413 (by rw [baseOmegaOne_type_card_r391]; exact PSet.omega_lt_aleph_one)
  apply le_compl_iff_disjoint_left.mpr
  have hS : (larger_than bSet.omega (check BaseOmegaOne) : PreparedBA)≤
      surjects_onto bSet.omega (check BaseOmegaOne) :=
    surjects_onto_of_larger_than_and_exists_mem le_rfl (aleph_one_check_exists_mem)
  rw [hNo] at hS
  rw [le_bot_iff.mp hS]
  exact disjoint_bot_left

end PreparedModel
end JSP000933
