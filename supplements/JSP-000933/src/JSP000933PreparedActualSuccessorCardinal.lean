import JSP000933PreparedSmallerOrdinals

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

theorem ordinalMk_func_eq_r396 (α : Ordinal) (i : (PSet.ordinalMk α).Type) :
    (PSet.ordinalMk α).Func i=PSet.ordinalMk ((cast PSet.ordinalMk_type i).toOrd.val) := by
  have hF : HEq (PSet.ordinalMk α).Func (fun a : α.ToType => PSet.ordinalMk a.toOrd.val) := by
    rw [PSet.ordinalMk_eq_def]
  exact congr_heq hF (cast_heq PSet.ordinalMk_type i).symm

theorem baseCollapse_allMixedPredecessors_smaller_r396 :
    (⊤ : CHBase)≤⨅ a : bSet CHBase,
      (a ∈ᴮ check BaseSuccPSet) ⟹ larger_than (check BaseOmegaOne) a := by
  rw [← bounded_forall (h_congr := B_ext_larger_than_right)]
  apply le_iInf
  intro i
  rw [← deduction,check_bval_top,top_inf_eq,check_func]
  let j : (PSet.ordinalMk GroundContinuumSucc.ord).Type := check_cast i
  let α : GroundContinuumSucc.ord.ToType := cast PSet.ordinalMk_type j
  have he : BaseSuccPSet.Func (check_cast i)=PSet.ordinalMk α.toOrd.val := ordinalMk_func_eq_r396 _ _
  rw [he]
  exact baseCollapse_checkedOrdinal_smaller_r395 _ α.toOrd.property

noncomputable def namedSuccessorCardinal (x y : bSet CHBase) : CHBase :=
  Ord y⊓((larger_than x y)ᶜ⊓⨅ a : bSet CHBase, (a ∈ᴮ y) ⟹ larger_than x a)

theorem baseCollapse_checkedSucc_is_nextCardinal_r396 :
    (⊤ : CHBase)≤namedSuccessorCardinal (check BaseOmegaOne) (check BaseSuccPSet) := by
  apply le_inf
  · exact Ord_card_ex GroundContinuumSucc
  · exact le_inf baseCollapse_omegaOne_notCoversSucc_r394 baseCollapse_allMixedPredecessors_smaller_r396

end PreparedModel
end JSP000933
