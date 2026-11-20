import JSP000933PreparedActualGraphRangeBound

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

noncomputable def namedAllSmallerGraphsBounded (Y : bSet CHBase) : CHBase :=
  ⨅ X : bSet CHBase, (X∈ᴮ Y) ⟹
    (⨅ G : bSet CHBase, (is_func G) ⟹
      (⨆ d : bSet CHBase, (d∈ᴮ Y)⊓namedRangeBelow X Y G d))

theorem namedRangeBelow_extSource_r398 (Y G d : bSet CHBase) :
    B_ext (fun X => namedRangeBelow X Y G d) := by
  unfold namedRangeBelow
  exact B_ext_iInf (h := fun a => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))

theorem baseCollapse_actualSuccessor_regular_r398 :
    (⊤ : CHBase)≤namedAllSmallerGraphsBounded (check BaseSuccPSet) := by
  let Y : bSet CHBase := check BaseSuccPSet
  have hExt : B_ext (fun X : bSet CHBase => ⨅ G : bSet CHBase, (is_func G) ⟹
      (⨆ d : bSet CHBase, (d∈ᴮ Y)⊓namedRangeBelow X Y G d)) :=
    B_ext_iInf (h := fun G => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun d => B_ext_inf B_ext_const (namedRangeBelow_extSource_r398 Y G d))))
  unfold namedAllSmallerGraphsBounded
  rw [← bounded_forall (h_congr := hExt)]
  apply le_iInf
  intro i
  rw [← deduction,check_bval_top,inf_top_eq,check_func]
  let x := BaseSuccPSet.Func (check_cast i)
  let j := baseSuccIndexEquiv.symm (check_cast i)
  have he : x=PSet.ordinalMk (continuumSuccOrdinal j) := by
    have he := baseSuccFunc_ordinal_r397 j
    have hj : baseSuccIndexEquiv j = check_cast i := baseSuccIndexEquiv.apply_symm_apply _
    rw [hj] at he
    exact he
  have hx : Cardinal.mk x.Type<GroundContinuumSucc := by
    rw [he,PSet.ordinalMk_card]
    exact Cardinal.lt_ord.mp (continuumSuccOrdinal_lt_r392 j)
  apply le_iInf
  intro G
  rw [← deduction,top_inf_eq]
  exact baseCollapse_actualGraphRangeBound_r397 x hx G (is_func G) le_rfl

theorem baseCollapse_actualSuccessor_and_regular_r398 :
    (⊤ : CHBase)≤namedSuccessorCardinal (check BaseOmegaOne) (check BaseSuccPSet)⊓
      namedAllSmallerGraphsBounded (check BaseSuccPSet) :=
  le_inf baseCollapse_checkedSucc_is_nextCardinal_r396 baseCollapse_actualSuccessor_regular_r398

end PreparedModel
end JSP000933
