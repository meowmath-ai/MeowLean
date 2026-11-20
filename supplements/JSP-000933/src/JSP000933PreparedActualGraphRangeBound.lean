import JSP000933PreparedActualSuccessorCardinal

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

theorem prepOrdinalMk_mem_of_lt_r397 {α β : Ordinal} (h : α<β) :
    PSet.ordinalMk α∈PSet.ordinalMk β := by
  let i : β.ToType := Ordinal.ToType.mk ⟨α,h⟩
  let j : (PSet.ordinalMk β).Type := cast (PSet.ordinalMk_type (η := β)).symm i
  have hJ : ((cast (PSet.ordinalMk_type (η := β)) j).toOrd.val)=α := by
    simp [j,i,Ordinal.ToType.toOrd]
  have he := ordinalMk_func_eq_r396 β j
  rw [hJ] at he
  rw [← he]
  exact PSet.func_mem _ j

theorem baseSuccFunc_ordinal_r397 (i : GroundContinuumSuccIndex) :
    BaseSuccPSet.Func (baseSuccIndexEquiv i) = PSet.ordinalMk (continuumSuccOrdinal i) := by
  have he := ordinalMk_func_eq_r396 GroundContinuumSucc.ord (baseSuccIndexEquiv i)
  have hi : cast (PSet.ordinalMk_type (η := GroundContinuumSucc.ord)) (baseSuccIndexEquiv i) = i := by
    change cast (PSet.ordinalMk_type (η := GroundContinuumSucc.ord))
      (cast (PSet.ordinalMk_type (η := GroundContinuumSucc.ord)).symm i) = i
    simp only [cast_cast, cast_eq]
  rw [hi] at he
  exact he

theorem checkedSuccEntry_ordinal_r397 (i : GroundContinuumSuccIndex) :
    checkedSuccEntry i = check (PSet.ordinalMk (continuumSuccOrdinal i)) :=
  congrArg (fun x => (check x : bSet CHBase)) (baseSuccFunc_ordinal_r397 i)

noncomputable def namedRangeBelow (X Y G d : bSet CHBase) : CHBase :=
  ⨅ a : bSet CHBase, (a∈ᴮ X) ⟹
    (⨅ b : bSet CHBase, (b∈ᴮ Y) ⟹ ((pair a b∈ᴮ G) ⟹ b∈ᴮ d))

theorem baseCollapse_actualGraphRangeBound_r397 (x : PSet.{0})
    (hx : Cardinal.mk x.Type<GroundContinuumSucc) (G : bSet CHBase) (q : CHBase)
    (hG : q≤ is_func G) :
    q≤⨆ d : bSet CHBase, d∈ᴮ check BaseSuccPSet⊓namedRangeBelow (check x) (check BaseSuccPSet) G d := by
  obtain ⟨β,hβ,hBound⟩ := baseCollapse_checkedGraph_bounded_r393 x hx G q hG
  let d : bSet CHBase := check (PSet.ordinalMk β)
  have hd : q≤d ∈ᴮ check BaseSuccPSet := check_mem (prepOrdinalMk_mem_of_lt_r397 hβ)
  refine le_iSup_of_le d (le_inf hd ?_)
  unfold namedRangeBelow
  have hA : B_ext (fun a : bSet CHBase => ⨅ b : bSet CHBase,
      (b∈ᴮ check BaseSuccPSet) ⟹ ((pair a b∈ᴮ G) ⟹ b∈ᴮ d)) :=
    B_ext_iInf (h := fun b => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_imp (h₁ := B_ext_pair_mem_left) (h₂ := B_ext_const)))
  rw [← bounded_forall (h_congr := hA)]
  apply le_iInf
  intro i
  rw [← deduction,check_bval_top,inf_top_eq,check_func]
  let a : bSet CHBase := check (x.Func (check_cast i))
  have hB : B_ext (fun b : bSet CHBase => (pair a b∈ᴮ G) ⟹ b∈ᴮ d) :=
    B_ext_imp (h₁ := B_ext_pair_mem_right) (h₂ := B_ext_mem_left)
  change q≤⨅ b : bSet CHBase, (b∈ᴮ check BaseSuccPSet) ⟹ ((pair a b∈ᴮ G) ⟹ b∈ᴮ d)
  rw [← bounded_forall (h_congr := hB)]
  apply le_iInf
  intro j
  rw [← deduction,check_bval_top,inf_top_eq,check_func,← deduction]
  let z := baseSuccIndexEquiv.symm (check_cast j)
  have hz : checkedSuccEntry z=check (BaseSuccPSet.Func (check_cast j)) := by
    simp [checkedSuccEntry,z]
  rw [←hz]
  by_cases hb : continuumSuccOrdinal z<β
  · rw [checkedSuccEntry_ordinal_r397]
    exact check_mem (prepOrdinalMk_mem_of_lt_r397 hb)
  · have h := hBound (check_cast i) z (le_of_not_gt hb)
    rw [show q⊓(pair a (checkedSuccEntry z)∈ᴮ G)=⊥ from h]
    exact bot_le

end PreparedModel
end JSP000933
