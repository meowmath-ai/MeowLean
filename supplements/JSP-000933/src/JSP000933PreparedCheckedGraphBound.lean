import JSP000933PreparedCollapseOrdinalBound

open bSet Cardinal Flypitch
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

noncomputable abbrev BaseSuccPSet : PSet.{0} := PSet.card_ex GroundContinuumSucc

noncomputable def baseSuccIndexEquiv : GroundContinuumSuccIndex ≃ BaseSuccPSet.Type :=
  Equiv.cast (PSet.ordinalMk_type (η := GroundContinuumSucc.ord)).symm

noncomputable def checkedSuccEntry (i : GroundContinuumSuccIndex) : bSet CHBase :=
  check (BaseSuccPSet.Func (baseSuccIndexEquiv i))

theorem checkedSuccEntry_eq_bot_r393 {i j : GroundContinuumSuccIndex} (h : i≠j) :
    ((checkedSuccEntry i =ᴮ checkedSuccEntry j) : CHBase)=⊥ := by
  unfold checkedSuccEntry
  apply check_bv_eq_bot_of_not_equiv
  exact PSet.ordinalMk_inj GroundContinuumSucc.ord _ _ (fun he => h (baseSuccIndexEquiv.injective he))

theorem baseCollapse_checkedGraph_bounded_r393 (x : PSet.{0}) (hx : Cardinal.mk x.Type<GroundContinuumSucc)
    (G : bSet CHBase) (q : CHBase) (hG : q ≤ bSet.is_func G) :
    ∃ β : Ordinal, β<GroundContinuumSucc.ord ∧
      ∀ i : x.Type, ∀ j : GroundContinuumSuccIndex, β≤continuumSuccOrdinal j →
        q⊓(pair (check (x.Func i)) (checkedSuccEntry j) ∈ᴮ G)=⊥ := by
  let v (i : x.Type) (j : GroundContinuumSuccIndex) :=
    (pair (check (x.Func i)) (checkedSuccEntry j) ∈ᴮ G)
  have he (i : x.Type) : Pairwise (fun j k => Disjoint (q⊓v i j) (q⊓v i k)) := by
    intro j k hJK
    apply disjoint_iff_inf_le.mpr
    let r := (q⊓v i j)⊓(q⊓v i k)
    have hR : r≤q := inf_le_left.trans inf_le_left
    have hJ : r≤v i j := inf_le_left.trans inf_le_right
    have hK : r≤v i k := inf_le_right.trans inf_le_right
    have hEq : r≤checkedSuccEntry j =ᴮ checkedSuccEntry k :=
      eq_of_is_func_of_eq (hR.trans hG) bv_refl hJ hK
    exact hEq.trans_eq (checkedSuccEntry_eq_bot_r393 hJK)
  exact baseCollapse_shortArrays_bounded_r392 hx q v he

end PreparedModel
end JSP000933
