import JSP000933PreparedCheckedOrdinalRange
import JSP000933PreparedActualCH

open bSet Cardinal Flypitch Lattice
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

open BooleanCompletion

theorem prepared_shortDomain_noSurj_r417 (x : PSet.{0})
    (hx : Cardinal.mk x.Type<GroundContinuumSucc) (S G : bSet PreparedBA) (m : PreparedBA)
    (hS : m≤S⊆ᴮ check x) (hG : m≤ is_func G)
    (hOnto : m≤ is_surj S (check BaseSuccPSet) G) : m=⊥ := by
  by_contra hm
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hm
  obtain ⟨s,β,hs,hV⟩ := prepared_partialProfiles_bounded_r415 hx
    (preparedGraphValues x G) (is_func G) (preparedGraphValues_disjoint_r416 x G)
    p.1 p.2 (hp.trans hG)
  let q : PreparedCondition := (p.1,s)
  let c := imageCondition q
  have hc : c≤ m := (imageCondition_mono_r50 (show q≤p from ⟨le_rfl,hs⟩)).trans hp
  let y : bSet PreparedBA := preparedOrdinalEntry β
  have hy : c≤y∈ᴮ (check BaseSuccPSet : bSet PreparedBA) :=
    check_mem (PSet.func_mem BaseSuccPSet (baseSuccIndexEquiv β))
  let φ (z : bSet PreparedBA) := pair z y∈ᴮ G
  have hE : B_ext φ := B_ext_pair_mem_left
  have hA : c≤⨆ w : bSet PreparedBA,w∈ᴮ S⊓φ w :=
    (le_inf ((hc.trans hOnto).trans (iInf_le _ y)) hy).trans Lattice.bv_imp_elim
  have hD : c≤⨆ w : bSet PreparedBA,w∈ᴮ check x⊓φ w := by
    apply (le_inf le_rfl hA).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro w
    apply le_iSup_of_le w
    exact le_inf (mem_of_mem_subset (inf_le_left.trans (hc.trans hS))
      (inf_le_right.trans inf_le_left)) (inf_le_right.trans inf_le_right)
  rw [← bounded_exists (h_congr := hE)] at hD
  have hz : c≤⊥ := by
    apply (le_inf le_rfl hD).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro i
    simp only [check_bval_top,top_inf_eq,check_func]
    change c⊓preparedGraphValues x G (check_cast i) β≤⊥
    exact (hV (check_cast i) β le_rfl).le
  exact imageCondition_ne_bot_r50 q (le_bot_iff.mp hz)

theorem prepared_checkedShort_notLarger_r417 (x : PSet.{0})
    (hx : Cardinal.mk x.Type<GroundContinuumSucc) :
    (larger_than (check x : bSet PreparedBA) (check BaseSuccPSet))=⊥ := by
  apply le_bot_iff.mp
  unfold larger_than
  apply iSup_le
  intro S
  apply iSup_le
  intro G
  let c := ((S⊆ᴮ (check x : bSet PreparedBA))⊓is_func' S (check BaseSuccPSet) G)⊓
    is_surj S (check BaseSuccPSet) G
  exact (prepared_shortDomain_noSurj_r417 x hx S G c (inf_le_left.trans inf_le_left)
    (inf_le_left.trans (inf_le_right.trans inf_le_left)) inf_le_right).le

theorem prepared_omegaOne_notCoversSucc_r417 :
    (⊤ : PreparedBA)≤(larger_than (check BaseOmegaOne : bSet PreparedBA) (check BaseSuccPSet))ᶜ := by
  have hCard : Cardinal.mk BaseOmegaOne.Type<GroundContinuumSucc := by
    rw [baseOmegaOne_type_card_r391]
    exact Cardinal.aleph_one_le_continuum.trans_lt (Order.lt_succ _)
  rw [prepared_checkedShort_notLarger_r417 BaseOmegaOne hCard,compl_bot]

theorem prepared_checkedPredecessor_smaller_r417 (α : Ordinal) (hα : α<GroundContinuumSucc.ord) :
    (⊤ : PreparedBA)≤larger_than (check BaseOmegaOne) (check (PSet.ordinalMk α)) := by
  let X : bSet PreparedBA := check BaseOmegaOne
  let Y : bSet PreparedBA := check (PSet.ordinalMk α)
  let Z : bSet PreparedBA := check BaseGroundReals
  let c := (larger_than X Y)ᶜ
  have hY : c≤ injects_into Y Z := check_injects_into (ordinalBelowSucc_injects_groundReals_r395 α hα)
  have hN : c≤(larger_than X Z)ᶜ := bSet_lt_of_lt_of_le (show c≤(larger_than X Y)ᶜ from le_rfl) hY
  have hP : c≤larger_than X Z := le_top.trans prepared_omegaOne_covers_checkedReals_r414
  have h0 : c≤⊥ := (le_inf hP hN).trans_eq inf_compl_eq_bot'
  simpa only [c,compl_bot,compl_compl] using compl_le_compl h0

theorem prepared_actualSuccessorCardinal_r417 :
    (⊤ : PreparedBA)≤Ord (check BaseSuccPSet)⊓
      ((larger_than (check BaseOmegaOne) (check BaseSuccPSet))ᶜ⊓
        ⨅ d : bSet PreparedBA,(d∈ᴮ check BaseSuccPSet)⟹larger_than (check BaseOmegaOne) d) := by
  refine le_inf (Ord_card_ex GroundContinuumSucc) (le_inf prepared_omegaOne_notCoversSucc_r417 ?_)
  rw [← bounded_forall (h_congr := B_ext_larger_than_right)]
  apply le_iInf
  intro i
  rw [← deduction,check_bval_top,top_inf_eq,check_func]
  let j : (PSet.ordinalMk GroundContinuumSucc.ord).Type := check_cast i
  let α : GroundContinuumSucc.ord.ToType := cast PSet.ordinalMk_type j
  rw [show BaseSuccPSet.Func (check_cast i)=PSet.ordinalMk α.toOrd.val from ordinalMk_func_eq_r396 _ _]
  exact prepared_checkedPredecessor_smaller_r417 _ α.toOrd.property

theorem prepared_actualSuccessor_regular_r417 :
    (⊤ : PreparedBA)≤⨅ X : bSet PreparedBA,(X∈ᴮ check BaseSuccPSet)⟹
      (⨅ G : bSet PreparedBA,(is_func G)⟹
        (⨆ d : bSet PreparedBA,(d∈ᴮ check BaseSuccPSet)⊓
          preparedRangeBelow X (check BaseSuccPSet) G d)) := by
  let Y : bSet PreparedBA := check BaseSuccPSet
  have hExt : B_ext (fun X : bSet PreparedBA => ⨅ G : bSet PreparedBA,(is_func G)⟹
      (⨆ d : bSet PreparedBA,(d∈ᴮ Y)⊓preparedRangeBelow X Y G d)) :=
    B_ext_iInf (h := fun G => B_ext_imp (h₁ := B_ext_const)
      (h₂ := B_ext_iSup (h := fun d => B_ext_inf B_ext_const
        (B_ext_iInf (h := fun a => B_ext_imp (h₁ := B_ext_mem_right) (h₂ := B_ext_const))))))
  rw [← bounded_forall (h_congr := hExt)]
  apply le_iInf
  intro i
  rw [← deduction,check_bval_top,top_inf_eq,check_func]
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
  exact prepared_checkedShort_graphRange_r416 x hx G

end PreparedModel
end JSP000933
