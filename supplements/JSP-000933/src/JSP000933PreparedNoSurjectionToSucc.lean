import JSP000933PreparedCheckedGraphBound

open bSet Cardinal Flypitch
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

theorem baseCollapse_shortDomain_noSurj_r394 (x : PSet.{0})
    (hx : Cardinal.mk x.Type<GroundContinuumSucc) (S G : bSet CHBase) (q : CHBase)
    (hS : q≤S ⊆ᴮ check x) (hG : q≤ is_func G) (hOnto : q≤ is_surj S (check BaseSuccPSet) G) : q=⊥ := by
  by_contra hq
  obtain ⟨δ,hδ,hBound⟩ := baseCollapse_checkedGraph_bounded_r393 x hx G q hG
  let j := Ordinal.ToType.mk (o := GroundContinuumSucc.ord) ⟨δ,hδ⟩
  have hj : continuumSuccOrdinal j=δ := by unfold continuumSuccOrdinal j; simp
  let y := checkedSuccEntry j
  have hy : q≤y ∈ᴮ (check BaseSuccPSet : bSet CHBase) := by
    apply check_mem
    exact PSet.func_mem BaseSuccPSet (baseSuccIndexEquiv j)
  let φ (z : bSet CHBase) := pair z y ∈ᴮ G
  have hE : B_ext φ := by
    intro z w
    exact subst_congr_mem_left' (pair_congr inf_le_left (bv_refl (x := y))) inf_le_right
  have hA : q≤⨆ w : bSet CHBase, w ∈ᴮ S⊓φ w :=
    (le_inf (hOnto.trans (iInf_le _ y)) hy).trans Lattice.bv_imp_elim
  have hD : q≤⨆ w : bSet CHBase, w ∈ᴮ check x⊓φ w := by
    apply (le_inf le_rfl hA).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro w
    apply le_iSup_of_le w
    exact le_inf (mem_of_mem_subset (inf_le_left.trans hS) (inf_le_right.trans inf_le_left))
      (inf_le_right.trans inf_le_right)
  let i := instantiate_existential_over_check hE x (bot_lt_iff_ne_bot.mpr hq) hD
  have hNot := instantiate_existential_over_check_spec hE x (bot_lt_iff_ne_bot.mpr hq) hD
  have hz : q⊓φ (check (x.Func i))=⊥ := hBound i j hj.ge
  change ⊥<(φ (check (x.Func i)))⊓q at hNot
  rw [inf_comm,hz] at hNot
  exact (lt_irrefl (⊥ : CHBase)) hNot

theorem baseCollapse_checkedShort_notLarger_r394 (x : PSet.{0})
    (hx : Cardinal.mk x.Type<GroundContinuumSucc) :
    larger_than (check x : bSet CHBase) (check BaseSuccPSet)=⊥ := by
  apply le_bot_iff.mp
  unfold larger_than
  apply iSup_le
  intro S
  apply iSup_le
  intro G
  let q := ((S ⊆ᴮ (check x : bSet CHBase))⊓is_func' S (check BaseSuccPSet) G)⊓is_surj S (check BaseSuccPSet) G
  exact (baseCollapse_shortDomain_noSurj_r394 x hx S G q (inf_le_left.trans inf_le_left)
    (inf_le_left.trans (inf_le_right.trans inf_le_left)) inf_le_right).le

theorem baseCollapse_omegaOne_notCoversSucc_r394 :
    ((⊤ : CHBase)≤(larger_than (check BaseOmegaOne : bSet CHBase) (check BaseSuccPSet))ᶜ) := by
  rw [baseCollapse_checkedShort_notLarger_r394 BaseOmegaOne]
  · simp
  · rw [baseOmegaOne_type_card_r391]
    exact Order.lt_succ_iff.mpr Cardinal.aleph_one_le_continuum

end PreparedModel
end JSP000933
