import JSP000933PreparedNoSurjectionToSucc

open bSet Cardinal Flypitch
open scoped Flypitch

namespace JSP000933
namespace PreparedModel

theorem baseGroundReals_psetIndex_inj_r395
    {S T : BaseGroundReals.Type} (h : PSet.Equiv (BaseGroundReals.Func S) (BaseGroundReals.Func T)) :
    S=T := by
  have hE := PSet.equiv_iff.mp h
  apply Set.ext
  intro n
  constructor
  · intro hn
    obtain ⟨m,he⟩ := hE.1 (⟨n,hn⟩ : ↥(show Set (PSet.omega : PSet.{0}).Type from S))
    have hnm : n=m.val := PSet.omega_inj he
    exact hnm.symm ▸ m.property
  · intro hn
    obtain ⟨m,he⟩ := hE.2 (⟨n,hn⟩ : ↥(show Set (PSet.omega : PSet.{0}).Type from T))
    have hnm : n=m.val := PSet.omega_inj he.symm
    exact hnm.symm ▸ m.property

theorem ordinalBelowSucc_injects_groundReals_r395 (α : Ordinal)
    (hα : α<GroundContinuumSucc.ord) :
    PSet.injects_into (PSet.ordinalMk α) BaseGroundReals := by
  let X := PSet.ordinalMk α
  have hC : Cardinal.mk X.Type≤Cardinal.mk BaseGroundReals.Type := by
    rw [baseGroundReals_type_card_r391]
    change Cardinal.mk (PSet.ordinalMk α).Type≤𝔠
    rw [PSet.ordinalMk_card]
    exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hα)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hC
  let f (i : X.Type) := BaseGroundReals.Func (e i)
  have hE (i j : X.Type) (h : PSet.Equiv (X.Func i) (X.Func j)) : PSet.Equiv (f i) (f j) := by
    have he : i=j := by by_contra hn; exact PSet.ordinalMk_inj α i j hn h
    subst j
    exact PSet.Equiv.refl _
  have hI (i j : X.Type) (h : PSet.Equiv (f i) (f j)) : PSet.Equiv (X.Func i) (X.Func j) := by
    have he : i=j := e.injective (baseGroundReals_psetIndex_inj_r395 h)
    subst j
    exact PSet.Equiv.refl _
  exact ⟨PSet.function_mk.mk f hE,
    PSet.function_mk.mk_is_func f (fun i => PSet.func_mem BaseGroundReals (e i)),
    PSet.function_mk.mk_inj_of_inj f hE hI⟩

theorem baseCollapse_checkedOrdinal_smaller_r395 (α : Ordinal) (hα : α<GroundContinuumSucc.ord) :
    (⊤ : CHBase)≤larger_than (check BaseOmegaOne) (check (PSet.ordinalMk α)) := by
  let X : bSet CHBase := check BaseOmegaOne
  let Y : bSet CHBase := check (PSet.ordinalMk α)
  let Z : bSet CHBase := check BaseGroundReals
  let q := (larger_than X Y)ᶜ
  have hY : q≤ injects_into Y Z := check_injects_into (ordinalBelowSucc_injects_groundReals_r395 α hα)
  have hNo : q≤(larger_than X Z)ᶜ := bSet_lt_of_lt_of_le (show q≤(larger_than X Y)ᶜ from le_rfl) hY
  have hYes : q≤larger_than X Z := collapse_algebra.aleph1_larger_than_continuum
  have h0 : q≤⊥ := (le_inf hYes hNo).trans_eq inf_compl_eq_bot'
  have he := compl_le_compl h0
  simpa only [q,compl_bot,compl_compl] using he

end PreparedModel
end JSP000933
