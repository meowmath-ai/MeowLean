import JSP000933WholeReduction
import JSP000933SmallRealNames

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

theorem OmegaTwoIndex_countable_bounded_r101 (S : Set OmegaTwoIndex) (hS : S.Countable) :
    ∃ a : OmegaTwoIndex, ∀ i ∈ S, i < a := by
  let o := (Order.succ (ℵ₁ : Cardinal)).ord
  let t := Ordinal.ToType.mk (o := o)
  let f (i : S) : Ordinal := (t.symm i.1).1 + 1
  have hReg : (Order.succ (ℵ₁ : Cardinal)).IsRegular :=
    Cardinal.isRegular_succ Cardinal.isRegular_aleph_one.1
  have hCof : Cardinal.mk S < o.cof := by
    rw [show o.cof = Order.succ (ℵ₁ : Cardinal) from hReg.cof_ord]
    exact ((Cardinal.mk_le_aleph0_iff.mpr hS.to_subtype).trans
      Cardinal.isRegular_aleph_one.1).trans_lt (Order.lt_succ _)
  have hδ : (⨆ i, f i) < o :=
    Ordinal.iSup_lt_of_lt_cof hCof (fun i =>
      (Cardinal.isSuccLimit_ord hReg.1).add_one_lt (t.symm i.1).2)
  refine ⟨t ⟨_,hδ⟩,fun i hi => ?_⟩
  have h' : (t.symm i).1 < ⨆ i, f i :=
    ((Order.add_one_le_iff).mp (le_rfl : f ⟨i,hi⟩ ≤ f ⟨i,hi⟩)).trans_le
      (Ordinal.le_iSup f ⟨i,hi⟩)
  have h'' : t.symm i < (⟨_,hδ⟩ : ↥(Set.Iio o)) := h'
  have ht := t.strictMono h''
  rw [t.apply_symm_apply i] at ht
  exact ht

theorem exists_properStage_for_countable_values_r101 {N : OmegaTwoIndex → Type}
    {R : Rules N} {I : Type} [Countable I]
    (hCCC : HasCountableAntichains (Condition R)) (g : I → RO (Condition R)) :
    ∃ a : OmegaTwoIndex, ∃ old : I → RO (Before R a),
      ∀ n, (wholeReduction a).boolPullback (old n) = g n := by
  classical
  have hEach (n : I) :
      ∃ S : Set (Condition R), S.Countable ∧ (⨆ p : S, imageCondition p.1) = g n :=
    exists_countable_basicSupport_r98 (booleanCCC_of_conditionCCC_r66 hCCC) (g n)
  choose S hs hJoin using hEach
  let G : Set (Condition R) := ⋃ n, S n
  have hG : G.Countable := Set.countable_iUnion hs
  letI : Countable (↥G) := hG.to_subtype
  let Coord : Set OmegaTwoIndex := ⋃ p : ↥G, (support p.1 : Set OmegaTwoIndex)
  have hc : Coord.Countable := Set.countable_iUnion (fun p : ↥G => (support p.1).finite_toSet.countable)
  obtain ⟨a,ha⟩ := OmegaTwoIndex_countable_bounded_r101 Coord hc
  let q (n : I) (p : ↥(S n)) : Before R a :=
    ⟨p.1,fun i hi => ha i (Set.mem_iUnion.mpr
      ⟨⟨p.1,Set.mem_iUnion.mpr ⟨n,p.2⟩⟩,(mem_support_r75 p.1 i).mpr hi⟩)⟩
  refine ⟨a,fun n => ⨆ p : ↥(S n), imageCondition (q n p),fun n => ?_⟩
  rw [(wholeReduction a (R := R)).boolPullback_iSup_r91]
  simp only [wholeReduction_basic_r100]
  exact hJoin n

end FiniteSupport
end JSP000933
