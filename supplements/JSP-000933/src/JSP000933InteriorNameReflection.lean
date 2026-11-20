import JSP000933OmegaTwoClub
import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

open scoped Cardinal

namespace JSP000933
namespace FiniteSupport

open BooleanCompletion OpenGraphForcing

noncomputable def omegaTwoOrdinal (a : OmegaTwoIndex) : Ordinal :=
  ((Ordinal.ToType.mk (o := (Order.succ (ℵ₁ : Cardinal)).ord)).symm a).1

theorem omegaTwo_countable_bounded_below_r109 (a : OmegaTwoIndex)
    (hcf : (ℵ₀ : Cardinal) < (omegaTwoOrdinal a).cof)
    (S : Set OmegaTwoIndex) (hS : S.Countable) (hBelow : ∀ i ∈ S, i < a) :
    ∃ b < a, ∀ i ∈ S, i < b := by
  let o := (Order.succ (ℵ₁ : Cardinal)).ord
  let t := Ordinal.ToType.mk (o := o)
  let α := (t.symm a).1
  have hα : Order.IsSuccLimit α :=
    Ordinal.one_lt_cof_iff.mp (Ordinal.aleph0_le_cof_iff.mp hcf.le)
  let f (i : S) : Ordinal := (t.symm i.1).1 + 1
  have hCard : Cardinal.mk S < α.cof := (Cardinal.mk_le_aleph0_iff.mpr hS.to_subtype).trans_lt hcf
  have hδ : (⨆ i, f i) < α := Ordinal.iSup_lt_of_lt_cof hCard (fun i =>
    hα.add_one_lt (t.symm.strictMono (hBelow i.1 i.2)))
  have hδo := hδ.trans (t.symm a).2
  let b := t ⟨_,hδo⟩
  have hba : b < a := by
    have h : (⟨_,hδo⟩ : ↥(Set.Iio o)) < t.symm a := hδ
    have ht := t.strictMono h
    rw [t.apply_symm_apply a] at ht
    exact ht
  refine ⟨b,hba,fun i hi => ?_⟩
  have h' : (t.symm i).1 < ⨆ j, f j :=
    ((Order.add_one_le_iff).mp (le_rfl : f ⟨i,hi⟩ ≤ f ⟨i,hi⟩)).trans_le
      (Ordinal.le_iSup f ⟨i,hi⟩)
  have h'' : t.symm i < (⟨_,hδo⟩ : ↥(Set.Iio o)) := h'
  have ht := t.strictMono h''
  rw [t.apply_symm_apply i] at ht
  exact ht

theorem exists_earlierStage_for_countable_values_r109 {N : OmegaTwoIndex → Type}
    {R : Rules N} {I : Type} [Countable I] (a : OmegaTwoIndex)
    (hcf : (ℵ₀ : Cardinal) < (omegaTwoOrdinal a).cof)
    (hCCC : HasCountableAntichains (Before R a)) (g : I → RO (Before R a)) :
    ∃ b : OmegaTwoIndex, ∃ hb : b < a, ∃ old : I → RO (Before R b),
      ∀ n, (prefixReduction (R := R) hb.le).boolPullback (old n) = g n := by
  classical
  have hEach (n : I) :
      ∃ S : Set (Before R a), S.Countable ∧ (⨆ p : S, imageCondition p.1) = g n :=
    exists_countable_basicSupport_r98 (booleanCCC_of_conditionCCC_r66 hCCC) (g n)
  choose S hs hJoin using hEach
  let G : Set (Before R a) := ⋃ n, S n
  have hG : G.Countable := Set.countable_iUnion hs
  letI : Countable (↥G) := hG.to_subtype
  let Coord : Set OmegaTwoIndex := ⋃ p : ↥G, (support p.1.1 : Set OmegaTwoIndex)
  have hc : Coord.Countable := Set.countable_iUnion
    (fun p : ↥G => (support p.1.1).finite_toSet.countable)
  have hCa (i : OmegaTwoIndex) (hi : i ∈ Coord) : i < a := by
    obtain ⟨p,hp⟩ := Set.mem_iUnion.mp hi
    exact p.1.2 i ((mem_support_r75 p.1.1 i).mp hp)
  obtain ⟨b,hba,hb⟩ := omegaTwo_countable_bounded_below_r109 a hcf Coord hc hCa
  let q (n : I) (p : ↥(S n)) : Before R b :=
    ⟨p.1.1,fun i hi => hb i (Set.mem_iUnion.mpr
      ⟨⟨p.1,Set.mem_iUnion.mpr ⟨n,p.2⟩⟩,(mem_support_r75 p.1.1 i).mpr hi⟩)⟩
  refine ⟨b,hba,fun n => ⨆ p : ↥(S n), imageCondition (q n p),fun n => ?_⟩
  rw [(prefixReduction (R := R) hba.le).boolPullback_iSup_r91]
  simp only [prefixReduction_basic_r92]
  apply (show (⨆ p : ↥(S n), imageCondition (includeBefore hba.le (q n p))) =
      (⨆ p : ↥(S n), imageCondition p.1) from ?_).trans (hJoin n)
  apply congrArg (fun f : ↥(S n) → RO (Before R a) => iSup f)
  funext p
  exact congrArg imageCondition (Subtype.ext rfl)

end FiniteSupport
end JSP000933
