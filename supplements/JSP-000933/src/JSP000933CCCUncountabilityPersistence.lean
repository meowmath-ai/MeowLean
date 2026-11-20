import JSP000933CompleteValueMap
import JSP000933BooleanUncountability

namespace JSP000933
namespace OpenGraphForcing

open BooleanCompletion

variable {B C I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

noncomputable def outsideValue (g : I → B) (S : Set I) : B :=
  ⨅ i : {i : I // i ∉ S}, (g i.1)ᶜ

theorem outsideValue_le_countableCoverage_r95 (g : I → B) (S : Set I) (hS : S.Countable) :
    outsideValue g S ≤ countableCoverageValue g := by
  classical
  obtain ⟨f,hf⟩ := exists_optionEnumeration_r60 S hS
  let e : EnumerationMatrix I B := ⟨fun n i => if f n = some i then ⊤ else ⊥,by
    intro n i j hij
    by_cases hi : f n = some i
    · have hj : f n ≠ some j := fun h => hij (Option.some.inj (hi.symm.trans h))
      simp [hi,hj,hij]
    · simp [hi]⟩
  unfold countableCoverageValue
  apply le_iSup_of_le e
  apply le_iInf
  intro i
  by_cases hi : i ∈ S
  · obtain ⟨n,hn⟩ := (hf i).mp hi
    have hTop : (⊤ : B) ≤ ⨆ n, e.1 n i :=
      le_iSup_of_le n (by simp [e,hn])
    exact le_top.trans (hTop.trans le_sup_right)
  · exact (iInf_le (fun j : {j : I // j ∉ S} => (g j.1)ᶜ) ⟨i,hi⟩).trans le_sup_left

theorem countableCoverageValue_map_le_r95 (F : CompleteValueMap B C) (hCCC : BooleanCCC C)
    (g : I → B) :
    countableCoverageValue (fun i => F.toFun (g i)) ≤ F.toFun (countableCoverageValue g) := by
  apply iSup_le
  intro e
  let S : Set I := ⋃ n : ℕ, {i | e.1 n i ≠ ⊥}
  have hS : S.Countable := Set.countable_iUnion (enumerationRow_support_countable_r68 hCCC e)
  have hb : matrixCoverage (fun i => F.toFun (g i)) e ≤ F.toFun (outsideValue g S) := by
    rw [outsideValue,F.map_iInf]
    apply le_iInf
    intro i
    have hz (n : ℕ) : e.1 n i.1 = ⊥ := by
      by_contra hn
      exact i.2 (Set.mem_iUnion.mpr ⟨n,hn⟩)
    have hh := iInf_le (fun j => (F.toFun (g j))ᶜ ⊔ (⨆ n, e.1 n j)) i.1
    simpa only [matrixCoverage,hz,iSup_const,sup_bot_eq,F.map_compl] using hh
  exact hb.trans (F.monotone (outsideValue_le_countableCoverage_r95 g S hS))

theorem countableCoverageValue_le_map_r95 (F : CompleteValueMap B C) (g : I → B) :
    F.toFun (countableCoverageValue g) ≤ countableCoverageValue (fun i => F.toFun (g i)) := by
  rw [countableCoverageValue,F.map_iSup]
  apply iSup_le
  intro e
  let ee : EnumerationMatrix I C := ⟨fun n i => F.toFun (e.1 n i),by
    intro n i j hij
    apply disjoint_iff_inf_le.mpr
    rw [← F.map_inf]
    exact (F.monotone (disjoint_iff_inf_le.mp (e.2 n i j hij))).trans_eq F.map_bot⟩
  apply le_iSup_of_le ee
  simp only [matrixCoverage,F.map_iInf,F.map_iSup,F.map_sup_r93,F.map_compl,ee]
  exact le_rfl

theorem countableCoverageValue_map_eq_r95 (F : CompleteValueMap B C) (hCCC : BooleanCCC C)
    (g : I → B) :
    F.toFun (countableCoverageValue g) = countableCoverageValue (fun i => F.toFun (g i)) :=
  le_antisymm (countableCoverageValue_le_map_r95 F g) (countableCoverageValue_map_le_r95 F hCCC g)

theorem map_forcing_uncountable_r95 (F : CompleteValueMap B C) (hCCC : BooleanCCC C)
    (g : I → B) {p : B} (hp : p ≤ (countableCoverageValue g)ᶜ) :
    F.toFun p ≤ (countableCoverageValue (fun i => F.toFun (g i)))ᶜ := by
  calc
    F.toFun p ≤ F.toFun ((countableCoverageValue g)ᶜ) := F.monotone hp
    _ = _ := by rw [F.map_compl,countableCoverageValue_map_eq_r95 F hCCC g]

end OpenGraphForcing
end JSP000933
