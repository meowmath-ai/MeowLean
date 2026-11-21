import JSP000933CompleteValueMap
import JSP000933ProjectedSuccessorCCC

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.RelativeOCA

variable {A D : Type} [CompleteBooleanAlgebra A] [CompleteBooleanAlgebra D]

noncomputable def prefixReduce (F : CompleteValueMap A D) (x : D) : A :=
  ⨅ a : {a : A // x ≤ F.toFun a},a.val

theorem prefixReduce_le_iff (F : CompleteValueMap A D) (x : D) (a : A) :
    prefixReduce F x ≤ a ↔ x ≤ F.toFun a := by
  have hX : x ≤ F.toFun (prefixReduce F x) := by
    unfold prefixReduce
    rw [F.map_iInf]
    exact le_iInf fun t => t.property
  exact ⟨fun h => hX.trans (F.monotone h),fun h => iInf_le (fun t : {t : A // x ≤ F.toFun t} => t.val) ⟨a,h⟩⟩

theorem prefixReduce_gc (F : CompleteValueMap A D) :
    GaloisConnection (prefixReduce F) F.toFun :=
  prefixReduce_le_iff F

theorem prefixReduce_nonzero (F : CompleteValueMap A D) {x : D} (hx : x ≠ ⊥) :
    prefixReduce F x ≠ ⊥ := by
  intro h
  have he := (prefixReduce_le_iff F x ⊥).1 h.le
  rw [F.map_bot] at he
  exact hx (le_bot_iff.mp he)

theorem prefixReduce_image (F : CompleteValueMap A D) (a : A) :
    prefixReduce F (F.toFun a) = a := by
  apply le_antisymm ((prefixReduce_le_iff F _ _).2 le_rfl)
  exact F.reflect_le_r93 ((prefixReduce_le_iff F _ _).1 le_rfl)

theorem prefixReduce_meet_ne_bot (F : CompleteValueMap A D) {x : D} {a : A}
    (ha : a ≠ ⊥) (hle : a ≤ prefixReduce F x) :
    x ⊓ F.toFun a ≠ ⊥ := by
  intro hf
  have hb : x ≤ (F.toFun a)ᶜ :=
    le_compl_iff_disjoint_right.mpr (disjoint_iff_inf_le.mpr hf.le)
  rw [← F.map_compl] at hb
  have h := hle.trans ((prefixReduce_le_iff F _ _).2 hb)
  exact ha (disjoint_compl_right.out _ le_rfl h)

theorem exists_basic_prefix_reduction (F : CompleteValueMap A D)
    {J : Type} (basic : J → A)
    (hDense : ∀ a,a ≠ ⊥ → ∃ j,basic j ≠ ⊥ ∧ basic j ≤ a)
    {x : D} (hx : x ≠ ⊥) :
    ∃ j,basic j ≠ ⊥ ∧ basic j ≤ prefixReduce F x ∧
      ∀ a,a ≠ ⊥ → a ≤ basic j → x ⊓ F.toFun a ≠ ⊥ := by
  obtain ⟨j,hj,hb⟩ := hDense _ (prefixReduce_nonzero F hx)
  exact ⟨j,hj,hb,fun a ha h => prefixReduce_meet_ne_bot F ha (h.trans hb)⟩

end JSP000930.Negative
