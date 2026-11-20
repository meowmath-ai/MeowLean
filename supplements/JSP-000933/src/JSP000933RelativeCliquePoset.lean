import JSP000933RelativeCCCProjection
import JSP000933CliqueLabelValidity

namespace JSP000933
namespace RelativeOCA

open MarkedForcing CantorCodes

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]

open scoped Classical in
noncomputable def relativeCliquePoset (mark : B) (D : I→B) (K : I→I→B) :
    ValuedPoset B (Finset I) where
  valid := cliqueAdmitted mark D K
  refines s t := if t⊆s then cliqueAdmitted mark D K s else ⊥
  refine_valid s t := by
    by_cases h : t⊆s
    · simp only [ite_eq_left h]
      exact le_inf le_rfl (cliqueAdmitted_anti_r121 mark D K h)
    · simp only [ite_eq_right h,bot_le]
  refl s := by rw [ite_eq_left (show s⊆s from fun _ h => h)]
  trans s t u := by
    by_cases hst : t⊆s
    · by_cases htu : u⊆t
      · rw [ite_eq_left hst,ite_eq_left htu,ite_eq_left (htu.trans hst)]
        exact inf_le_left
      · simp only [ite_eq_right htu,inf_bot_eq,bot_le]
    · simp only [ite_eq_right hst,bot_inf_eq,bot_le]
  weakest := ∅
  weakest_valid := cliqueAdmitted_empty_r121 mark D K
  weaker s := by simp only [Finset.empty_subset,ite_true,le_rfl]

theorem relativeClique_common_r437 (mark : B) (D : I→B) (K : I→I→B) (s t : Finset I) :
    commonRefinementValue (relativeCliquePoset mark D K) s t=cliqueAdmitted mark D K (s∪t) := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro r
    change ((if s⊆r then cliqueAdmitted mark D K r else ⊥)⊓
      (if t⊆r then cliqueAdmitted mark D K r else ⊥))≤_
    by_cases hs : s⊆r
    · by_cases ht : t⊆r
      · simp only [ite_eq_left hs,ite_eq_left ht,inf_idem]
        exact cliqueAdmitted_anti_r121 mark D K (Finset.union_subset hs ht)
      · simp only [ite_eq_right ht,inf_bot_eq,bot_le]
    · simp only [ite_eq_right hs,bot_inf_eq,bot_le]
  · apply le_iSup_of_le (s∪t)
    change _≤(if s⊆s∪t then cliqueAdmitted mark D K (s∪t) else ⊥)⊓
      (if t⊆s∪t then cliqueAdmitted mark D K (s∪t) else ⊥)
    simp only [ite_eq_left Finset.subset_union_left,ite_eq_left Finset.subset_union_right,inf_idem,le_rfl]

noncomputable def genericVertexValue (mark : B) (D : I→B) (K : I→I→B) (i : I) :
    TotalBA (relativeCliquePoset mark D K) :=
  traceValue (relativeCliquePoset mark D K) {i}

theorem genericVertex_support_r437 (mark : B) (D : I→B) (K : I→I→B) (i : I) :
    supportProjection (relativeCliquePoset mark D K) (genericVertexValue mark D K i)=mark⊓D i := by
  rw [genericVertexValue,traceValue_support_r429]
  exact cliqueAdmitted_singleton_r121 mark D K i

theorem genericVertex_edge_r437 (mark : B) (D : I→B) (K : I→I→B) {i j : I} (hne : i≠j) :
    genericVertexValue mark D K i⊓genericVertexValue mark D K j≤
      baseEmbed (relativeCliquePoset mark D K) (K i j) := by
  apply (supportProjection_le_iff_r428 _ _ _).mp
  unfold genericVertexValue
  rw [traceValue_pair_support_r430,relativeClique_common_r437]
  exact cliqueAdmitted_le_edge_r121 mark D K
    (Finset.mem_union.mpr (Or.inl (Finset.mem_singleton_self i)))
    (Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self j))) hne

end RelativeOCA
end JSP000933
