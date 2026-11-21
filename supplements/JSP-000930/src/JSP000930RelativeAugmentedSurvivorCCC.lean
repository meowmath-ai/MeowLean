import JSP000930ActualPureNativeCCC
import JSP000930NegativeComposedBaseProjection

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.ForcingTransport JSP000933.MarkedForcing
open JSP000933.RelativeOCA JSP000933.OpenGraphForcing

theorem intrinsic_relativeCCC_of_projected_composition930 {B D N : Type}
    [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra D]
    (F : CompleteValueMap B D) (Q : ValuedPoset D N)
    (hProj : ProjectedAntichainCCC (prefixReduce F ∘ supportProjection Q)) :
    ForcesRelativeCCC Q := by
  apply (relativeCCC_iff_projected Q).mpr
  intro W hW
  let U := unboundedValue (fun i => supportProjection Q (W i))
  let G := prefixReduce F
  have hZero := hProj W hW
  have hU : G U ≤ unboundedValue (fun i => G (supportProjection Q (W i))) := by
    apply le_iInf
    intro b
    have h := (prefixReduce_gc F).monotone_l
      (iInf_le (fun j => aboveValue (fun i => supportProjection Q (W i)) j) b)
    change G U ≤ G (⨆ j : {j : OmegaOneIndex // b<j},supportProjection Q (W j.val)) at h
    exact h.trans_eq ((prefixReduce_gc F).l_iSup
      (f := fun j : {j : OmegaOneIndex // b < j} => supportProjection Q (W j.val)))
  rw [show unboundedValue (fun i => G (supportProjection Q (W i))) = ⊥ from hZero] at hU
  by_contra hn
  exact prefixReduce_nonzero F hn (le_bot_iff.mp hU)

theorem actualAugmented_relativeCCC_of_inner930 {B N M : Type} [NontrivialCompleteBooleanAlgebra B]
    (P : ValuedPoset B N) (Q : ValuedPoset (TotalBA P) M)
    (hP : ForcesRelativeCCC P) (hQ : ForcesRelativeCCC Q) :
    ForcesRelativeCCC (augmentedQ P Q) := by
  let E := (augmentedDenseMap P Q).pullIso
  let T := augmentedQ P Q
  have hPQ : ProjectedAntichainCCC (supportProjection P ∘ supportProjection Q) :=
    projectedAntichainCCC_comp _ _ (supportProjection_gc_r428 P).monotone_l
      (fun _ f => (supportProjection_gc_r428 P).l_iSup)
      ((relativeCCC_iff_projected P).mp hP) ((relativeCCC_iff_projected Q).mp hQ)
  apply (relativeCCC_iff_projected T).mpr
  intro W hW
  have hDisj (i j : OmegaOneIndex) (hij : i<j) : Disjoint (E.symm (W i)) (E.symm (W j)) := by
    apply disjoint_iff_inf_le.mpr
    rw [← E.symm.map_inf,← E.symm.map_bot]
    exact E.symm.monotone (disjoint_iff_inf_le.mp (hW i j hij))
  have h := hPQ (fun i => E.symm (W i)) hDisj
  have hEq (i : OmegaOneIndex) : supportProjection T (W i) =
      supportProjection P (supportProjection Q (E.symm (W i))) :=
    (congrArg (supportProjection T) (E.apply_symm_apply (W i)).symm).trans
      (augmentedDenseMap_support P Q (E.symm (W i)))
  exact (congrArg unboundedValue (funext hEq)).trans h

theorem actualAugmented_innerCCC_of_relative930 {B N M : Type} [NontrivialCompleteBooleanAlgebra B]
    (P : ValuedPoset B N) (Q : ValuedPoset (TotalBA P) M)
    (h : ForcesRelativeCCC (augmentedQ P Q)) :
    ForcesRelativeCCC Q := by
  let E := (augmentedDenseMap P Q).pullIso
  have hComp : ProjectedAntichainCCC (supportProjection P ∘ supportProjection Q) := by
    intro W hW
    have hD (i j : OmegaOneIndex) (hij : i<j) : Disjoint (E (W i)) (E (W j)) := by
      apply disjoint_iff_inf_le.mpr
      rw [← E.map_inf,← E.map_bot]
      exact E.monotone (disjoint_iff_inf_le.mp (hW i j hij))
    have hT := (relativeCCC_iff_projected (augmentedQ P Q)).mp h (fun i => E (W i)) hD
    exact (congrArg unboundedValue (funext fun i => (augmentedDenseMap_support P Q (W i)).symm)).trans hT
  apply intrinsic_relativeCCC_of_projected_composition930 (JSP000930.Positive.totalBaseMap P) Q
  rw [← supportProjection_eq_prefixReduce P (JSP000930.Positive.totalBaseMap P) (fun _ => rfl)]
  exact hComp

end JSP000930.Negative
