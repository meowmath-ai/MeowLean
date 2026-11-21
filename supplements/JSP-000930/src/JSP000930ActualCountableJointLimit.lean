import JSP000930ActualAugmentedFiniteSupport

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
open JSP000933.OpenGraphForcing

theorem actualAugmented_countableCofinalCCC (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (hL : CheckedGroundLimit a)
    (g : ℕ → {j : GroundContinuumSuccIndex // j<a})
    (hG : ∀ j<a,∃ n,j≤(g n).val)
    (hCCC : ∀ j<a,ForcesRelativeCCC (actualAugmentedQ j s)) :
    ForcesRelativeCCC (actualAugmentedQ a s) := by
  intro W hW hSep
  let A (n : ℕ) := actualAugmentedIncludeLabel (g n).property.le s
  let T (n : ℕ) (i : OmegaOneIndex) (p : ActualAugmentedLabel (g n).val s) := W i (A n p)
  let V (n : ℕ) (i : OmegaOneIndex) := ⨆ p : ActualAugmentedLabel (g n).val s,T n i p
  have hV (n : ℕ) : unboundedValue (V n) = ⊥ := by
    apply hCCC (g n).val (g n).property (T n)
    · intro i p
      exact (hW i (A n p)).trans_eq (actualAugmented_valid_transport (g n).property.le s p)
    · intro i j hij p q
      have he := hSep i j hij (A n p) (A n q)
      exact le_bot_iff.mp <|
        (inf_le_inf le_rfl (actualAugmented_common_forward (g n).property.le s p q)).trans_eq he
  have hCover (i : OmegaOneIndex) : (⨆ p,W i p) ≤ ⨆ n,V n i := by
    apply iSup_le
    intro p
    obtain ⟨j,hj,q,hq⟩ := actualAugmentedBasis_earlier hL s p
    obtain ⟨n,hn⟩ := hG j hj
    let q' := actualAugmentedIncludeLabel hn s q
    have hEq : A n q' = p :=
      (actualAugmentedIncludeLabel_comp hn (g n).property.le s q).trans hq
    rw [← hEq]
    exact le_iSup_of_le n (le_iSup (T n i) q')
  apply le_bot_iff.mp
  apply (unboundedValue_mono_r431 hCover).trans
  rw [unboundedValue_countablePartition_r433 prepared_boundsOmegaOne_r432]
  exact iSup_le fun n => (hV n).le

theorem actualWetzelJointCCC_countable_limit (a : GroundContinuumSuccIndex)
    (hL : CheckedGroundLimit a)
    (g : ℕ → {j : GroundContinuumSuccIndex // j<a}) (hG : ∀ j<a,∃ n,j≤(g n).val)
    (hPrev : ∀ j<a,ActualWetzelPrefixCCC j) (hJ : ∀ j<a,ActualWetzelJointCCC j) :
    ActualWetzelJointCCC a := by
  intro s hs
  apply actualSurvivorProduct_of_augmentedCCC
  apply actualAugmented_countableCofinalCCC a s hL g hG
  intro j hj
  exact actualAugmentedQ_of_stageCCC j s (hPrev j hj)
    (hJ j hj s (fun r hr => hj.le.trans (hs r hr)))

end JSP000930.Negative
