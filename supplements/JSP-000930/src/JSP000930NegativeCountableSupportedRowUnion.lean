import JSP000930NegativeActualPointedR121Product

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B N : Type} [CompleteBooleanAlgebra B]

theorem relativeCCC_of_countable_supported_union
    (hB : BoundsCountableOmegaOneNames B)
    {T : ℕ → Type} (Q : ValuedPoset B N) (P : ∀ n,ValuedPoset B (T n))
    (inc : ∀ n,T n → N)
    (hValid : ∀ n a,Q.valid (inc n a) = (P n).valid a)
    (hRef : ∀ n a b,(P n).refines a b ≤ Q.refines (inc n a) (inc n b))
    (hCover : ∀ p : N,∃ n a,inc n a = p)
    (hCCC : ∀ n,ForcesRelativeCCC (P n)) :
    ForcesRelativeCCC Q := by
  intro W hW hSep
  let V (n : ℕ) (i : OmegaOneIndex) (p : T n) := W i (inc n p)
  have hOldSep (n : ℕ) (i j : OmegaOneIndex) (hij : i < j) (a b : T n) :
      (V n i a ⊓ V n j b) ⊓ commonRefinementValue (P n) a b = ⊥ := by
    have hCommon : commonRefinementValue (P n) a b ≤ commonRefinementValue Q (inc n a) (inc n b) :=
      iSup_le fun r => le_iSup_of_le (inc n r) (inf_le_inf (hRef n r a) (hRef n r b))
    exact le_bot_iff.mp ((inf_le_inf_left _ hCommon).trans_eq (hSep i j hij _ _))
  have hZero (n : ℕ) : unboundedValue (fun i => ⨆ a,V n i a) = ⊥ :=
    hCCC n (V n) (fun i a => (hW i (inc n a)).trans_eq (hValid n a)) (hOldSep n)
  have hRow (i : OmegaOneIndex) : (⨆ p,W i p) ≤ ⨆ n,⨆ a,V n i a := by
    apply iSup_le
    intro p
    obtain ⟨n,a,ha⟩ := hCover p
    exact le_iSup_of_le n (le_iSup_of_le a (by simp only [V,ha,le_rfl]))
  apply le_bot_iff.mp
  apply (unboundedValue_mono_r431 hRow).trans
  rw [unboundedValue_countable_cells hB]
  exact iSup_le fun n => (hZero n).le

end JSP000930.Negative
