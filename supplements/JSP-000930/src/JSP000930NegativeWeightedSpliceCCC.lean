import JSP000930NegativeWeightedCountableCondensation

namespace JSP000930.Negative

open JSP000933.OpenGraphForcing JSP000933.RelativeOCA
  JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B N M : Type} [CompleteBooleanAlgebra B]

structure SpliceCondensation (old : ValuedPoset B M) (new : ValuedPoset B N) where
  cell : ℕ → N → M → B
  cover : ∀ p,new.valid p ≤ ⨆ k : ℕ,⨆ a : M,cell k p a
  valid : ∀ k p a,cell k p a ≤ old.valid a
  splice : ∀ k p q a b,
    ((cell k p a ⊓ cell k q b) ⊓ commonRefinementValue old a b) ≤
      commonRefinementValue new p q

theorem SpliceCondensation.relativeCCC
    {old : ValuedPoset B M} {new : ValuedPoset B N}
    (S : SpliceCondensation old new)
    (hB : BoundsCountableOmegaOneNames B) (hOld : ForcesRelativeCCC old) :
    ForcesRelativeCCC new := by
  intro W hW hSep
  let V (k : ℕ) (i : OmegaOneIndex) (a : M) := ⨆ p,W i p ⊓ S.cell k p a
  have hValid (k : ℕ) (i : OmegaOneIndex) (a : M) : V k i a ≤ old.valid a :=
    iSup_le (fun p => inf_le_right.trans (S.valid k p a))
  have hApart (k : ℕ) (i j : OmegaOneIndex) (hij : i < j) (a b : M) :
      (V k i a ⊓ V k j b) ⊓ commonRefinementValue old a b = ⊥ := by
    apply le_bot_iff.mp
    dsimp only [V]
    rw [iSup_inf_eq, iSup_inf_eq]
    apply iSup_le
    intro p
    rw [inf_iSup_eq, iSup_inf_eq]
    apply iSup_le
    intro q
    let A := (W i p ⊓ S.cell k p a) ⊓ (W j q ⊓ S.cell k q b)
    have hLeft : A ≤ W i p ⊓ W j q :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have hRight : A ≤ S.cell k p a ⊓ S.cell k q b :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    exact (le_inf (inf_le_left.trans hLeft)
      ((inf_le_inf hRight le_rfl).trans (S.splice k p q a b))).trans_eq
      (hSep i j hij p q)
  have hZero (k : ℕ) : unboundedValue (fun i => ⨆ a,V k i a) = ⊥ :=
    hOld (V k) (hValid k) (hApart k)
  have hCover (i : OmegaOneIndex) : (⨆ p,W i p) ≤ ⨆ k : ℕ,⨆ a : M,V k i a := by
    apply iSup_le
    intro p
    apply (le_inf le_rfl ((hW i p).trans (S.cover p))).trans
    rw [inf_iSup_eq]
    apply iSup_le
    intro k
    rw [inf_iSup_eq]
    apply iSup_le
    intro a
    exact le_iSup_of_le k (le_iSup_of_le a (le_iSup (fun q => W i q ⊓ S.cell k q a) p))
  apply le_bot_iff.mp
  apply (unboundedValue_mono_r431 hCover).trans
  rw [unboundedValue_countable_cells hB]
  exact iSup_le fun k => (hZero k).le

theorem finiteSpliceCondensation_CCC
    (hB : BoundsCountableOmegaOneNames B) {T : ℕ → Type}
    (Q : ∀ n,ValuedPoset B (T n))
    (S : ∀ n,SpliceCondensation (Q n) (Q (n+1)))
    (h0 : ForcesRelativeCCC (Q 0)) : ∀ n,ForcesRelativeCCC (Q n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact (S n).relativeCCC hB ih

end JSP000930.Negative
