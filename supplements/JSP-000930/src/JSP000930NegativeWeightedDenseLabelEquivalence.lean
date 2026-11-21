import JSP000930NegativeActualUnchangedProductRows

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing

variable {B N M : Type} [CompleteBooleanAlgebra B]

structure WeightedDenseLabels (Q : ValuedPoset B N) (R : ValuedPoset B M) where
  label : N → M
  valid : ∀ x,R.valid (label x) = Q.valid x
  refines : ∀ x y,R.refines (label x) (label y) = Q.refines x y
  dense : ∀ p m,m ≠ ⊥ → m ≤ R.valid p →
    ∃ (a : N) (s : B),s ≠ ⊥ ∧ s ≤ m ∧ s ≤ R.refines (label a) p

theorem WeightedDenseLabels.cover {Q : ValuedPoset B N} {R : ValuedPoset B M}
    (F : WeightedDenseLabels Q R) (p : M) :
    R.valid p ≤ ⨆ a,R.refines (F.label a) p := by
  by_contra hn
  let U := ⨆ a,R.refines (F.label a) p
  let m := R.valid p ⊓ Uᶜ
  have hm : m ≠ ⊥ := fun he => hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
  obtain ⟨a,s,hs,hsm,ha⟩ := F.dense p m hm inf_le_left
  exact hs (disjoint_compl_right.out _ (ha.trans (le_iSup (fun x => R.refines (F.label x) p) a)) (hsm.trans inf_le_right))

theorem WeightedDenseLabels.common_eq {Q : ValuedPoset B N} {R : ValuedPoset B M}
    (F : WeightedDenseLabels Q R) (p q : N) :
    commonRefinementValue R (F.label p) (F.label q) = commonRefinementValue Q p q := by
  apply le_antisymm ?_ ?_
  · unfold commonRefinementValue
    apply iSup_le
    intro r
    let m := R.refines r (F.label p) ⊓ R.refines r (F.label q)
    let U := commonRefinementValue Q p q
    change m ≤ U
    by_contra hn
    let d := m ⊓ Uᶜ
    have hd : d ≠ ⊥ := fun he => hn (disjoint_compl_right_iff.mp (disjoint_iff_inf_le.mpr he.le))
    have hV : d ≤ R.valid r :=
      inf_le_left.trans (inf_le_left.trans ((R.refine_valid _ _).trans inf_le_left))
    obtain ⟨a,s,hs,hsd,hA⟩ := F.dense r d hd hV
    have hP : s ≤ Q.refines a p := by
      rw [← F.refines a p]
      exact (le_inf hA (hsd.trans (inf_le_left.trans inf_le_left))).trans (R.trans _ _ _)
    have hQ : s ≤ Q.refines a q := by
      rw [← F.refines a q]
      exact (le_inf hA (hsd.trans (inf_le_left.trans inf_le_right))).trans (R.trans _ _ _)
    exact hs (disjoint_compl_right.out _ (le_iSup_of_le a (le_inf hP hQ)) (hsd.trans inf_le_right))
  · apply iSup_le
    intro a
    rw [← F.refines a p,← F.refines a q]
    exact le_iSup (fun t => R.refines t (F.label p) ⊓ R.refines t (F.label q)) (F.label a)

noncomputable def WeightedDenseLabels.toLargerCondensation
    {Q : ValuedPoset B N} {R : ValuedPoset B M} (F : WeightedDenseLabels Q R) :
    SpliceCondensation Q R where
  cell _ p a := R.refines (F.label a) p
  cover p := (F.cover p).trans (le_iSup (fun _ : ℕ => ⨆ a,R.refines (F.label a) p) 0)
  valid _ p a := ((R.refine_valid _ _).trans inf_le_left).trans_eq (F.valid a)
  splice := by
    intro _ p q a b
    rw [← F.common_eq]
    unfold commonRefinementValue
    rw [inf_iSup_eq]
    apply iSup_le
    intro d
    apply le_iSup_of_le d
    exact le_inf ((le_inf (inf_le_right.trans inf_le_left)
      (inf_le_left.trans inf_le_left)).trans (R.trans _ _ _))
      ((le_inf (inf_le_right.trans inf_le_right)
        (inf_le_left.trans inf_le_right)).trans (R.trans _ _ _))

noncomputable def WeightedDenseLabels.toSmallerCondensation
    {Q : ValuedPoset B N} {R : ValuedPoset B M} (F : WeightedDenseLabels Q R) :
    SpliceCondensation R Q := by
  classical
  let C (_ : ℕ) (p : N) (a : M) := if a = F.label p then Q.valid p else ⊥
  refine ⟨C,?_,?_,?_⟩
  · intro p
    exact le_iSup_of_le 0 (le_iSup_of_le (F.label p) (by simp [C]))
  · intro k p a
    by_cases h : a = F.label p
    · subst a
      simp [C,F.valid]
    · simp only [C,ite_eq_right h,bot_le]
  · intro k p q a b
    by_cases ha : a = F.label p
    · by_cases hb : b = F.label q
      · simp only [C,ite_eq_left ha,ite_eq_left hb,ha,hb,F.common_eq]
        exact inf_le_right
      · simp only [C,ite_eq_right hb,inf_bot_eq,bot_inf_eq,bot_le]
    · simp only [C,ite_eq_right ha,bot_inf_eq,bot_le]

theorem WeightedDenseLabels.relativeCCC_iff
    {Q : ValuedPoset B N} {R : ValuedPoset B M} (F : WeightedDenseLabels Q R)
    (hB : BoundsCountableOmegaOneNames B) :
    ForcesRelativeCCC Q ↔ ForcesRelativeCCC R :=
  ⟨F.toLargerCondensation.relativeCCC hB,F.toSmallerCondensation.relativeCCC hB⟩

end JSP000930.Negative
