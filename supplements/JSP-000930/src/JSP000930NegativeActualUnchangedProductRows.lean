import JSP000930NegativeActualNamedRowCondensation
import JSP000930MarkedAnalyticRowProduct

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA

variable {B N M T : Type} [CompleteBooleanAlgebra B]

noncomputable def pairedRowQ (Q : ValuedPoset B N) (R : ValuedPoset B T) :
    ValuedPoset B (N × T) where
  valid p := Q.valid p.1 ⊓ R.valid p.2
  refines p q := Q.refines p.1 q.1 ⊓ R.refines p.2 q.2
  refine_valid p q := le_inf
    (le_inf (inf_le_left.trans ((Q.refine_valid _ _).trans inf_le_left))
      (inf_le_right.trans ((R.refine_valid _ _).trans inf_le_left)))
    (le_inf (inf_le_left.trans ((Q.refine_valid _ _).trans inf_le_right))
      (inf_le_right.trans ((R.refine_valid _ _).trans inf_le_right)))
  refl p := inf_le_inf (Q.refl _) (R.refl _)
  trans p q r := le_inf
    ((le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)).trans (Q.trans _ _ _))
    ((le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans (R.trans _ _ _))
  weakest := (Q.weakest,R.weakest)
  weakest_valid := by simp only [Q.weakest_valid,R.weakest_valid,inf_top_eq]
  weaker p := inf_le_inf (Q.weaker _) (R.weaker _)

theorem pairedRow_common (Q : ValuedPoset B N) (R : ValuedPoset B T) (p q : N × T) :
    commonRefinementValue (pairedRowQ Q R) p q =
      commonRefinementValue Q p.1 q.1 ⊓ commonRefinementValue R p.2 q.2 := by
  unfold commonRefinementValue
  rw [iSup_inf_iSup]
  apply iSup_congr
  rintro ⟨r,s⟩
  change (Q.refines r p.1 ⊓ R.refines s p.2) ⊓ (Q.refines r q.1 ⊓ R.refines s q.2) =
    (Q.refines r p.1 ⊓ Q.refines r q.1) ⊓ (R.refines s p.2 ⊓ R.refines s q.2)
  ac_rfl

noncomputable def SpliceCondensation.withUnchangedRows
    {Q : ValuedPoset B M} {P : ValuedPoset B N} (S : SpliceCondensation Q P)
    (R : ValuedPoset B T) : SpliceCondensation (pairedRowQ Q R) (pairedRowQ P R) := by
  classical
  let C (k : ℕ) (p : N × T) (a : M × T) : B :=
    if p.2 = a.2 then S.cell k p.1 a.1 ⊓ R.valid p.2 else ⊥
  refine ⟨C,?_,?_,?_⟩
  · intro p
    change (P.valid p.1 ⊓ R.valid p.2) ≤ _
    apply (inf_le_inf_right _ (S.cover p.1)).trans
    rw [iSup_inf_eq]
    apply iSup_le
    intro k
    rw [iSup_inf_eq]
    apply iSup_le
    intro a
    exact le_iSup_of_le k (le_iSup_of_le (a,p.2) (by simp [C]))
  · intro k p a
    by_cases h : p.2 = a.2
    · change C k p a ≤ Q.valid a.1 ⊓ R.valid a.2
      simp only [C,ite_eq_left h,h]
      exact inf_le_inf_right _ (S.valid _ _ _)
    · simp only [C,ite_eq_right h,bot_le]
  · intro k p q a b
    by_cases ha : p.2 = a.2
    · by_cases hb : q.2 = b.2
      · rw [pairedRow_common,pairedRow_common]
        simp only [C,ite_eq_left ha,ite_eq_left hb,← ha,← hb]
        refine le_inf ?_ (inf_le_right.trans inf_le_right)
        apply le_trans ?_ (S.splice k p.1 q.1 a.1 b.1)
        exact le_inf (inf_le_left.trans (inf_le_inf inf_le_left inf_le_left))
          (inf_le_right.trans inf_le_left)
      · simp only [C,ite_eq_right hb,inf_bot_eq,bot_inf_eq,bot_le]
    · simp only [C,ite_eq_right ha,bot_inf_eq,bot_le]

end JSP000930.Negative
