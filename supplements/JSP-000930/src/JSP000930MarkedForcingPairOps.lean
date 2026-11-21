import JSP000933RelativeCCCProjection
import JSP000933CompleteValueMap

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

variable {B C N K : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

noncomputable def valuedPair (P : ValuedPoset B N) (Q : ValuedPoset B K) :
    ValuedPoset B (N × K) where
  valid p := P.valid p.1 ⊓ Q.valid p.2
  refines q p := P.refines q.1 p.1 ⊓ Q.refines q.2 p.2
  refine_valid q p := by
    refine le_inf (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact inf_le_left.trans ((P.refine_valid _ _).trans inf_le_left)
    · exact inf_le_right.trans ((Q.refine_valid _ _).trans inf_le_left)
    · exact inf_le_left.trans ((P.refine_valid _ _).trans inf_le_right)
    · exact inf_le_right.trans ((Q.refine_valid _ _).trans inf_le_right)
  refl p := inf_le_inf (P.refl _) (Q.refl _)
  trans r q p := le_inf
    ((le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)).trans (P.trans _ _ _))
    ((le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans (Q.trans _ _ _))
  weakest := (P.weakest,Q.weakest)
  weakest_valid := by rw [P.weakest_valid,Q.weakest_valid,inf_top_eq]
  weaker p := inf_le_inf (P.weaker _) (Q.weaker _)

theorem common_valuedPair (P : ValuedPoset B N) (Q : ValuedPoset B K) (p q : N × K) :
    commonRefinementValue (valuedPair P Q) p q =
       commonRefinementValue P p.1 q.1 ⊓ commonRefinementValue Q p.2 q.2 := by
  unfold commonRefinementValue
  rw [iSup_inf_iSup]
  apply iSup_congr
  intro r
  change ((P.refines r.1 p.1 ⊓ Q.refines r.2 p.2) ⊓
      (P.refines r.1 q.1 ⊓ Q.refines r.2 q.2)) =
    ((P.refines r.1 p.1 ⊓ P.refines r.1 q.1) ⊓
      (Q.refines r.2 p.2 ⊓ Q.refines r.2 q.2))
  ac_rfl

def changeValuedBase (F : CompleteValueMap B C) (Q : ValuedPoset B N) : ValuedPoset C N where
  valid p := F.toFun (Q.valid p)
  refines q p := F.toFun (Q.refines q p)
  refine_valid q p := (F.monotone (Q.refine_valid q p)).trans_eq (F.map_inf _ _)
  refl p := F.monotone (Q.refl p)
  trans r q p := (le_of_eq (F.map_inf _ _).symm).trans (F.monotone (Q.trans r q p))
  weakest := Q.weakest
  weakest_valid := (congrArg F.toFun Q.weakest_valid).trans F.map_top
  weaker p := F.monotone (Q.weaker p)

theorem common_changeValuedBase (F : CompleteValueMap B C) (Q : ValuedPoset B N) (p q : N) :
    commonRefinementValue (changeValuedBase F Q) p q =
       F.toFun (commonRefinementValue Q p q) := by
  unfold commonRefinementValue
  simp only [changeValuedBase, F.map_iSup, F.map_inf]

end JSP000930.Negative
