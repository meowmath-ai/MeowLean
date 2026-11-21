import JSP000930NegativeRealPreparedRelativeDirectLimitCCC

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
  JSP000933.OpenGraphForcing JSP000933.PreparedModel

variable {B N : Type} [CompleteBooleanAlgebra B]

def inertOutsideValue (m x : B) : B := (m ⊓ x) ⊔ mᶜ

theorem inertOutside_mono (m : B) : Monotone (inertOutsideValue m) :=
  fun _ _ h => sup_le_sup_right (inf_le_inf_left _ h) _

theorem inertOutside_inf (m x y : B) :
    inertOutsideValue m (x ⊓ y) =
      inertOutsideValue m x ⊓ inertOutsideValue m y := by
  have hm : m ⊓ (x ⊓ y) = (m ⊓ x) ⊓ (m ⊓ y) := by
    apply le_antisymm
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
        (le_inf inf_le_left (inf_le_right.trans inf_le_right))
    · exact le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  unfold inertOutsideValue
  rw [hm]
  rw [sup_comm ((m ⊓ x) ⊓ (m ⊓ y)),sup_inf_left]
  rw [sup_comm mᶜ (m ⊓ x),sup_comm mᶜ (m ⊓ y)]

theorem inertOutside_clip (m x : B) :
    m ⊓ inertOutsideValue m x = m ⊓ x := by
  unfold inertOutsideValue
  simp only [inf_sup_left,← inf_assoc,inf_idem,inf_compl_eq_bot,sup_bot_eq]

theorem inertOutside_iSup (m : B) {I : Type} [Nonempty I] (v : I → B) :
    inertOutsideValue m (⨆ i,v i) = ⨆ i,inertOutsideValue m (v i) := by
  apply le_antisymm ?_ (iSup_le fun i => inertOutside_mono m (le_iSup v i))
  unfold inertOutsideValue
  rw [inf_iSup_eq]
  apply sup_le
  · exact iSup_le fun i => le_iSup_of_le i le_sup_left
  · obtain ⟨i⟩ := ‹Nonempty I›
    exact le_iSup_of_le i le_sup_right

def inertOutside (Q : ValuedPoset B N) (m : B) : ValuedPoset B N where
  valid t := inertOutsideValue m (Q.valid t)
  refines t u := inertOutsideValue m (Q.refines t u)
  refine_valid t u :=
    (inertOutside_mono m (Q.refine_valid t u)).trans_eq (inertOutside_inf _ _ _)
  refl t := inertOutside_mono m (Q.refl t)
  trans t u v := (inertOutside_inf _ _ _).ge.trans (inertOutside_mono m (Q.trans t u v))
  weakest := Q.weakest
  weakest_valid := by
    change inertOutsideValue m (Q.valid Q.weakest) = ⊤
    simp only [Q.weakest_valid,inertOutsideValue,inf_top_eq,sup_compl_eq_top]
  weaker t := inertOutside_mono m (Q.weaker t)

theorem inertOutside_common (Q : ValuedPoset B N) (m : B) (t u : N) :
    commonRefinementValue (inertOutside Q m) t u =
      inertOutsideValue m (commonRefinementValue Q t u) := by
  letI : Nonempty N := ⟨Q.weakest⟩
  change (⨆ r : N, inertOutsideValue m (Q.refines r t) ⊓
    inertOutsideValue m (Q.refines r u)) = inertOutsideValue m (⨆ r : N,Q.refines r t ⊓ Q.refines r u)
  simp only [← inertOutside_inf,inertOutside_iSup]

def RelativeCCCOn (Q : ValuedPoset B N) (m : B) : Prop :=
  ∀ W : OmegaOneIndex → N → B,
    (∀ i t,W i t ≤ Q.valid t) →
    (∀ i j,i<j→∀ t u,
      (W i t ⊓ W j u) ⊓ commonRefinementValue Q t u = ⊥) →
    m ⊓ unboundedValue (fun i => ⨆ t,W i t) = ⊥

theorem unboundedValue_inf_mask (m : B) (w : OmegaOneIndex → B) :
    unboundedValue (fun i => m ⊓ w i) = m ⊓ unboundedValue w := by
  unfold unboundedValue aboveValue
  simp only [← inf_iSup_eq]
  apply le_antisymm
  · have hn : Nonempty OmegaOneIndex := Cardinal.mk_ne_zero_iff.mp (by
      rw [mk_OmegaOneIndex_r61]
      exact (Cardinal.aleph_pos _).ne')
    obtain ⟨a⟩ := hn
    exact le_inf ((iInf_le _ a).trans inf_le_left)
      (le_iInf fun i => (iInf_le _ i).trans inf_le_right)
  · exact le_iInf fun i => inf_le_inf_left _ (iInf_le _ i)

theorem relativeCCC_glue {I : Type} (Q : ValuedPoset B N) (m : I → B)
    (hM : (⨆ i,m i) = ⊤) (hc : ∀ i,RelativeCCCOn Q (m i)) :
    ForcesRelativeCCC Q := by
  intro W hW hSep
  let X := unboundedValue (fun i => ⨆ t,W i t)
  change X = ⊥
  rw [← top_inf_eq X,← hM,iSup_inf_eq]
  have h (i : I) : m i ⊓ X = ⊥ := hc i W hW hSep
  simp only [h,iSup_bot]

end JSP000930.Negative
