import JSP000933RelativeGreedyCuts

namespace JSP000933
namespace RelativeOCA

open MarkedForcing BooleanCompletion OpenGraphForcing CantorCodes

variable {B N : Type} [CompleteBooleanAlgebra B]

noncomputable def actualGreedyCut (Q : ValuedPoset B N) (E : MixedEnumeration OmegaOneIndex N B)
    (x : ℕ→TotalBA Q) (c : OmegaOneIndex) : B :=
  ⨅ n,⨆ b : ↥(Set.Iio c),(aboveValue (greedyRowActive Q E (x n)) b.val)ᶜ

theorem actualGreedyCuts_cover_r468 (Q : ValuedPoset B N)
    (hQ : ForcesRelativeCCC Q) (hB : BoundsCountableOmegaOneNames B)
    (E : MixedEnumeration OmegaOneIndex N B) (x : ℕ→TotalBA Q) :
    (⨆ c,actualGreedyCut Q E x c)=⊤ := by
  let F (n : ℕ) (b : OmegaOneIndex) := (aboveValue (greedyRowActive Q E (x n)) b)ᶜ
  have hF (n : ℕ) : (⨆ b,F n b)=⊤ := by
    have h := omegaOne_greedyWeight_bounded_r465 Q hQ E (x n)
    have hc := congrArg (fun v : B => vᶜ) h
    change (unboundedValue (greedyRowActive Q E (x n)))ᶜ = (⊥ : B)ᶜ at hc
    simpa only [unboundedValue,F,compl_iInf,compl_bot] using hc
  exact top_unique ((le_iInf (fun n => (hF n).ge)).trans (hB F))

theorem actualGreedyCut_disjoint_r468 (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (x : ℕ→TotalBA Q)
    (c i : OmegaOneIndex) (hi : c≤ i) (n : ℕ) :
    Disjoint (actualGreedyCut Q E x c) (greedyRowActive Q E (x n) i) := by
  apply le_compl_iff_disjoint_right.mp
  apply (iInf_le _ n).trans
  apply iSup_le
  intro b
  exact compl_le_compl (le_iSup (fun j : {j : OmegaOneIndex // b.val < j} => greedyRowActive Q E (x n) j.val)
    ⟨i,b.property.trans_le hi⟩)

abbrev CutCodeSlot (c : OmegaOneIndex) := ℕ×↥(Set.Iio c)

noncomputable def initialTableReal (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (c : OmegaOneIndex) (u : CutCodeSlot c→B) :
    ℕ→TotalBA Q :=
  fun n => ⨆ i : ↥(Set.Iio c),⨆ k,traceRectangle Q k (u (n,i)⊓E.cell i.val k)

theorem initialTableReal_mask_r468 (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (c : OmegaOneIndex)
    (u v : CutCodeSlot c→B) (m : B) (he : m≤tableAgreement u v) (n : ℕ) :
    baseEmbed Q m⊓initialTableReal Q E c u n=baseEmbed Q m⊓initialTableReal Q E c v n := by
  have h := (tableAgreement_spec_r441 u v m).mp he
  unfold initialTableReal
  apply mask_iSup_congr_r126
  intro i
  apply mask_iSup_congr_r126
  intro k
  rw [traceRectangle_meet_base_r467,traceRectangle_meet_base_r467]
  apply congrArg (traceRectangle Q k)
  exact (inf_assoc _ _ _).symm.trans ((congrArg (fun x => x⊓E.cell i.val k) (h (n,i))).trans
    (inf_assoc _ _ _))

theorem genuineCut_encodedReal_agrees_r468 (Q : ValuedPoset B N)
    (E : MixedEnumeration OmegaOneIndex N B) (x : ℕ→TotalBA Q)
    (c : OmegaOneIndex) (m : B) (v : CutCodeSlot c→B)
    (hm : m≤actualGreedyCut Q E x c)
    (he : m≤tableAgreement (fun p : CutCodeSlot c => greedyRowActive Q E (x p.1) p.2.val) v) :
    baseEmbed Q m≤realEqValue x (initialTableReal Q E c v) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro n
  have hCut := greedy_initial_on_cut_r467 Q E (x n) c m
    (fun i hi => (actualGreedyCut_disjoint_r468 Q E x c i hi n).mono_left hm)
  have hTab : initialGreedyValue Q E (x n) c=
      initialTableReal Q E c (fun p : CutCodeSlot c => greedyRowActive Q E (x p.1) p.2.val) n := by
    simp only [initialGreedyValue,initialTableReal,greedyRowActive_spec_r467]
  exact (hCut.trans (congrArg (fun z => baseEmbed Q m⊓z) hTab)).trans
    (initialTableReal_mask_r468 Q E c _ v m he n)

end RelativeOCA
end JSP000933
