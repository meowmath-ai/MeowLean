import JSP000930NegativeGenuineMixedRegressiveReductions

namespace JSP000930.Negative

open JSP000933.RelativeOCA JSP000933.OpenGraphForcing JSP000933.BooleanCompletion

variable {P D I : Type} [Preorder P] [CompleteBooleanAlgebra D] [LinearOrder I]
variable {A : I → Type} [∀ t,CompleteBooleanAlgebra (A t)]

theorem projectedCCC_of_mixed_continuousTower
    (hP : IsCountablyClosed P) (hB : BoundsCountableOmegaOneNames (RO P))
    (F : CompleteValueMap (RO P) D) (T : CompleteStageTower F A)
    (hT : ContinuousStageTower T) (C : MixedCofinalStageSequence (RO P) I)
    (hCCC : ∀ a,ProjectedAntichainCCC (prefixReduce (T.base a))) :
    ProjectedAntichainCCC (prefixReduce F) := by
  intro X hX
  let m := unboundedValue (fun i => prefixReduce F (X i))
  change m = ⊥
  have hReg : m ≤ ⨆ a,unboundedValue (fun j => mixedReductionWeight T C X j a) :=
    relative_regressive_limit_rows_unbounded hP m (mixedReductionWeight T C X)
      (mixedReductionRows_cover T hT C X m le_rfl)
  apply le_bot_iff.mp
  apply hReg.trans
  apply iSup_le
  intro a
  let u := unboundedValue (fun j => mixedReductionWeight T C X j a)
  change u ≤ ⊥
  rw [← inf_top_eq u,← (C.pick a).covers,inf_iSup_eq]
  apply iSup_le
  intro s
  let v := u ⊓ (C.pick a).value s
  let J := Σ d : OmegaOneIndex,MixedTowerReduction T C X d a s
  let row (j : J) := j.1
  let rank (j : J) := max j.1 (max j.2.laterCutRow j.2.row)
  let Y (j : J) := j.2.small
  let W (j : J) := prefixReduce (T.base s) (Y j)
  have hTail : ∀ b,v ≤ ⨆ j : {j : J // b < row j},W j.val := by
    intro b
    apply (inf_le_inf (iInf_le _ b) le_rfl).trans
    unfold aboveValue
    rw [iSup_inf_eq]
    apply iSup_le
    intro d
    unfold mixedReductionWeight
    rw [iSup_inf_eq]
    apply iSup_le
    intro t
    rw [iSup_inf_eq]
    apply iSup_le
    intro q
    by_cases h : t = s
    · subst t
      exact inf_le_left.trans
        (le_iSup (fun j : {j : J // b < row j} => W j.val) ⟨⟨d.val,q⟩,d.property⟩)
    · exact (disjoint_iff_inf_le.mp (((C.pick a).disjoint h).mono_left q.small_old_mask)).trans bot_le
  have hSep (i j : J) (h : rank i < row j) : Disjoint (Y i) (Y j) :=
    i.2.apart_when_late hX j.2
      ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt h))
      ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt h))
  exact (projectedCCC_forbids_skew_unbounded hB (T.base s) (hCCC s) rank row Y W
    (fun _ => le_rfl) hSep v hTail).le

variable [WellFoundedLT I] [Nonempty I]

theorem projectedCCC_of_mixedOmegaOne_prepared_limit
    (hP : IsCountablyClosed P) (hB : BoundsCountableOmegaOneNames (RO P))
    (F : CompleteValueMap (RO P) D) (T : CompleteStageTower F A)
    (hT : ContinuousStageTower T)
    (hI : AllCountableGroundBounded I) (E : MixedEnumeration OmegaOneIndex I (RO P))
    (hCCC : ∀ a,ProjectedAntichainCCC (prefixReduce (T.base a))) :
    ProjectedAntichainCCC (prefixReduce F) := by
  obtain ⟨C⟩ := exists_mixedCofinalStageSequence hP hI E
  exact projectedCCC_of_mixed_continuousTower hP hB F T hT C hCCC

end JSP000930.Negative
