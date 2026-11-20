import JSP000933GreedyProbeCuts

open Cardinal

namespace JSP000933
namespace RelativeOCA

open PreparedModel MarkedForcing BooleanCompletion CantorCodes

variable {N : Type}

noncomputable def greedyProbeMatrix (Q : ValuedPoset PreparedBA N)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (x : GroundContinuumSuccIndex→TotalBA Q)
    (i j : GroundContinuumSuccIndex) : PreparedBA :=
  greedyTraceWeight Q (groundMixedEnumeration f hf) (x i) j (f j)

noncomputable def guessedPrefixProbe (Q : ValuedPoset PreparedBA N)
    (f : GroundContinuumSuccIndex→N) (d i : GroundContinuumSuccIndex) : TotalBA Q :=
  ⨆ j : ↥(Set.Iio d),traceRectangle Q (f j.val) (decodePreparedGuess d (kappaPairCode (i,j.val)))

theorem booleanAgree_eq_bitEq_r485 (u v : PreparedBA) : booleanAgree u v=bitEq u v := by
  simp only [booleanAgree,bitEq,himp_eq,sup_comm]

set_option maxHeartbeats 600000 in
theorem exists_actual_reflectedProbe_r485 (Q : ValuedPoset PreparedBA N)
    (hQ : ForcesRelativeCCC Q)
    (f : GroundContinuumSuccIndex→N) (hf : Function.Surjective f)
    (scope : N→Finset GroundContinuumSuccIndex)
    (x : GroundContinuumSuccIndex→TotalBA Q) (p : TotalBA Q) (hp : p≠⊥) :
    ∃ (d : GroundContinuumSuccIndex) (m : PreparedBA) (r : TotalCondition Q),
      OmegaOneCofinalIndex d ∧ m≠⊥ ∧ imageCondition r≤p⊓baseEmbed Q m ∧
      (∀ i<d,∀ k∈scope (f i),k<d) ∧
      ∀ i<d,baseEmbed Q m⊓x i=baseEmbed Q m⊓guessedPrefixProbe Q f d i := by
  classical
  let A := packedKappaMatrix (greedyProbeMatrix Q f hf x)
  let F := clubProbeCut Q f hf scope x
  let C := mixedClosedStageValue F
  have hF (i : GroundContinuumSuccIndex) : (⨆ b,F i b)=⊤ :=
    clubProbeCut_cover_r484 Q hQ actual_prepared_boundsSmallKappa_r473 f hf scope x i
  have hTop : (⊤ : PreparedBA)≤preparedCorrectGuessValue A C :=
    prepared_diamondOnMixedClosedStages_r482 A F hF
  let P := supportProjection Q p
  have hP : P≠⊥ := fun he => hp ((supportProjection_zero_iff_r428 Q p).mp he)
  let V (d : {d : GroundContinuumSuccIndex // OmegaOneCofinalIndex d}) :=
    C d.val⊓⨅ j : ↥(Set.Iio d.val),booleanAgree (A j.val) (decodePreparedGuess d.val j.val)
  obtain ⟨d0,m,hm,hmP,hmV⟩ := exists_nonzero_below_choice_r135 P hP V (le_top.trans hTop)
  let d := d0.val
  have hd : OmegaOneCofinalIndex d := d0.property
  have hC : m≤C d := hmV.trans inf_le_left
  have hB (i : GroundContinuumSuccIndex) (hi : i<d) : codeTraceStageBound f scope i<d :=
    clubProbeCut_scopeBound_r484 Q f hf scope x m d i hm hC hi
  have hScope (i : GroundContinuumSuccIndex) (hi : i<d) (k : GroundContinuumSuccIndex)
      (hk : k∈scope (f i)) : k<d := by
    obtain ⟨j,hij,hj⟩ := omegaOneCofinalIndex_between_r483 hd hi
    exact ((codeTraceStageBound_spec_r484 f scope j).2 i hij k hk).trans (hB j hj)
  have hCode (i j : GroundContinuumSuccIndex) (hi : i<d) (hj : j<d) :
      kappaPairCode (i,j)<d := by
    obtain ⟨b,hij,hb⟩ := omegaOneCofinalIndex_between_r483 hd (max_lt hi hj)
    exact ((codeTraceStageBound_spec_r484 f scope b).1 i ((le_max_left _ _).trans_lt hij)
      j ((le_max_right _ _).trans_lt hij)).trans (hB b hb)
  have hMatch (i j : GroundContinuumSuccIndex) (hi : i<d) (hj : j<d) :
      m⊓greedyProbeMatrix Q f hf x i j=m⊓decodePreparedGuess d (kappaPairCode (i,j)) := by
    have hh : m≤booleanAgree (A (kappaPairCode (i,j))) (decodePreparedGuess d (kappaPairCode (i,j))) :=
      (hmV.trans inf_le_right).trans (iInf_le (fun t : ↥(Set.Iio d) =>
        booleanAgree (A t.val) (decodePreparedGuess d t.val)) ⟨kappaPairCode (i,j),hCode i j hi hj⟩)
    rw [booleanAgree_eq_bitEq_r485] at hh
    apply (le_bitEq_iff_r126 _ _ _).mp
    simpa only [A,packedKappaMatrix_eval_r483] using hh
  have hN : p⊓baseEmbed Q m≠⊥ := by
    intro he
    have hs := supportProjection_meet_base_r428 Q p m
    rw [he,(supportProjection_zero_iff_r428 Q ⊥).mpr rfl,inf_eq_right.mpr hmP] at hs
    exact hm hs.symm
  obtain ⟨r,hr⟩ := imageCondition_dense_r50 _ hN
  refine ⟨d,m,r,hd,hm,hr,hScope,fun i hi => ?_⟩
  let E : MixedEnumeration GroundContinuumSuccIndex N PreparedBA :=
    groundMixedEnumeration f hf
  have hNo (j : GroundContinuumSuccIndex) (hj : d≤j) :
      Disjoint m (greedyRowActive Q E (x i) j) :=
    clubProbeCut_noLate_r484 Q f hf scope x m d i j hC hi hj
  calc
    baseEmbed Q m⊓x i=baseEmbed Q m⊓initialKappaGreedyValue Q E (x i) d :=
      greedy_initial_on_kappaCut_r476 Q E (x i) d m hNo
    _ = baseEmbed Q m⊓(⨆ j : ↥(Set.Iio d),traceRectangle Q (f j.val) (greedyProbeMatrix Q f hf x i j.val)) :=
      congrArg (fun z => baseEmbed Q m⊓z) (initialKappaGreedyValue_ground_r478 Q f hf (x i) d)
    _ = baseEmbed Q m⊓guessedPrefixProbe Q f d i := by
      unfold guessedPrefixProbe
      apply mask_iSup_congr_r126
      intro j
      rw [traceRectangle_meet_base_r467,traceRectangle_meet_base_r467]
      exact congrArg (traceRectangle Q (f j.val)) (hMatch i j.val hi j.property)

end RelativeOCA
end JSP000933
