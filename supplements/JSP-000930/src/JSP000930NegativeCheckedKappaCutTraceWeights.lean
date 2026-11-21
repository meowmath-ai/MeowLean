import JSP000930NegativeSmallAmbientRectangleRealCover
import JSP000930PositiveOneReserveUnboundedFamily
import JSP000933PreparedSmallTraceEnum
import JSP000933LocalKappaTraceSupport

open Cardinal

namespace JSP000930.Negative

open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.OpenGraphForcing
  JSP000933.RelativeOCA JSP000933.CantorCodes JSP000933.PreparedModel
  JSP000930.Positive.Cohen

abbrev ClosedKappaCut (c : GroundContinuumSuccIndex) := {j : GroundContinuumSuccIndex // j ≤ c}

instance (c : GroundContinuumSuccIndex) : Nonempty (ClosedKappaCut c) :=
  ⟨⟨c,le_rfl⟩⟩

theorem closedKappaCut_card (c : GroundContinuumSuccIndex) :
    Cardinal.mk (ClosedKappaCut c) ≤ 𝔠 := by
  obtain ⟨d⟩ := kappa_above_nonempty c
  let g : ClosedKappaCut c → {j : GroundContinuumSuccIndex // j < d.val} :=
    fun j => ⟨j.val,j.property.trans_lt d.property⟩
  have hg : Function.Injective g := fun _ _ h => Subtype.ext (congrArg (fun j : {j : GroundContinuumSuccIndex // j < d.val} => j.val) h)
  exact (Cardinal.mk_le_of_injective hg).trans
    (Order.lt_succ_iff.mp (continuumSuccInitial_card_lt_r406 d.val))

variable {N : Type}

noncomputable def cutoffGreedyWeight (Q : ValuedPoset PreparedBA N)
    (f : GroundContinuumSuccIndex → N) (hf : Function.Surjective f)
    (x : ℕ → TotalBA Q) (c : GroundContinuumSuccIndex) (n : ℕ) (j : ClosedKappaCut c) : PreparedBA :=
  if j.val < c then greedyTraceWeight Q (groundMixedEnumeration f hf) (x n) j.val (f j.val)
  else ⊥

theorem cutoffGreedyWeight_valid (Q : ValuedPoset PreparedBA N)
    (f : GroundContinuumSuccIndex → N) (hf : Function.Surjective f)
    (x : ℕ → TotalBA Q) (c : GroundContinuumSuccIndex) (n : ℕ)
    (j : ClosedKappaCut c) :
    cutoffGreedyWeight Q f hf x c n j ≤ Q.valid (f j.val) := by
  by_cases h : j.val < c
  · simpa only [cutoffGreedyWeight,ite_eq_left h] using
      (greedyTraceWeight_valid_r465 Q (groundMixedEnumeration f hf) (x n) j.val (f j.val))
  · simp [cutoffGreedyWeight,h]

theorem cutoffGreedyWeight_apart (Q : ValuedPoset PreparedBA N)
    (f : GroundContinuumSuccIndex → N) (hf : Function.Surjective f)
    (x : ℕ → TotalBA Q) (c : GroundContinuumSuccIndex) (n : ℕ)
    (j k : ClosedKappaCut c) (h : j ≠ k) :
    (cutoffGreedyWeight Q f hf x c n j ⊓ cutoffGreedyWeight Q f hf x c n k) ⊓
      commonRefinementValue Q (f j.val) (f k.val) = ⊥ := by
  by_cases hj : j.val < c
  · by_cases hk : k.val < c
    · simp only [cutoffGreedyWeight,ite_eq_left hj,ite_eq_left hk]
      have hne : j.val ≠ k.val := fun he => h (Subtype.ext he)
      rcases lt_or_gt_of_ne hne with hl | hl
      · exact greedyTraceWeight_apart_r465 Q (groundMixedEnumeration f hf) (x n) _ _ hl _ _
      · rw [inf_comm (greedyTraceWeight Q (groundMixedEnumeration f hf) (x n) j.val (f j.val))
          (greedyTraceWeight Q (groundMixedEnumeration f hf) (x n) k.val (f k.val)),
          commonRefinementValue_comm_r464 Q (f j.val) (f k.val)]
        exact greedyTraceWeight_apart_r465 Q (groundMixedEnumeration f hf) (x n) _ _ hl _ _
    · simp [cutoffGreedyWeight,hk]
  · simp [cutoffGreedyWeight,hj]

theorem cutoffGreedyWeight_real (Q : ValuedPoset PreparedBA N)
    (f : GroundContinuumSuccIndex → N) (hf : Function.Surjective f)
    (x : ℕ → TotalBA Q) (c : GroundContinuumSuccIndex) (n : ℕ) :
    weightedTraceReal Q (fun j : ClosedKappaCut c => f j.val)
      (cutoffGreedyWeight Q f hf x c) n =
      initialKappaGreedyValue Q (groundMixedEnumeration f hf) (x n) c := by
  rw [initialKappaGreedyValue_ground_r478 Q f hf (x n) c]
  let U := greedyTraceWeight Q (groundMixedEnumeration f hf) (x n)
  apply le_antisymm
  · apply iSup_le
    intro j
    by_cases hj : j.val < c
    · simp only [cutoffGreedyWeight,ite_eq_left hj]
      exact le_iSup_of_le (⟨j.val,hj⟩ : Set.Iio c) le_rfl
    · simp only [cutoffGreedyWeight,ite_eq_right hj,traceRectangle_zero_r464,bot_le]
  · apply iSup_le
    intro j
    refine le_iSup_of_le (⟨j.val,j.property.le⟩ : ClosedKappaCut c) ?_
    have hj : j.val < c := j.property
    simp only [cutoffGreedyWeight,ite_eq_left hj,U]
    exact le_rfl

end JSP000930.Negative
