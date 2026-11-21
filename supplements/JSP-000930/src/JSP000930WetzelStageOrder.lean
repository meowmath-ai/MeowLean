import JSP000930BootstrappedWetzelTail

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.OpenGraphForcing

theorem wetzel_bot_lt_bulk : (⊥ : WetzelStageIndex) < wetzelBulkStage :=
  WithBot.bot_lt_coe _

theorem before_wetzelBulk_only_base (i : WetzelStageIndex) (hi : i < wetzelBulkStage) : i = ⊥ := by
  cases i with
  | none => rfl
  | some i =>
    change (i : WetzelStageIndex) < ((⊥ : WithBot GroundContinuumSuccIndex) : WetzelStageIndex) at hi
    exact (not_lt_of_ge bot_le (WithBot.coe_lt_coe.mp hi)).elim

theorem wetzelBulk_lt_work (i : GroundContinuumSuccIndex) : wetzelBulkStage < wetzelWorkStage i :=
  WithBot.coe_lt_coe.mpr (WithBot.bot_lt_coe _)

theorem wetzelWorkStage_lt_iff (i j : GroundContinuumSuccIndex) :
    wetzelWorkStage i < wetzelWorkStage j ↔ i < j :=
  WithBot.coe_lt_coe.trans WithBot.coe_lt_coe

theorem wetzelWorkStage_le_iff (i j : GroundContinuumSuccIndex) :
    wetzelWorkStage i ≤ wetzelWorkStage j ↔ i ≤ j :=
  WithBot.coe_le_coe.trans WithBot.coe_le_coe

theorem exists_first_ground_wetzel_stage :
    ∃ m : GroundContinuumSuccIndex,∀ j : GroundContinuumSuccIndex,m≤j := by
  classical
  let S : Set GroundContinuumSuccIndex := Set.univ
  have hS : S.Nonempty := ⟨continuumSuccIndexOf 0 groundContinuumSucc_regular_r392.ord_pos, Set.mem_univ _⟩
  obtain ⟨m,hm,hMin⟩ := wellFounded_lt.has_min S hS
  exact ⟨m,fun j => le_of_not_gt (hMin j (Set.mem_univ j))⟩

noncomputable def firstGroundWetzelStage : GroundContinuumSuccIndex :=
  Classical.choose exists_first_ground_wetzel_stage

theorem firstGroundWetzelStage_le (i : GroundContinuumSuccIndex) :
    firstGroundWetzelStage ≤ i := Classical.choose_spec exists_first_ground_wetzel_stage i

theorem wetzelBulk_next (i : WetzelStageIndex) :
    i < wetzelWorkStage firstGroundWetzelStage ↔ i ≤ wetzelBulkStage := by
  constructor
  · intro hi
    cases i with
    | none => exact bot_le
    | some i =>
      cases i with
      | bot => exact le_rfl
      | coe i =>
        exact (not_lt_of_ge (firstGroundWetzelStage_le i)
          ((wetzelWorkStage_lt_iff i _).mp hi)).elim
  · intro hi
    exact lt_of_le_of_lt hi (wetzelBulk_lt_work _)

end JSP000930.Negative
