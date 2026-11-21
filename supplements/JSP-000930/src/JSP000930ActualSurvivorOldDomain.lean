import JSP000930ActualWorkCohenIso

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

variable {B C I : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]
variable {N : I → Type}

theorem change_rowProduct930 (F : CompleteValueMap B C) (Q : ∀ i,ValuedPoset B (N i)) :
    changeValuedBase F (rowProductQ Q) = rowProductQ (fun i => changeValuedBase F (Q i)) := by
  apply valuedPoset_ext_values
  · funext p
    exact F.map_iInf _
  · funext p q
    exact F.map_iInf _
  · rfl

noncomputable def actualSurvivorOldDomainProduct (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) :=
  let b := wetzelGroundNext a
  rowProductQ (fun r : s => supportedSymbolicQ (actualWorkingInputs b).site
    (actualWetzelRowPalette b r.val) (WorkingDomain a))

theorem actualSurvivorOldDomainProduct_eq (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) :
    changeValuedBase (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le)
      (actualSurvivorProduct a s) = actualSurvivorOldDomainProduct a s := by
  let b := wetzelGroundNext a
  let hab : a≤b := ((wetzelGroundNext_spec a a).mpr le_rfl).le
  let F := actualHistoryShift hab
  have hS (j : GroundContinuumSuccIndex) (hj : j<a) :
      ((actualWorkingInputs a).site j).map F = (actualWorkingInputs b).site j :=
    actualWorkingSite_transport hab hj
  have hH (r j : GroundContinuumSuccIndex) (hj : j<a) (n : ℕ) :
      (actualWetzelRowPalette a r j n).map F = actualWetzelRowPalette b r j n :=
    actualWetzelRowPalette_transport hab hj r n
  have hr (r : GroundContinuumSuccIndex) :
      changeValuedBase F (actualSurvivorRow a r) = supportedSymbolicQ
        (actualWorkingInputs b).site (actualWetzelRowPalette b r) (WorkingDomain a) := by
    apply valuedPoset_ext_values
    · funext p
      exact symbolicLabel_partial_map F _ _ _ _ hS (hH r) p.val p.2
    · funext p q
      exact symbolicLabel_refines_partial_map F _ _ _ _ hS (hH r) p.val q.val p.2 q.2
    · rfl
  change changeValuedBase F (rowProductQ (fun r : s => actualSurvivorRow a r.val)) = _
  rw [change_rowProduct930]
  unfold actualSurvivorOldDomainProduct
  exact congrArg (fun F => rowProductQ F) (funext fun r => hr r.val)

theorem actualWorkingSuccessor_projectedCCC (a : GroundContinuumSuccIndex)
    (hPrev : ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project)
    (hA : ForcesRelativeCCC ((actualWorkingInputs a).row a)) :
    ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail
      (wetzel_bot_lt_work (wetzelGroundNext a))).project :=
  nativeWetzelWork_successor_projectedCCC actualWetzelTail (wetzel_bot_lt_work a) (wetzelWork_next a)
    (actualWorkingInputs a).site (actualWorkingInputs a).palette (WorkingDomain a)
    (actualWetzelTail_stageValues a) hPrev (actualWorkingPrefix_boundsOmegaOne a hPrev) hA

theorem actualWorkingSuccessor_survivorsOldCCC (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex)
    (hPrev : ProjectedAntichainCCC (prefixMaskRealization actualWetzelTail (wetzel_bot_lt_work a)).project)
    (hA : ForcesRelativeCCC ((actualWorkingInputs a).row a)) (ha : a∉s)
    (hJ : ForcesRelativeCCC (actualSurvivorProduct a (insert a s))) :
    ForcesRelativeCCC (actualSurvivorOldDomainProduct a s) :=
  (actualSurvivorOldDomainProduct_eq a s) ▸
    actualRelativeCCC_after_work_oldBase a s hPrev hA (actualSurvivingRows_factorCCC a s ha hJ)

end JSP000930.Negative
