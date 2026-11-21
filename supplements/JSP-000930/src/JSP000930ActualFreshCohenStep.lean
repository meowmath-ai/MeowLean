import JSP000930ActualBeforeFreshCohen

open bSet
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Negative.Cohen
open JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.BooleanCompletion JSP000933.MarkedForcing
open JSP000933.ForcingTransport JSP000933.RelativeOCA

noncomputable def freshCohenTest (a : GroundContinuumSuccIndex) (s : Finset GroundContinuumSuccIndex) :=
  LaterAnalyticProduct (beforeFreshSite a) (beforeFreshPalette a s)
    (fun r : s => actualWorkPaletteLabel a r.val) (WorkingDomain a) a

theorem actualWorkSite_map_until_self (a j : GroundContinuumSuccIndex) (h : j≤a) :
    mapComplexBits (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le)
      ((actualWorkingInputs a).site j) = (actualWorkingInputs (wetzelGroundNext a)).site j := by
  rcases lt_or_eq_of_le h with hj|he
  · exact actualWorkingSite_transport _ hj
  · subst j
    exact (actualWorkingSite_at_new a).symm

theorem beforeFreshApart (a : GroundContinuumSuccIndex)
    (hB : ∀ j≤a,BoundsSmallKappaNames (ActualWorkBA j))
    (i j : GroundContinuumSuccIndex) (hi : i≤a) (hj : j≤a) (hne : i≠j) :
    ((beforeFreshSite a i).name =ᴮ (beforeFreshSite a j).name) = ⊥ := by
  let b := wetzelGroundNext a
  let G := actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le
  have h0 : (((actualWorkingInputs a).site i).name =ᴮ
      ((actualWorkingInputs a).site j).name) = ⊥ := by
    apply G.injective
    rw [← mapComplexBits_eqTruth930 G,G.map_bot,actualWorkSite_map_until_self a i hi,
      actualWorkSite_map_until_self a j hj]
    exact actualWorkingSite_supportApart b (fun k hk => hB k ((wetzelGroundNext_spec a k).mp hk))
      ((wetzelGroundNext_spec a i).mpr hi) ((wetzelGroundNext_spec a j).mpr hj) hne
  change ((mapComplexBits (actualWorkRowMap a) ((actualWorkingInputs a).site i)).name =ᴮ
    (mapComplexBits (actualWorkRowMap a) ((actualWorkingInputs a).site j)).name) = ⊥
  rw [mapComplexBits_eqTruth930,h0,(actualWorkRowMap a).map_bot]

noncomputable def realFreshCohenMap (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA) :
    MaskedCondition (beforeFreshCohenTest a s) ((actualWorkPreparedAfterRow a).toFun u) →
      MaskedCondition (freshCohenTest a s)
        ((stageCohenMap (LiveRowModel a)).toFun ((actualWorkPreparedAfterRow a).toFun u)) :=
  actualCohenSuccessorInsideMap (beforeFreshSite a) (beforeFreshPalette a s)
    (fun r : s => actualWorkPaletteLabel a r.val) (WorkingDomain a) a (lt_irrefl a)
    ((actualWorkPreparedAfterRow a).toFun u)

theorem realFreshCohenMap_mono (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA) :
    Monotone (realFreshCohenMap a s u) := by
  intro p q h
  let F := stageCohenMap (LiveRowModel a)
  let z := actualCohenSuccessorMap (beforeFreshSite a) (beforeFreshPalette a s)
    (fun r : s => actualWorkPaletteLabel a r.val) (WorkingDomain a) a (lt_irrefl a)
  change z p.val ≤ z q.val
  unfold z actualCohenSuccessorMap
  exact (includeAnalyticProductCondition_le_iff _ F _ _ _ _ _ _ p.val q.val).mpr h

theorem realFreshCohenMap_predense (a : GroundContinuumSuccIndex)
    (s : Finset GroundContinuumSuccIndex) (u : PreparedBA)
    (hSep : ∀ i j : s,i≠j → u ≤ (labelAgreement (preparedWetzelRows i.val a) (preparedWetzelRows j.val a))ᶜ)
    (hB : ∀ j≤a,BoundsSmallKappaNames (ActualWorkBA j)) :
    PreservesPredensity (realFreshCohenMap a s u) := by
  apply actualCohenSuccessorInsideMap_predensity
  · intro i j h
    exact actualWork_mark_separatesPalette (hSep i j h)
  · intro j
    have h := properSite_map (actualWorkRowMap a) ((actualWorkingInputs a).site j) (actualWorkingSite_proper a j)
    rwa [(actualWorkRowMap a).map_top] at h
  · intro r j _ n
    have h := properSite_map (actualWorkRowMap a) (actualWetzelRowPalette a r.val j n)
      (actualWetzelRowPalette_proper a r.val j n)
    rwa [(actualWorkRowMap a).map_top] at h
  · intro j hj k hk hne
    have hj' : j≤a := hj.elim (fun hl => hl.le) (fun he => he.le)
    have hk' : k≤a := hk.elim (fun hl => hl.le) (fun he => he.le)
    rw [beforeFreshApart a hB j k hj' hk' hne,compl_bot] <;> exact le_rfl

end JSP000930.Negative
