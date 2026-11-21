import JSP000930ActualSurvivorOldDomain

open bSet
open scoped bSet Flypitch

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Negative.Cohen
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

theorem actualWorkingSite_proper (a j : GroundContinuumSuccIndex) :
    ((actualWorkingInputs a).site j).CutOn ⊤ := by
  rw [actualWorkingInputs_site_eq]
  exact workingSiteAt_proper a _ j

theorem actualWetzelRowPalette_proper (a r j : GroundContinuumSuccIndex) (n : ℕ) :
    (actualWetzelRowPalette a r j n).CutOn ⊤ := by
  classical
  by_cases hj : j<a
  · rw [actualWetzelRowPalette_eq_map hj,createdWetzelMixedPalette,mapComplexBits_comp930]
    let F := composeCompleteValueMaps (createdCohenToHistory j) (actualHistoryShift (wetzelGroundNext_le_of_lt hj))
    have h := properSite_map F (actualMixedPalette (actualWorkPaletteLabel j r) n)
      (actualMixedPalette_cutOn (actualWorkPaletteLabel j r) n)
    rwa [F.map_top] at h
  · simp only [actualWetzelRowPalette,historyPaletteAt,dite_eq_right hj]
    exact ComplexBits.checked_cutOn 0 ⊤

theorem actualWorkingSite_maps_final {a j : GroundContinuumSuccIndex} (hj : j<a) :
    mapComplexBits (wetzelHistoryToWhole actualWetzelRest a) ((actualWorkingInputs a).site j) =
      nativeWetzelFinalSite actualWetzelRest j := by
  rw [actualWorkingInputs_site_eq,workingSiteAt_of_lt _ hj
    (earlierHistory_persistent_r131 actualWetzelPolicy _)]
  exact nativeWetzelFinalSite_eq_earlier actualWetzelRest a ⟨j,hj⟩

theorem actualWorkingSite_supportApart (a : GroundContinuumSuccIndex)
    (hB : ∀ j<a,BoundsSmallKappaNames (ActualWorkBA j))
    {i j : GroundContinuumSuccIndex} (hi : i<a) (hj : j<a) (hij : i≠j) :
    (((actualWorkingInputs a).site i).name =ᴮ ((actualWorkingInputs a).site j).name) = ⊥ := by
  let F := wetzelHistoryToWhole actualWetzelRest a
  apply F.injective
  rw [← mapComplexBits_eqTruth930 F,F.map_bot,actualWorkingSite_maps_final hi,actualWorkingSite_maps_final hj]
  rcases lt_or_gt_of_ne hij with h|h
  · have ht := nativeWetzelFinalSite_apart_of_lt actualWetzelRest h (hB j hj)
    exact le_bot_iff.mp (bSet.bv_eq_symm.trans_le ht.le)
  · exact nativeWetzelFinalSite_apart_of_lt actualWetzelRest h (hB i hi)

theorem actualChosenRowCCC_of_singleton (a : GroundContinuumSuccIndex)
    (h : ForcesRelativeCCC (actualSurvivorProduct a {a})) :
    ForcesRelativeCCC ((actualWorkingInputs a).row a) := by
  classical
  rw [← actualSurvivorRow_self]
  let I := (↥({a} : Finset GroundContinuumSuccIndex))
  let N := SupportedSymbolic GroundContinuumSuccIndex (WorkingDomain a)
  let i : I := ⟨a,Finset.mem_singleton_self a⟩
  letI : Nonempty I := ⟨i⟩
  have he (j : I) : j=i := Subtype.ext (Finset.mem_singleton.mp j.property)
  let E : N ≃ (I→N) :=
    ⟨fun n _ => n,fun f => f i,fun _ => rfl,fun f => funext fun j => congrArg f (he j).symm⟩
  apply relCCC_of_labelEquiv _ _ E _ _ h
  · intro p
    change (actualSurvivorRow a a).valid p =
      ⨅ j : I,(actualSurvivorRow a j.val).valid p
    have hEq (j : I) : (actualSurvivorRow a j.val).valid p =
        (actualSurvivorRow a a).valid p := by rw [he j]
    simp only [hEq,iInf_const]
  · intro p q
    change (actualSurvivorRow a a).refines p q =
      ⨅ j : I,(actualSurvivorRow a j.val).refines p q
    have hEq (j : I) : (actualSurvivorRow a j.val).refines p q =
        (actualSurvivorRow a a).refines p q := by rw [he j]
    simp only [hEq,iInf_const]

end JSP000930.Negative
