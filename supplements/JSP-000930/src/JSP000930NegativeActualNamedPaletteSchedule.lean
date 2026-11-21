import JSP000930NegativeFinalWorkingTaylor
import JSP000930NegativeNamedPaletteScheduleCardinals

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Negative.Cohen JSP000930.MixedPalettes
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing

noncomputable def finalPurePalette930 (j : GroundContinuumSuccIndex) (r : OmegaOneIndex) (n : ℕ) :
    bSet ActualWetzelFinalBA930 :=
  ((createdWetzelPurePalette j r n).map
    (wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext j))).name

theorem finalStagePalette_cover930 {a j : GroundContinuumSuccIndex} (hj : j<a) (n : ℕ) :
    (⊤ : ActualWetzelFinalBA930) ≤
      ⨆ r : OmegaOneIndex,(finalStagePalette930 a j n).name =ᴮ finalPurePalette930 j r n := by
  let F := wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext j)
  let G := composeCompleteValueMaps (createdCohenToHistory j) F
  let M := actualWorkPaletteLabel j a
  have hPast : (finalStagePalette930 a j n) = ((actualMixedPalette M n).map G) := by
    have hj' : j < wetzelGroundNext a := (wetzelGroundNext_spec a j).mpr hj.le
    unfold finalStagePalette930
    rw [actualWetzelRowPalette_eq_map hj']
    apply (actualHistoryShift_thenWhole_bits930 (wetzelGroundNext_le_of_lt hj')
      (createdWetzelMixedPalette j a n)).trans
    rfl
  have hWeights :
      (⨆ r : OmegaOneIndex,G.toFun ((stageCohenMap _).toFun (M.value r))) = (⊤ : ActualWetzelFinalBA930) := by
    rw [← G.map_iSup,← (stageCohenMap _).map_iSup,M.covers,(stageCohenMap _).map_top,G.map_top]
  rw [← hWeights]
  apply iSup_le
  intro r
  apply le_iSup_of_le r
  rw [hPast]
  exact transported_actualMixedPalette_eq_on M n r G

theorem finalFunctionTaylor_pure_palette930 (hB : AllPriorBounds930)
    {i j : GroundContinuumSuccIndex} (hj : j < i) :
    (⊤ : ActualWetzelFinalBA930) ≤ ⨆ r : OmegaOneIndex,⨆ n : ℕ,
      (taylorLimitBits (finalFunctionTaylorCoeffs930 hB i) (nativeWetzelFinalSite actualWetzelRest j)).name
        =ᴮ finalPurePalette930 j r n := by
  let a := wetzelFunctionStage i
  let w := (taylorLimitBits (finalFunctionTaylorCoeffs930 hB i)
    (nativeWetzelFinalSite actualWetzelRest j)).name
  have ha : j<a := hj.trans_le (le_wetzelFunctionStage i)
  have hm := finalStageTaylor_palette930 hB ha
  apply hm.trans
  apply iSup_le
  intro n
  let p := w =ᴮ (finalStagePalette930 a j n).name
  change p ≤ _
  apply (le_inf le_rfl (le_top.trans (finalStagePalette_cover930 ha n))).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro r
  exact le_iSup_of_le r (le_iSup_of_le n (bSet.bv_trans inf_le_left inf_le_right))

theorem finalFunctionTaylor_coeff_readback930 (hB : AllPriorBounds930)
    (i : GroundContinuumSuccIndex) :
    complexCoeffBits (finalFunctionTaylorBits930 hB i) = finalFunctionTaylorCoeffs930 hB i := by
  funext n
  change (⟨(finalFunctionTaylorCoeffs930 hB i n).re,
    (finalFunctionTaylorCoeffs930 hB i n).im⟩ : ComplexBits ActualWetzelFinalBA930) =
      finalFunctionTaylorCoeffs930 hB i n
  generalize finalFunctionTaylorCoeffs930 hB i n = a
  cases a
  rfl

noncomputable def actualNamedPaletteSchedule930 (hB : AllPriorBounds930)
    (hF : ForcesRelativeCCC (nativeWetzelWholeQ actualWetzelRest)) :
    NamedPaletteSchedule ActualWetzelFinalBA930 where
  code := finalFunctionTaylorBits930 hB
  site := nativeWetzelFinalSite actualWetzelRest
  palette := finalPurePalette930
  codeCut i n := by
    rw [finalFunctionTaylor_coeff_readback930]
    exact finalStageTaylorCoeffs_proper930 hB _ n
  codeGrowth i := by
    rw [finalFunctionTaylor_coeff_readback930]
    exact finalStageTaylorCoeffs_growth930 hB _
  siteCutOn := nativeWetzelFinalSite_proper actualWetzelRest
  codeApart i j hij := by
    rcases lt_or_gt_of_ne hij with h | h
    · rw [bSet.bv_eq_symm]
      exact compl_eq_top.mp (top_unique (finalFunctionTaylor_apart930 hB h))
    · exact compl_eq_top.mp (top_unique (finalFunctionTaylor_apart930 hB h))
  sitesCover z p hp := nativeWetzelFinalSite_covers actualWetzelRest hB hF z p hp
  late i j hj := by
    rw [finalFunctionTaylor_coeff_readback930]
    exact finalFunctionTaylor_pure_palette930 hB hj

end JSP000930.Negative
