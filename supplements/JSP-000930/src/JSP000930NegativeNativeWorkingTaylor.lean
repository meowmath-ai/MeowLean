import JSP000930NegativeSupportedRowEmbedding
import JSP000930NegativeActualTowerPaletteValues
import JSP000930NegativeTransportedMixedPalette
import JSP000930NegativeFineTowerApartTransport
import JSP000930ActualLiveSiteNames

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Negative.Cohen
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA

abbrev WorkSiteIndex930 (a : GroundContinuumSuccIndex) := AllowedPin (WorkingDomain a)
abbrev WorkPriorBounds930 (a : GroundContinuumSuccIndex) :=
  ∀ j<a,BoundsSmallKappaNames (ActualWorkBA j)
noncomputable abbrev workSites930 (a : GroundContinuumSuccIndex) : WorkSiteIndex930 a → ComplexBits (ActualWorkBA a) :=
  allowedSite930 (actualWorkingInputs a).site
noncomputable abbrev workPalettes930 (a : GroundContinuumSuccIndex) :
    WorkSiteIndex930 a → ℕ → ComplexBits (ActualWorkBA a) :=
  allowedPalette930 (actualWorkingInputs a).palette
abbrev WorkRawBA930 (a : GroundContinuumSuccIndex) := TotalBA (polynomialQ (workSites930 a) (workPalettes930 a))

theorem workSites_proper930 (a : GroundContinuumSuccIndex) (i : WorkSiteIndex930 a) :
    (workSites930 a i).CutOn ⊤ := actualWorkingSite_proper a i.val

theorem workPalettes_proper930 (a : GroundContinuumSuccIndex) (i : WorkSiteIndex930 a) (n : ℕ) :
    (workPalettes930 a i n).CutOn ⊤ := by
  change ((actualWorkingInputs a).palette i.val n).CutOn ⊤
  rw [actualWorkingInputs_palette_eq]
  exact actualWetzelRowPalette_proper a a i.val n

theorem workSites_apart930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a)
    (i j : WorkSiteIndex930 a) (hij : i≠j) :
    (⊤ : ActualWorkBA a) ≤ ((workSites930 a i).name =ᴮ (workSites930 a j).name)ᶜ := by
  have he := actualWorkingSite_supportApart a hb i.property j.property (fun h => hij (Subtype.ext h))
  change (⊤ : ActualWorkBA a) ≤
    (((actualWorkingInputs a).site i.val).name =ᴮ ((actualWorkingInputs a).site j.val).name)ᶜ
  rw [he,compl_bot]

theorem workPalettes_avoiding930 (a : GroundContinuumSuccIndex) (i : WorkSiteIndex930 a) :
    AvoidingPalette (workPalettes930 a i) := by
  let j := i.val
  let F := composeCompleteValueMaps (createdCohenToHistory j)
    (actualHistoryShift (wetzelGroundNext_le_of_lt i.property))
  have he (n : ℕ) :
      workPalettes930 a i n = (actualMixedPalette (actualWorkPaletteLabel j a) n).map F := by
    change (actualWorkingInputs a).palette j n = _
    rw [actualWorkingInputs_palette_eq,actualWetzelRowPalette_eq_map i.property,
      createdWetzelMixedPalette,mapComplexBits_comp930] <;> rfl
  rw [funext he]
  exact transported_actualMixedPalette_avoiding (actualWorkPaletteLabel j a) F

theorem workPalettes_dense930 (a : GroundContinuumSuccIndex) (i : WorkSiteIndex930 a) :
    DensePalette (workPalettes930 a i) := avoidingPalette_dense (workPalettes_avoiding930 a i)

noncomputable def workRawToRow930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a) :
    CompleteValueMap (WorkRawBA930 a) (TotalBA ((actualWorkingInputs a).row a)) :=
  supportedRawToSymbolic930 (A := WorkingDomain a) (actualWorkingInputs a).site
    (actualWorkingInputs a).palette (workSites_proper930 a) (workPalettes_proper930 a) (workSites_apart930 a hb)

noncomputable def workRawToNext930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a) :
    CompleteValueMap (WorkRawBA930 a) (ActualWorkBA (wetzelGroundNext a)) :=
  composeCompleteValueMaps
    (composeCompleteValueMaps (workRawToRow930 a hb) (stageCohenMap _))
    (createdCohenToHistory a)

theorem workRawToNext930_base (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a)
    (b : ActualWorkBA a) :
    (workRawToNext930 a hb).toFun
      ((polynomialBaseValueMap (workSites930 a) (workPalettes930 a)).toFun b) =
      (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le).toFun b := by
  let W := actualWorkingInputs a
  let P := polynomialBaseValueMap (workSites930 a) (workPalettes930 a)
  change (createdCohenToHistory a).toFun ((stageCohenMap _).toFun
      ((workRawToRow930 a hb).toFun (P.toFun b))) = _
  have he := supportedRawToSymbolic930_base (A := WorkingDomain a) W.site W.palette
      (workSites_proper930 a) (workPalettes_proper930 a) (workSites_apart930 a hb) b
  change (workRawToRow930 a hb).toFun (P.toFun b) = baseEmbed (W.row a) b at he
  rw [he]
  exact createdCohenToHistory_base a b

noncomputable def rawWorkCoeffs930 (a : GroundContinuumSuccIndex) : ℕ → ComplexBits (WorkRawBA930 a) :=
  (actualFinePolynomialTower (workSites930 a) (workPalettes930 a)).limitCoefficients

noncomputable def actualCreatedTaylorCoeffs930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a) :
    ℕ → ComplexBits (ActualWorkBA (wetzelGroundNext a)) :=
  fun n => (rawWorkCoeffs930 a n).map (workRawToNext930 a hb)

theorem actualCreatedTaylorCoeffs_proper930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a) :
    ∀ n,(actualCreatedTaylorCoeffs930 a hb n).CutOn ⊤ := by
  intro n
  let T := actualFinePolynomialTower (workSites930 a) (workPalettes930 a)
  have ht := T.limit_coeff_proper ⊤ (actualFinePolynomialTower_on (workSites930 a) (workPalettes930 a)) n
  change ((T.limitCoefficients n).map (workRawToNext930 a hb)).CutOn ⊤
  simpa only [(workRawToNext930 a hb).map_top] using ComplexBits.map_cutOn (workRawToNext930 a hb) ht

theorem actualCreatedTaylorCoeffs_growth930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a) :
    GrowthOn ⊤ (actualCreatedTaylorCoeffs930 a hb) := by
  let T := actualFinePolynomialTower (workSites930 a) (workPalettes930 a)
  have ht := T.limitGrowth ⊤ (actualFinePolynomialTower_on (workSites930 a) (workPalettes930 a))
  change GrowthOn ⊤ (fun n => (T.limitCoefficients n).map (workRawToNext930 a hb))
  simpa only [(workRawToNext930 a hb).map_top] using ht.map (workRawToNext930 a hb)

end JSP000930.Negative
