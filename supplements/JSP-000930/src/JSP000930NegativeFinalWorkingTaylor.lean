import JSP000930NegativeNativeWorkingTaylorOutputs

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.AnalyticSyntax JSP000930.Positive
open JSP000933.PreparedModel JSP000933.RelativeOCA JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.SetLanguage

abbrev ActualWetzelFinalBA930 := TotalBA (nativeWetzelWholeQ actualWetzelRest)
abbrev AllPriorBounds930 := ∀ j : GroundContinuumSuccIndex,BoundsSmallKappaNames (ActualWorkBA j)

noncomputable def finalStageTaylorCoeffs930 (hB : AllPriorBounds930)
    (a : GroundContinuumSuccIndex) : ℕ → ComplexBits ActualWetzelFinalBA930 :=
  fun n => (actualCreatedTaylorCoeffs930 a (fun j _ => hB j) n).map
    (wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext a))

theorem finalStageTaylorCoeffs_proper930 (hB : AllPriorBounds930) (a : GroundContinuumSuccIndex) :
    ∀ n,(finalStageTaylorCoeffs930 hB a n).CutOn ⊤ := by
  intro n
  let F := wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext a)
  change ((actualCreatedTaylorCoeffs930 a (fun j _ => hB j) n).map F).CutOn ⊤
  simpa only [F.map_top] using ComplexBits.map_cutOn F
    (actualCreatedTaylorCoeffs_proper930 a (fun j _ => hB j) n)

theorem finalStageTaylorCoeffs_growth930 (hB : AllPriorBounds930) (a : GroundContinuumSuccIndex) :
    GrowthOn ⊤ (finalStageTaylorCoeffs930 hB a) := by
  let F := wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext a)
  change GrowthOn ⊤ (fun n => (actualCreatedTaylorCoeffs930 a (fun j _ => hB j) n).map F)
  simpa only [F.map_top] using
    (actualCreatedTaylorCoeffs_growth930 a (fun j _ => hB j)).map F

theorem actualHistoryShift_thenWhole_bits930 {a b : GroundContinuumSuccIndex} (hab : a≤b)
    (z : ComplexBits (ActualWorkBA a)) :
    (z.map (actualHistoryShift hab)).map (wetzelHistoryToWhole actualWetzelRest b) =
      z.map (wetzelHistoryToWhole actualWetzelRest a) := by
  cases z with
  | mk x y =>
    exact congrArg₂ ComplexBits.mk
      (funext fun q => wetzelHistoryToWhole_commutes actualWetzelRest hab (x q))
      (funext fun q => wetzelHistoryToWhole_commutes actualWetzelRest hab (y q))

theorem finalStageTaylor_apart930 (hB : AllPriorBounds930) {a b : GroundContinuumSuccIndex} (hab : a<b)
    [Infinite (WorkSiteIndex930 b)] :
    (⊤ : ActualWetzelFinalBA930) ≤
      (codeNameOfComplexBits (finalStageTaylorCoeffs930 hB b) =ᴮ
        codeNameOfComplexBits (finalStageTaylorCoeffs930 hB a))ᶜ := by
  let h₀ := wetzelGroundNext_le_of_lt hab
  let h₁ := ((wetzelGroundNext_spec b b).mpr le_rfl).le
  let G := actualHistoryShift h₀
  let H := actualHistoryShift h₁
  let F := wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext b)
  let u := actualCreatedTaylorCoeffs930 a (fun j _ => hB j)
  let v := fun n => (u n).map G
  have hv (n : ℕ) : (v n).CutOn ⊤ := by
    simpa only [G.map_top] using ComplexBits.map_cutOn G
      (actualCreatedTaylorCoeffs_proper930 a (fun j _ => hB j) n)
  have hg : GrowthOn ⊤ v := by
    simpa only [G.map_top] using (actualCreatedTaylorCoeffs_growth930 a (fun j _ => hB j)).map G
  have hn := actualCreatedTaylor_fresh930 b (fun j _ => hB j) v hv hg
  have h := map_mixed_taylor_code_apart F (actualCreatedTaylorCoeffs930 b (fun j _ => hB j))
    (fun n => (v n).map H) ⊤ hn
  have he (n : ℕ) : (((v n).map H).map F) = (u n).map (wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext a)) := by
    rw [actualHistoryShift_thenWhole_bits930 h₁,actualHistoryShift_thenWhole_bits930 h₀]
  have hfun : (fun n => (((v n).map H).map F)) = finalStageTaylorCoeffs930 hB a := funext he
  change (⊤ : ActualWetzelFinalBA930) ≤
    (codeNameOfComplexBits (fun n => (actualCreatedTaylorCoeffs930 b (fun j _ => hB j) n).map F) =ᴮ
      codeNameOfComplexBits (finalStageTaylorCoeffs930 hB a))ᶜ
  simpa only [F.map_top,transportedTaylorCode,hfun] using h

noncomputable def finalStagePalette930 (a j : GroundContinuumSuccIndex) (n : ℕ) :
    ComplexBits ActualWetzelFinalBA930 :=
  (actualWetzelRowPalette (wetzelGroundNext a) a j n).map
    (wetzelHistoryToWhole actualWetzelRest (wetzelGroundNext a))

theorem finalStageTaylor_palette930 (hB : AllPriorBounds930) {a j : GroundContinuumSuccIndex} (hj : j<a) :
    (⊤ : ActualWetzelFinalBA930) ≤ ⨆ n : ℕ,
      (taylorLimitBits (finalStageTaylorCoeffs930 hB a) (nativeWetzelFinalSite actualWetzelRest j)).name =ᴮ
      (finalStagePalette930 a j n).name := by
  let b := wetzelGroundNext a
  let F := wetzelHistoryToWhole actualWetzelRest b
  have hjb : j<b := (wetzelGroundNext_spec a j).mpr hj.le
  have h := actualCreatedTaylor_palette930 a (fun j _ => hB j) ⟨j,hj⟩
  have hz : ((actualWorkingInputs b).site j).map F = nativeWetzelFinalSite actualWetzelRest j :=
    actualWorkingSite_maps_final hjb
  exact transport_taylor_palette F (actualCreatedTaylorCoeffs930 a (fun j _ => hB j))
    ((actualWorkingInputs b).site j) (actualWetzelRowPalette b a j) h
    (finalStageTaylorCoeffs930 hB a) (nativeWetzelFinalSite actualWetzelRest j)
    (finalStagePalette930 a j) rfl hz rfl

noncomputable def finalFunctionTaylorCoeffs930 (hB : AllPriorBounds930) (i : GroundContinuumSuccIndex) :=
  finalStageTaylorCoeffs930 hB (wetzelFunctionStage i)

noncomputable def finalFunctionTaylorBits930 (hB : AllPriorBounds930) (i : GroundContinuumSuccIndex) :
    TaylorSlot → ActualWetzelFinalBA930 :=
  codeBitsOfComplexBits (finalFunctionTaylorCoeffs930 hB i)

theorem finalFunctionTaylor_apart930 (hB : AllPriorBounds930)
    {i j : GroundContinuumSuccIndex} (hij : i<j) :
    (⊤ : ActualWetzelFinalBA930) ≤
      (taylorCodeName (finalFunctionTaylorBits930 hB j) =ᴮ
       taylorCodeName (finalFunctionTaylorBits930 hB i))ᶜ := by
  letI : Infinite (WorkSiteIndex930 (wetzelFunctionStage j)) := infinite_oldSites_functionStage j
  exact finalStageTaylor_apart930 hB (wetzelFunctionStage_strictMono hij)

theorem finalFunctionTaylor_forces_entire930 (hB : AllPriorBounds930)
    (i : GroundContinuumSuccIndex) {n : ℕ} (v : DVec (V ActualWetzelFinalBA930) n) (A : STerm n)
    (hA : bTerm v A = taylorCodeName (finalFunctionTaylorBits930 hB i)) :
    (⊤ : ActualWetzelFinalBA930) ≤ bTruth v (isEntireCode_f A) :=
  codeNameOfComplexBits_forces_entire v A _ ⊤ hA
    (finalStageTaylorCoeffs_proper930 hB (wetzelFunctionStage i))
    (finalStageTaylorCoeffs_growth930 hB (wetzelFunctionStage i))

theorem finalFunctionTaylor_literal_palette930 (hB : AllPriorBounds930)
    (i j : GroundContinuumSuccIndex) (hj : j < wetzelFunctionStage i)
    {n : ℕ} (v : DVec (V ActualWetzelFinalBA930) n) (A Z Y : STerm n)
    (hA : bTerm v A = taylorCodeName (finalFunctionTaylorBits930 hB i))
    (hZ : bTerm v Z = (nativeWetzelFinalSite actualWetzelRest j).name)
    (p : ActualWetzelFinalBA930) (hEval : p ≤ bTruth v (evalAt_f A Z Y)) :
    p ≤ ⨆ k : ℕ,bTerm v Y =ᴮ (finalStagePalette930 (wetzelFunctionStage i) j k).name := by
  let f := finalFunctionTaylorCoeffs930 hB i
  let z := nativeWetzelFinalSite actualWetzelRest j
  have hE : p ≤ bTerm v Y =ᴮ (taylorLimitBits f z).name :=
    (codeNameOfComplexBits_eval_iff v A Z Y f z p hA hZ
      (fun k => cutOn_mono930 (finalStageTaylorCoeffs_proper930 hB _ k) le_top)
      ((finalStageTaylorCoeffs_growth930 hB _).mono le_top)
      (cutOn_mono930 (nativeWetzelFinalSite_proper actualWetzelRest j) le_top)).mp hEval
  have hPal := (show p ≤ ⊤ from le_top).trans (finalStageTaylor_palette930 hB hj)
  apply (le_inf hE hPal).trans
  rw [inf_iSup_eq]
  exact iSup_le fun k => le_iSup_of_le k (bSet.bv_trans inf_le_left inf_le_right)

end JSP000930.Negative
