import JSP000930NegativeNativeWorkingTaylor

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive
open JSP000933.PreparedModel JSP000933.FiniteSupport JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing

theorem workRawToNext930_baseBits (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a)
    (z : ComplexBits (ActualWorkBA a)) :
    (z.map (polynomialBaseValueMap (workSites930 a) (workPalettes930 a))).map (workRawToNext930 a hb) =
      z.map (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le) := by
  cases z with
  | mk x y =>
    exact congrArg₂ ComplexBits.mk (funext fun q => workRawToNext930_base a hb (x q))
      (funext fun q => workRawToNext930_base a hb (y q))

theorem workRawToNext930_baseSite (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a)
    (j : WorkSiteIndex930 a) :
    ((workSites930 a j).map (polynomialBaseValueMap (workSites930 a) (workPalettes930 a))).map
      (workRawToNext930 a hb) =
      (actualWorkingInputs (wetzelGroundNext a)).site j.val := by
  rw [workRawToNext930_baseBits]
  exact actualWorkingSite_transport ((wetzelGroundNext_spec a a).mpr le_rfl).le j.property

theorem workRawToNext930_basePalette (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a)
    (j : WorkSiteIndex930 a) (n : ℕ) :
    ((workPalettes930 a j n).map (polynomialBaseValueMap (workSites930 a) (workPalettes930 a))).map
      (workRawToNext930 a hb) =
      actualWetzelRowPalette (wetzelGroundNext a) a j.val n := by
  rw [workRawToNext930_baseBits]
  change ((actualWorkingInputs a).palette j.val n).map _ = _
  rw [actualWorkingInputs_palette_eq]
  exact actualWetzelRowPalette_transport ((wetzelGroundNext_spec a a).mpr le_rfl).le j.property a n

theorem transport_taylor_palette {B C : Type}
    [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
    (F : CompleteValueMap B C) (a : ℕ → ComplexBits B) (z : ComplexBits B)
    (y : ℕ → ComplexBits B) (h : (⊤ : B) ≤ ⨆ n : ℕ, (taylorLimitBits a z).name =ᴮ (y n).name)
    (a' : ℕ → ComplexBits C) (z' : ComplexBits C) (y' : ℕ → ComplexBits C)
    (ha : (fun k => (a k).map F) = a') (hz : z.map F = z')
    (hy : (fun n => (y n).map F) = y') :
    (⊤ : C) ≤ ⨆ n : ℕ, (taylorLimitBits a' z').name =ᴮ (y' n).name := by
  have hm := F.monotone h
  rw [F.map_top,F.map_iSup] at hm
  have he (n : ℕ) : F.toFun ((taylorLimitBits a z).name =ᴮ (y n).name) =
      (taylorLimitBits a' z').name =ᴮ (y' n).name := by
    rw [ComplexBits.map_nameEq, map_taylorLimitBits,ha,hz]
    exact congrArg (fun w : ComplexBits C => (taylorLimitBits a' z').name =ᴮ w.name)
      (congrFun hy n)
  exact hm.trans_eq (iSup_congr he)

theorem actualCreatedTaylor_palette930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a)
    (j : WorkSiteIndex930 a) :
    (⊤ : ActualWorkBA (wetzelGroundNext a)) ≤ ⨆ n : ℕ,
      (taylorLimitBits (actualCreatedTaylorCoeffs930 a hb)
        ((actualWorkingInputs (wetzelGroundNext a)).site j.val)).name =ᴮ
      (actualWetzelRowPalette (wetzelGroundNext a) a j.val n).name := by
  let G := polynomialBaseValueMap (workSites930 a) (workPalettes930 a)
  have h := actualFineTower_palette_top930 (workSites930 a) (workPalettes930 a) j
      (workSites_proper930 a) (workSites_apart930 a hb j) (workPalettes_proper930 a j)
      (workPalettes_dense930 a j)
  exact transport_taylor_palette (workRawToNext930 a hb) (rawWorkCoeffs930 a)
    ((workSites930 a j).map G) (fun n => (workPalettes930 a j n).map G) h
    (actualCreatedTaylorCoeffs930 a hb) ((actualWorkingInputs (wetzelGroundNext a)).site j.val)
    (actualWetzelRowPalette (wetzelGroundNext a) a j.val) rfl
    (workRawToNext930_baseSite a hb j) (funext (workRawToNext930_basePalette a hb j))

theorem actualCreatedTaylor_fresh930 (a : GroundContinuumSuccIndex) (hb : WorkPriorBounds930 a)
    [Infinite (WorkSiteIndex930 a)] (old : ℕ → ComplexBits (ActualWorkBA a))
    (ho : ∀ n,(old n).CutOn ⊤) (hg : GrowthOn ⊤ old) :
    (⊤ : ActualWorkBA (wetzelGroundNext a)) ≤
      (codeNameOfComplexBits (actualCreatedTaylorCoeffs930 a hb) =ᴮ
        codeNameOfComplexBits (fun n =>
          (old n).map (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le)))ᶜ := by
  have h := transportedActualFineTower_apart_old_code (workSites930 a) (workPalettes930 a)
    (workRawToNext930 a hb) (workSites_proper930 a) (workSites_apart930 a hb)
    (workPalettes_proper930 a) (workPalettes_avoiding930 a) old ho hg
  let F := workRawToNext930 a hb
  let G := polynomialBaseValueMap (workSites930 a) (workPalettes930 a)
  have he : transportedTaylorCode F (fun n => (old n).map G) =
      codeNameOfComplexBits (fun n => (old n).map (actualHistoryShift ((wetzelGroundNext_spec a a).mpr le_rfl).le)) :=
    congrArg codeNameOfComplexBits (funext (fun n => workRawToNext930_baseBits a hb (old n)))
  rw [← he]
  exact h

end JSP000930.Negative
