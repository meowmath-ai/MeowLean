import JSP000930NegativePolynomialActualPin

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.BooleanCompletion

variable {B C : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem map_roundedLiminfBits (F : CompleteValueMap B C)
    (u : ℕ → RatPresentation → B) (q : RatPresentation) :
    F.toFun (roundedLiminfBits u q) = roundedLiminfBits (fun n r => F.toFun (u n r)) q := by
  simp only [roundedLiminfBits,F.map_iSup,F.map_iInf,map_iSup_prop930]

theorem ComplexBits.map_power (F : CompleteValueMap B C) (z : ComplexBits B) (n : ℕ) :
    (z.power n).map F = (z.map F).power n := by
  induction n with
  | zero => exact ComplexBits.map_ofNat F 1
  | succ n ih =>
    simp only [ComplexBits.power,ComplexBits.map_mul,ih]

theorem map_taylorPrefixBits (F : CompleteValueMap B C)
    (a : ℕ → ComplexBits B) (z : ComplexBits B) (n : ℕ) :
    (taylorPrefixBits a z n).map F = taylorPrefixBits (fun n => (a n).map F) (z.map F) n := by
  induction n with
  | zero => exact ComplexBits.map_ofNat F 0
  | succ n ih =>
    simp only [taylorPrefixBits,ComplexBits.map_add,ComplexBits.map_mul,ComplexBits.map_power,ih]

theorem map_taylorLimitBits (F : CompleteValueMap B C)
    (a : ℕ → ComplexBits B) (z : ComplexBits B) :
    (taylorLimitBits a z).map F = taylorLimitBits (fun n => (a n).map F) (z.map F) := by
  let d := fun n => (a n).map F
  let x := z.map F
  change (⟨mapCut F (roundedLiminfBits (fun n => (taylorPrefixBits a z n).re)),
    mapCut F (roundedLiminfBits (fun n => (taylorPrefixBits a z n).im))⟩ : ComplexBits C) =
      ⟨roundedLiminfBits (fun n => (taylorPrefixBits d x n).re),
       roundedLiminfBits (fun n => (taylorPrefixBits d x n).im)⟩
  have hR : mapCut F (roundedLiminfBits (fun n => (taylorPrefixBits a z n).re)) =
      roundedLiminfBits (fun n => (taylorPrefixBits d x n).re) := by
    funext q
    change F.toFun (roundedLiminfBits (fun n => (taylorPrefixBits a z n).re) q) = _
    rw [map_roundedLiminfBits]
    have h : (fun n (r : RatPresentation) => F.toFun ((taylorPrefixBits a z n).re r)) =
        fun n => (taylorPrefixBits d x n).re := by
      funext n
      exact congrArg ComplexBits.re (map_taylorPrefixBits F a z n)
    rw [h]
  have hI : mapCut F (roundedLiminfBits (fun n => (taylorPrefixBits a z n).im)) =
      roundedLiminfBits (fun n => (taylorPrefixBits d x n).im) := by
    funext q
    change F.toFun (roundedLiminfBits (fun n => (taylorPrefixBits a z n).im) q) = _
    rw [map_roundedLiminfBits]
    have h : (fun n (r : RatPresentation) => F.toFun ((taylorPrefixBits a z n).im r)) =
        fun n => (taylorPrefixBits d x n).im := by
      funext n
      exact congrArg ComplexBits.im (map_taylorPrefixBits F a z n)
    rw [h]
  rw [hR,hI]

theorem map_radiusBudgetBits (F : CompleteValueMap B C) (a : ComplexBits B) (R K n : ℕ) :
    F.toFun (radiusBudgetBits a R K n) = radiusBudgetBits (a.map F) R K n := by
  simp only [radiusBudgetBits,map_weightedCut_subset,mapCut_mul,
    ComplexBits.map_normSq,mapCut_checked]

theorem GrowthOn.map (F : CompleteValueMap B C) {a : ℕ → ComplexBits B} {p : B}
    (h : GrowthOn p a) : GrowthOn (F.toFun p) (fun n => (a n).map F) := by
  intro R hR
  have h' := F.monotone (h R hR)
  simpa only [F.map_iSup,F.map_iInf,map_radiusBudgetBits] using h'

theorem map_taylorValue_name_eq (F : CompleteValueMap B C) {a : ℕ → ComplexBits B}
    {z y : ComplexBits B} {p : B}
    (h : p ≤ (taylorLimitBits a z).name =ᴮ y.name) :
    F.toFun p ≤ (taylorLimitBits (fun n => (a n).map F) (z.map F)).name =ᴮ (y.map F).name := by
  have h' := F.monotone h
  simpa only [ComplexBits.map_nameEq,map_taylorLimitBits] using h'

theorem map_taylorValue_eqTruth (F : CompleteValueMap B C)
    (a d : ℕ → ComplexBits B) (z w : ComplexBits B) :
    F.toFun ((taylorLimitBits a z).name =ᴮ (taylorLimitBits d w).name) =
      ((taylorLimitBits (fun n => (a n).map F) (z.map F)).name =ᴮ
        (taylorLimitBits (fun n => (d n).map F) (w.map F)).name) := by
  simp only [ComplexBits.map_nameEq,map_taylorLimitBits]

theorem map_taylorValue_apart (F : CompleteValueMap B C) {a d : ℕ → ComplexBits B}
    {z w : ComplexBits B} {p : B}
    (h : p ≤ ((taylorLimitBits a z).name =ᴮ (taylorLimitBits d w).name)ᶜ) :
    F.toFun p ≤
      ((taylorLimitBits (fun n => (a n).map F) (z.map F)).name =ᴮ
        (taylorLimitBits (fun n => (d n).map F) (w.map F)).name)ᶜ := by
  simpa only [F.map_compl,map_taylorValue_eqTruth] using F.monotone h

end JSP000930.BooleanAnalysis
