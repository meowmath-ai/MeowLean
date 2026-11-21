import JSP000930PositiveJointBudgetAndConvergenceTests

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure CommonTaylorGroundValues (A D : ℕ → ComplexBits B) (Z : ComplexBits B)
    (m : B) where
  p : ℕ → B
  left : ℕ → ℂ
  right : ℕ → ℂ
  point : ℂ
  yLeft : ℂ
  yRight : ℂ
  antitone : Antitone p
  nonzero : ∀ n,p n ≠ ⊥
  under : ∀ n,p n ≤ m
  leftTrace : ∀ n,ComplexDecisionTrace p (A n) (left n)
  rightTrace : ∀ n,ComplexDecisionTrace p (D n) (right n)
  pointTrace : ComplexDecisionTrace p Z point
  leftValTrace : ComplexDecisionTrace p (taylorLimitBits A Z) yLeft
  rightValTrace : ComplexDecisionTrace p (taylorLimitBits D Z) yRight
  leftRadius : RadiusCode left
  rightRadius : RadiusCode right
  leftEval : evaluate left point = yLeft
  rightEval : evaluate right point = yRight

theorem commonTaylorGroundValues_exists
    (A D : ℕ → ComplexBits B) (Z : ComplexBits B) (m : B) (hm : m ≠ ⊥)
    (hA : ∀ n,(A n).CutOn m) (hD : ∀ n,(D n).CutOn m)
    (hZ : Z.CutOn m) (hGA : GrowthOn m A) (hGD : GrowthOn m D) :
    Nonempty (CommonTaylorGroundValues A D Z m) := by
  let X : Option (Bool × Option ℕ) → ComplexBits B := fun
    | none => Z
    | some (false,none) => taylorLimitBits A Z
    | some (true,none) => taylorLimitBits D Z
    | some (false,some n) => A n
    | some (true,some n) => D n
  have hX (i : Option (Bool × Option ℕ)) : (X i).CutOn m := by
    match i with
    | none => exact hZ
    | some (false,none) => exact taylorLimitBits_cutOn A Z m hA hZ hGA
    | some (true,none) => exact taylorLimitBits_cutOn D Z m hD hZ hGD
    | some (false,some n) => exact hA n
    | some (true,some n) => exact hD n
  let T (k : ℕ) (t : TaylorTraceTest × TaylorTraceTest) : B :=
    t.1.value A Z k ⊓ t.2.value D Z k
  have hT (k : ℕ) : m ≤ ⨆ t : TaylorTraceTest × TaylorTraceTest,T k t :=
    pair_iSup_cover (fun t : TaylorTraceTest => t.value A Z k) (fun t : TaylorTraceTest => t.value D Z k) m
      (taylorTraceTests_cover A Z m hA hZ hGA k) (taylorTraceTests_cover D Z m hD hZ hGD k)
  obtain ⟨p,t,a,hP,hNZ,hpm,hSel,ha⟩ := complex_countable_completion_with_tests X m hm hX T hT
  let left (n : ℕ) := a (some (false,some n))
  let right (n : ℕ) := a (some (true,some n))
  let point := a none
  let yLeft := a (some (false,none))
  let yRight := a (some (true,none))
  have hLeft (n : ℕ) : ComplexDecisionTrace p (A n) (left n) := ha (some (false,some n))
  have hRight (n : ℕ) : ComplexDecisionTrace p (D n) (right n) := ha (some (true,some n))
  have hPoint : ComplexDecisionTrace p Z point := ha none
  have hyL : ComplexDecisionTrace p (taylorLimitBits A Z) yLeft := ha (some (false,none))
  have hyR : ComplexDecisionTrace p (taylorLimitBits D Z) yRight := ha (some (true,none))
  have hTestL (k : ℕ) : p k ≤ (t k).1.value A Z k := (hSel k).trans inf_le_left
  have hTestR (k : ℕ) : p k ≤ (t k).2.value D Z k := (hSel k).trans inf_le_right
  have hRadL := selected_tests_yield_radiusCode hP hNZ hpm A left Z hA hLeft
    (fun k => (t k).1) hTestL
  have hRadR := selected_tests_yield_radiusCode hP hNZ hpm D right Z hD hRight
    (fun k => (t k).2) hTestR
  have hEvalL := trace_identifies_taylorLimit hP hNZ hpm A left Z point yLeft
    hA hZ hLeft hPoint hyL hRadL (fun k => (t k).1.cutoff)
    (fun k j => TaylorTraceTest.select_cutoff (hTestL k) j)
  have hEvalR := trace_identifies_taylorLimit hP hNZ hpm D right Z point yRight
    hD hZ hRight hPoint hyR hRadR (fun k => (t k).2.cutoff)
    (fun k j => TaylorTraceTest.select_cutoff (hTestR k) j)
  exact ⟨⟨p,left,right,point,yLeft,yRight,hP,hNZ,hpm,hLeft,hRight,hPoint,hyL,hyR,
    hRadL,hRadR,hEvalL,hEvalR⟩⟩

end JSP000930.Positive
