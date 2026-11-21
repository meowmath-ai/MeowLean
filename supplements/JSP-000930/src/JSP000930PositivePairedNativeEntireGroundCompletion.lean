import JSP000930PositiveReflectCompleteNativeGrowthPair

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure PairedEntireGroundCompletion (U V : TaylorSlot → B) (m : B) where
  p : ℕ → B
  left : ℕ → ℂ
  right : ℕ → ℂ
  antitone : Antitone p
  nonzero : ∀ n,p n ≠ ⊥
  under : ∀ n,p n ≤ m
  leftTrace : ∀ n,ComplexDecisionTrace p (complexCoeffBits U n) (left n)
  rightTrace : ∀ n,ComplexDecisionTrace p (complexCoeffBits V n) (right n)
  leftRadius : RadiusCode left
  rightRadius : RadiusCode right
  different : left ≠ right
  budgets : ℕ → ℕ × ℕ
  leftBudget : ∀ k n,p k ≤ radiusBudgetBits (complexCoeffBits U n) (k+1) (budgets k).1 n
  rightBudget : ∀ k n,p k ≤ radiusBudgetBits (complexCoeffBits V n) (k+1) (budgets k).2 n

theorem pairedEntire_ground_completion (U V : TaylorSlot → B) (m : B) (hm : m ≠ ⊥)
    (hValid : m ≤ validDistinctTaylorPair U V)
    (hGrowthU : GrowthOn m (complexCoeffBits U))
    (hGrowthV : GrowthOn m (complexCoeffBits V)) :
    Nonempty (PairedEntireGroundCompletion U V m) := by
  obtain ⟨hU,hV,hne⟩ := (validDistinctTaylorPair_iff U V m).1 hValid
  let T (k : ℕ) (v : ℕ × ℕ) : B :=
    (⨅ n,radiusBudgetBits (complexCoeffBits U n) (k+1) v.1 n) ⊓
      (⨅ n,radiusBudgetBits (complexCoeffBits V n) (k+1) v.2 n)
  have hT (k : ℕ) : m ≤ ⨆ v : ℕ × ℕ,T k v := by
    refine (le_inf (hGrowthU (k+1) (by omega)) (hGrowthV (k+1) (by omega))).trans ?_
    rw [iSup_inf_iSup]
  obtain ⟨start,p,budget,z,box,hstart,hsm,hAnti,hNZ,hUnder,hSel,hDistinct,hBox,hTrace⟩ :=
    distinct_mixed_taylor_ground_completion U V m hm hne hU hV T hT
  let a (n : ℕ) : ℂ := ⟨z (false,n,false),z (false,n,true)⟩
  let b (n : ℕ) : ℂ := ⟨z (true,n,false),z (true,n,true)⟩
  have hTraceU (n : ℕ) : ComplexDecisionTrace p (complexCoeffBits U n) (a n) :=
    ⟨⟨(hTrace (false,n,false)).1,(hTrace (false,n,false)).2⟩,
      ⟨(hTrace (false,n,true)).1,(hTrace (false,n,true)).2⟩⟩
  have hTraceV (n : ℕ) : ComplexDecisionTrace p (complexCoeffBits V n) (b n) :=
    ⟨⟨(hTrace (true,n,false)).1,(hTrace (true,n,false)).2⟩,
      ⟨(hTrace (true,n,true)).1,(hTrace (true,n,true)).2⟩⟩
  have hUM (n : ℕ) : (complexCoeffBits U n).CutOn m := ⟨hU n false,hU n true⟩
  have hVM (n : ℕ) : (complexCoeffBits V n).CutOn m := ⟨hV n false,hV n true⟩
  have hp (k : ℕ) : p k ≤ m := (hUnder k).trans hsm
  have hbU (k n : ℕ) : p k ≤ radiusBudgetBits (complexCoeffBits U n) (k+1) (budget k).1 n :=
    ((hSel k).trans inf_le_left).trans (iInf_le _ n)
  have hbV (k n : ℕ) : p k ≤ radiusBudgetBits (complexCoeffBits V n) (k+1) (budget k).2 n :=
    ((hSel k).trans inf_le_right).trans (iInf_le _ n)
  have hR₁ : RadiusCode a := by
    intro R hR
    let k := R-1
    have hEq : k+1 = R := by dsimp only [k]; omega
    refine ⟨(budget k).1,fun n => ?_⟩
    rw [← hEq]
    exact trace_budget_to_norm (trace_radiusBudget_at hAnti hNZ hp (hTraceU n) (hUM n) (hbU k n))
  have hR₂ : RadiusCode b := by
    intro R hR
    let k := R-1
    have hEq : k+1 = R := by dsimp only [k]; omega
    refine ⟨(budget k).2,fun n => ?_⟩
    rw [← hEq]
    exact trace_budget_to_norm (trace_radiusBudget_at hAnti hNZ hp (hTraceV n) (hVM n) (hbV k n))
  have hDiff : a ≠ b := by
    obtain ⟨k,e,he⟩ := hDistinct
    intro h
    have hk := congrFun h k
    cases e
    · exact he (congrArg Complex.re hk)
    · exact he (congrArg Complex.im hk)
  exact ⟨⟨p,a,b,hAnti,hNZ,hp,hTraceU,hTraceV,hR₁,hR₂,hDiff,budget,hbU,hbV⟩⟩

end JSP000930.Positive
