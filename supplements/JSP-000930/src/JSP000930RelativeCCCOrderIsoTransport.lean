import JSP000930ActualActiveRowFactorization

namespace JSP000930.Negative

open JSP000933.PreparedModel JSP000933.ForcingTransport
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.RelativeOCA
open JSP000933.OpenGraphForcing

variable {B C N : Type} [CompleteBooleanAlgebra B] [CompleteBooleanAlgebra C]

theorem changeValuedBase_congr930 (F G : CompleteValueMap B C)
    (h : F.toFun = G.toFun) (P : ValuedPoset B N) :
    changeValuedBase F P = changeValuedBase G P := by
  apply valuedPoset_ext_values
  · exact congrArg (fun f => f ∘ P.valid) h
  · funext p q
    exact congrFun h (P.refines p q)
  · rfl

theorem orderIso_map_unboundedValue930 (e : B ≃o C) (W : OmegaOneIndex→B) :
    e (unboundedValue W) = unboundedValue (fun i => e (W i)) := by
  simp only [unboundedValue,aboveValue,e.map_iSup,e.map_iInf]

theorem relativeCCC_changeOrderIso930 (e : B ≃o C) (P : ValuedPoset B N)
    (hP : ForcesRelativeCCC P) :
    ForcesRelativeCCC (changeValuedBase (completeMapOfOrderIso930 e) P) := by
  let F := completeMapOfOrderIso930 e
  let Q := changeValuedBase F P
  have hC (n m : N) : e (commonRefinementValue P n m) = commonRefinementValue Q n m := by
    unfold commonRefinementValue
    simp only [e.map_iSup,e.map_inf,Q,changeValuedBase] <;> rfl
  intro W hW hSep
  let V (i : OmegaOneIndex) (n : N) := e.symm (W i n)
  have hV (i : OmegaOneIndex) (n : N) : V i n ≤ P.valid n := by
    have h := hW i n
    change W i n ≤ e (P.valid n) at h
    have hh := e.symm.monotone h
    simpa only [V,e.symm_apply_apply] using hh
  have hD (i j : OmegaOneIndex) (hij : i<j) (p q : N) :
      (V i p ⊓ V j q) ⊓ commonRefinementValue P p q = ⊥ := by
    apply e.injective
    rw [e.map_inf,e.map_inf,e.map_bot,hC]
    simp only [V,e.apply_symm_apply]
    exact hSep i j hij p q
  have h := congrArg e (hP V hV hD)
  simpa only [orderIso_map_unboundedValue930,e.map_bot,e.map_iSup,V,e.apply_symm_apply] using h

end JSP000930.Negative
