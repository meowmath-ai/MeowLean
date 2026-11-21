import JSP000930AnalyticFiniteSupportCutoff

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {D I J C : Type} [Preorder D] [Nonempty D] [Fintype I]
variable [NontrivialCompleteBooleanAlgebra C]
variable {BD : D → Type} [instD : ∀ d,NontrivialCompleteBooleanAlgebra (BD d)]

set_option maxHeartbeats 450000 in
theorem earlier_analytic_condition_below_limit
    (A : D → J → Prop) (Y : J → Prop)
    (hAY : ∀ d j,A d j → Y j)
    (hMono : ∀ {d e},d ≤ e → ∀ j,A d j → A e j)
    (hDirected : ∀ d e : D,∃ f : D,d ≤ f ∧ e ≤ f)
    (hCover : ∀ j,Y j → ∃ d,A d j)
    (F : ∀ d,CompleteValueMap (BD d) C)
    (siteD : ∀ d,J → ComplexBits (BD d)) (HD : ∀ d,I → J → ℕ → ComplexBits (BD d))
    (site : J → ComplexBits C) (H : I → J → ℕ → ComplexBits C)
    (hS : ∀ d j,A d j → (siteD d j).map (F d) = site j)
    (hH : ∀ d i j,A d j → ∀ n,(HD d i j n).map (F d) = H i j n)
    (hBaseBasis : ∀ (d : D) (x : C),x ≠ ⊥ → ∃ e : D, d ≤ e ∧
      ∃ b : BD e,b ≠ ⊥ ∧ (F e).toFun b ≤ x)
    (p : AnalyticRowTotal site H Y) :
    ∃ (d : D) (q : AnalyticRowTotal (siteD d) (HD d) (A d)),
      includeAnalyticProductCondition (hAY d) (F d) (siteD d) (HD d) site H
        (hS d) (hH d) q ≤ p := by
  obtain ⟨d,hd⟩ := rowProduct_support_has_stage A Y hMono hDirected hCover p.trace
  obtain ⟨e,hde,b,hb,hbp⟩ := hBaseBasis d p.mask p.nonzero
  let v (i : I) : SupportedSymbolic J (A e) := includeSymbolicSupport (hMono hde)
    ⟨(p.trace i).val,hd i⟩
  have hValid (i : I) : b ≤ (supportedSymbolicQ (siteD e) (HD e i) (A e)).valid (v i) := by
    apply (F e).reflect_le_r93
    change (F e).toFun b ≤ (F e).toFun ((symbolicPolynomialQ (siteD e) (HD e i)).valid (v i).val)
    rw [symbolicLabel_partial_map (F e) (siteD e) (HD e i) site (H i) (hS e) (hH e i) (v i).val (v i).2]
    exact hbp.trans (p.valid.trans (iInf_le _ i))
  let q : AnalyticRowTotal (siteD e) (HD e) (A e) := ⟨b,v,hb,le_iInf hValid⟩
  refine ⟨e,q,hbp,?_⟩
  have ht : (fun i => includeSymbolicSupport (hAY e) (q.trace i)) = p.trace := by
    funext i
    apply Subtype.ext
    rfl
  change (F e).toFun b ≤ (rowProductQ (fun i => supportedSymbolicQ site (H i) Y)).refines
    (fun i => includeSymbolicSupport (hAY e) (q.trace i)) p.trace
  rw [ht]
  exact hbp.trans (p.valid.trans ((rowProductQ (fun i => supportedSymbolicQ site (H i) Y)).refl _))

end JSP000930.Negative
