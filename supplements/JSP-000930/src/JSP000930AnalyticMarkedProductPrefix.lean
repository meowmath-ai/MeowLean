import JSP000930AnalyticFiniteProductCompatibility

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B C I J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable {A A' : J → Prop}
variable (hAA : ∀ j,A j → A' j) (F : CompleteValueMap B C)
variable (site : J → ComplexBits B) (H : I → J → ℕ → ComplexBits B)
variable (site' : J → ComplexBits C) (H' : I → J → ℕ → ComplexBits C)
variable (hS : ∀ j,A j → (site j).map F = site' j)
variable (hH : ∀ i j,A j → ∀ n,(H i j n).map F = H' i j n)

abbrev AnalyticRowTotal {D : Type} [NontrivialCompleteBooleanAlgebra D]
    (s : J → ComplexBits D) (P : I → J → ℕ → ComplexBits D) (Y : J → Prop) :=
  TotalCondition (rowProductQ (fun i => supportedSymbolicQ s (P i) Y))

noncomputable def includeAnalyticProductCondition (p : AnalyticRowTotal site H A) :
    AnalyticRowTotal site' H' A' :=
  ⟨F.toFun p.mask,fun i => includeSymbolicSupport hAA (p.trace i),
    fun h => p.nonzero (F.injective (h.trans F.map_bot.symm)),by
      apply le_iInf
      intro i
      have h := F.monotone (p.valid.trans (iInf_le _ i))
      change F.toFun p.mask ≤ F.toFun ((symbolicPolynomialQ site (H i)).valid (p.trace i).val) at h
      rw [symbolicLabel_partial_map F site (H i) site' (H' i) hS (hH i) (p.trace i).val (p.trace i).2] at h
      exact h⟩

theorem includeAnalyticProductCondition_le_iff (p q : AnalyticRowTotal site H A) :
    includeAnalyticProductCondition hAA F site H site' H' hS hH p ≤
      includeAnalyticProductCondition hAA F site H site' H' hS hH q ↔ p ≤ q := by
  let f := includeSymbolicSupport hAA
  let Q (i : I) := supportedSymbolicQ site (H i) A
  let Q' (i : I) := supportedSymbolicQ site' (H' i) A'
  change (F.toFun p.mask ≤ F.toFun q.mask ∧ F.toFun p.mask ≤
    ⨅ i, (Q' i).refines (f (p.trace i)) (f (q.trace i))) ↔
    (p.mask ≤ q.mask ∧ p.mask ≤ ⨅ i,(Q i).refines (p.trace i) (q.trace i))
  have heq : (⨅ i,(Q' i).refines (f (p.trace i)) (f (q.trace i))) =
      F.toFun (⨅ i,(Q i).refines (p.trace i) (q.trace i)) := by
    rw [F.map_iInf]
    exact iInf_congr (fun i => (map_supported_refines hAA F site (H i) site' (H' i)
      hS (hH i) (p.trace i) (q.trace i)).symm)
  rw [heq]
  exact ⟨fun h => ⟨F.reflect_le_r93 h.1,F.reflect_le_r93 h.2⟩,
    fun h => ⟨F.monotone h.1,F.monotone h.2⟩⟩

theorem includeAnalyticProductCondition_compatible_iff [Fintype I]
    (hSite' : ∀ j,A j → (site' j).CutOn (⊤ : C))
    (hH' : ∀ i j,A j → ∀ n,(H' i j n).CutOn (⊤ : C))
    (hApart' : ∀ j,A j → ∀ k,A k → j ≠ k →
      (⊤ : C) ≤ ((site' j).name =ᴮ (site' k).name)ᶜ)
    (p q : AnalyticRowTotal site H A) :
    Compatible (includeAnalyticProductCondition hAA F site H site' H' hS hH p)
      (includeAnalyticProductCondition hAA F site H site' H' hS hH q) ↔ Compatible p q := by
  rw [totalCompatible_iff_r426,totalCompatible_iff_r426,
    rowProduct_commonRefinement_eq,rowProduct_commonRefinement_eq]
  let f := includeSymbolicSupport hAA
  let Q (i : I) := supportedSymbolicQ site (H i) A
  let Q' (i : I) := supportedSymbolicQ site' (H' i) A'
  change ((F.toFun p.mask ⊓ F.toFun q.mask) ⊓
    (⨅ i,commonRefinementValue (Q' i) (f (p.trace i)) (f (q.trace i))) ≠ ⊥) ↔
    ((p.mask ⊓ q.mask) ⊓ (⨅ i,commonRefinementValue (Q i) (p.trace i) (q.trace i)) ≠ ⊥)
  have heq : (⨅ i,commonRefinementValue (Q' i) (f (p.trace i)) (f (q.trace i))) =
      F.toFun (⨅ i,commonRefinementValue (Q i) (p.trace i) (q.trace i)) := by
    rw [F.map_iInf]
    exact iInf_congr (fun i => (map_supported_commonRefinement hAA F site (H i) site' (H' i)
      hS (hH i) hSite' (hH' i) hApart' (p.trace i) (q.trace i)).symm)
  rw [heq,← F.map_inf,← F.map_inf]
  exact ⟨fun h hh => h ((congrArg F.toFun hh).trans F.map_bot),
    fun h hh => h (F.injective (hh.trans F.map_bot.symm))⟩

end JSP000930.Negative
