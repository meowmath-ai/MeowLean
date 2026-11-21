import JSP000930SymbolicOldSupportValues

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable {A A' : J → Prop}
variable (hAA : ∀ j,A j → A' j) (F : CompleteValueMap B C)
variable (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
variable (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
variable (hS : ∀ j,A j → (site j).map F = site' j)
variable (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)

noncomputable def includeSupportedCondition
    (p : TotalCondition (supportedSymbolicQ site H A)) :
    TotalCondition (supportedSymbolicQ site' H' A') :=
  ⟨F.toFun p.mask,includeSymbolicSupport hAA p.trace,
    fun h => p.nonzero (F.injective (h.trans F.map_bot.symm)),by
      have hv := F.monotone p.valid
      change F.toFun p.mask ≤ F.toFun ((symbolicPolynomialQ site H).valid p.trace.val) at hv
      rw [symbolicLabel_partial_map F site H site' H' hS hH p.trace.val p.trace.2] at hv
      exact hv⟩

theorem includeSupportedCondition_le_iff
    (p q : TotalCondition (supportedSymbolicQ site H A)) :
    includeSupportedCondition hAA F site H site' H' hS hH p ≤
      includeSupportedCondition hAA F site H site' H' hS hH q ↔ p ≤ q := by
  change (F.toFun p.mask ≤ F.toFun q.mask ∧ F.toFun p.mask ≤
    (supportedSymbolicQ site' H' A').refines (includeSymbolicSupport hAA p.trace)
      (includeSymbolicSupport hAA q.trace)) ↔
    (p.mask ≤ q.mask ∧ p.mask ≤ (supportedSymbolicQ site H A).refines p.trace q.trace)
  rw [← map_supported_refines hAA F site H site' H' hS hH]
  exact ⟨fun h => ⟨F.reflect_le_r93 h.1,F.reflect_le_r93 h.2⟩,
    fun h => ⟨F.monotone h.1,F.monotone h.2⟩⟩

theorem includeSupportedCondition_compatible_iff
    (hSite' : ∀ j,A j → (site' j).CutOn (⊤ : C))
    (hH' : ∀ j,A j → ∀ n,(H' j n).CutOn (⊤ : C))
    (hApart' : ∀ j,A j → ∀ i,A i → j ≠ i →
      (⊤ : C) ≤ ((site' j).name =ᴮ (site' i).name)ᶜ)
    (p q : TotalCondition (supportedSymbolicQ site H A)) :
    Compatible (includeSupportedCondition hAA F site H site' H' hS hH p)
      (includeSupportedCondition hAA F site H site' H' hS hH q) ↔ Compatible p q := by
  rw [totalCompatible_iff_r426,totalCompatible_iff_r426]
  let T := commonRefinementValue (supportedSymbolicQ site H A) p.trace q.trace
  change (F.toFun p.mask ⊓ F.toFun q.mask) ⊓
      commonRefinementValue (supportedSymbolicQ site' H' A')
        (includeSymbolicSupport hAA p.trace) (includeSymbolicSupport hAA q.trace) ≠ ⊥
    ↔ (p.mask ⊓ q.mask) ⊓ T ≠ ⊥
  rw [← map_supported_commonRefinement hAA F site H site' H' hS hH hSite' hH' hApart',
    ← F.map_inf,← F.map_inf]
  exact ⟨fun h hh => h ((congrArg F.toFun hh).trans F.map_bot),
    fun h hh => h (F.injective (hh.trans F.map_bot.symm))⟩

end JSP000930.Negative
