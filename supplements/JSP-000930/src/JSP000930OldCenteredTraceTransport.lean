import JSP000930OldCenteredSymbolicTrace

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]

theorem oldCenteredTrace_map (F : CompleteValueMap B C)
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
    (p : SymbolicTrace J) (i : PinNumber p) (c : ℚ × ℚ)
    (R : ℕ) (e : ℚ) (he : 0 < e)
    (hS : ∀ j ∈ p.pins.map Prod.fst,(site j).map F = site' j)
    (hH : ∀ j ∈ p.pins.map Prod.fst,j ≠ (pinAt p i).1 → ∀ n,(H j n).map F = H' j n) :
    (oldCenteredTrace site H p i c R e he).map F =
      oldCenteredTrace site' H' p i c R e he := by
  classical
  let G := overwritePalette H (pinAt p i).1 (ComplexBits.checked (gaussianRat c))
  let G' := overwritePalette H' (pinAt p i).1 (ComplexBits.checked (gaussianRat c))
  have hG : ∀ j ∈ p.pins.map Prod.fst,∀ n,(G j n).map F = G' j n := by
    intro j hj n
    by_cases h : j = (pinAt p i).1
    · simp only [G,G',overwritePalette,ite_eq_left h,ComplexBits.map_checked]
    · simpa only [G,G',overwritePalette,ite_eq_right h] using hH j hj h n
  have ht := decodeSymbolicTrace_completeMap_on_log F p site G site' G' hS hG
  have hc := congrArg PolyTrace.coeff ht
  unfold oldCenteredTrace PolyTrace.map
  change PolyTrace.mk (((decodeSymbolicTrace site G p).map F).coeff)
      ((p.pins.map Prod.fst).toFinset.erase (pinAt p i).1) R e he =
    PolyTrace.mk (decodeSymbolicTrace site' G' p).coeff
      ((p.pins.map Prod.fst).toFinset.erase (pinAt p i).1) R e he
  rw [hc]

end JSP000930.Negative
