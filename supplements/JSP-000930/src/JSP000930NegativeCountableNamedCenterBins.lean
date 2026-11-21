import JSP000930NegativeSpliceGuardRestriction
import JSP000930MarkedOnePinRefinement
import JSP000930NegativeWeightedSpliceCCC

open bSet Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev SpliceBin := Option (ℕ × ℕ × ℚ × ℚ × List (ℚ × ℚ))

noncomputable def spliceSeedEval (seed : List (ℚ × ℚ)) (z : ComplexBits B) :
    ComplexBits B :=
  mixedPolynomialEval (seed.map (fun r => ComplexBits.checked (gaussianRat r))) z

theorem spliceSeedEval_cut (seed : List (ℚ × ℚ)) (z : ComplexBits B)
    {m : B} (hz : z.CutOn m) : (spliceSeedEval seed z).CutOn m := by
  apply mixedPolynomialEval_cutOn _ _ _ hz
  intro c hc
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hc
  exact ComplexBits.checked_cutOn _ _

theorem exists_splice_center_bin (p : PolyTrace B J) (m : B) (hm : m ≠ ⊥)
    (hc : ∀ x ∈ p.coeff,x.CutOn m) :
    ∃ (s : B) (seed : List (ℚ × ℚ)), s ≠ ⊥ ∧ s ≤ m ∧
      ∀ g : RatGrid p.radius,s ≤ distanceLe (p.eval (ComplexBits.checked (gridPoint g)))
        (spliceSeedEval seed (ComplexBits.checked (gridPoint g))) (p.budget/8) := by
  let R : ℚ := p.radius
  let d : ℚ := (p.budget/8)/(1+R)^p.coeff.length
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hpow : 0 < (1+R)^p.coeff.length := pow_pos (by linarith) _
  have hd : 0 < d := div_pos (by linarith [p.budget_pos]) hpow
  obtain ⟨s,a,hs,hsm,hsa⟩ := exists_gaussian_seed p.coeff m hm hc d hd
  refine ⟨s,a,hs,hsm,fun g => ?_⟩
  let z := ComplexBits.checked (B := B) (gridPoint g)
  have hz : s ≤ distanceLe z (ComplexBits.checked (0 : ℂ)) R := by
    apply checked_distanceLe
    rw [dist_zero_right]
    simpa [R,z] using gridPoint_norm_le g
  have h := seedClose_horner_bound s z (ComplexBits.checked_cutOn _ s) d R hd.le hR hz p.coeff a
    (fun x hx => cutOn_mono930 (hc x hx) hsm) hsa
  have he : d*(1+R)^p.coeff.length = p.budget/8 := by
    exact div_mul_cancel₀ _ hpow.ne'
  rw [he] at h
  exact h

theorem distanceLe_splice_symm {m : B} {x y : ComplexBits B}
    (hx : x.CutOn m) (hy : y.CutOn m) {e : ℚ} (he : 0 ≤ e)
    (h : m ≤ distanceLe x y e) : m ≤ distanceLe y x e :=
  distanceLe_symm_mono hx hy he le_rfl h

end JSP000930.Negative
