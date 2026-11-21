import JSP000930SymbolicNamedGridDisplacement
import JSP000930NamedDistanceCongruence

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis ExprPoly

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_symbolic_precision (L r E : ℚ) (hL : 1 ≤ L) (hr : 0 < r) (hE : 0 < E)
    (degree pins : ℕ) :
    ∃ e : ℚ,0 < e ∧
      let η := e*(1+L)^degree
      (pins : ℚ)*(η/r*(L+L)^pins) + η ≤ E := by
  let C : ℚ := (1+L)^degree
  let G : ℚ := (pins : ℚ)*(r⁻¹*(L+L)^pins)
  have hC : 0 < C := pow_pos (by linarith) _
  have hG : 0 ≤ G := mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (inv_nonneg.mpr hr.le) (pow_nonneg (by linarith) _))
  have hCG : 0 < C*(1+G) := mul_pos hC (by linarith)
  let e := E/(C*(1+G))
  have he : 0 < e := div_pos hE hCG
  refine ⟨e,he,?_⟩
  change (pins : ℚ)*(e*C/r*(L+L)^pins) + e*C ≤ E
  calc
    (pins : ℚ)*(e*C/r*(L+L)^pins) + e*C = e*(C*(1+G)) := by
      unfold G
      rw [div_eq_mul_inv]
      ring
    _ = E := div_mul_cancel₀ _ hCG.ne'
    _ ≤ E := le_rfl

theorem extend_same_mark_seed_error {m : B} {x y z : ComplexBits B}
    (hx : x.CutOn m) (hy : y.CutOn m) (hz : z.CutOn m)
    (hxy : m ≤ x.name =ᴮ y.name) {e : ℚ} (he : 0 ≤ e)
    (h : m ≤ distanceLe x z e) : m ≤ distanceLe y z e := by
  have hZX := distanceLe_symm_mono hx hz he le_rfl h
  have hZY := distanceLe_congr_right930 hz hx hy hxy he hZX
  exact distanceLe_symm_mono hz hy he le_rfl hZY

end JSP000930.Negative
