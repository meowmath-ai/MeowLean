import JSP000930NamedHornerApproximationStep

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem scalar_geometric_horner_bound {e R : ℚ} (he : 0 ≤ e) (hR : 0 ≤ R)
    (n : ℕ) : e + R * (e*(1+R)^n) ≤ e*(1+R)^(n+1) := by
  have hpow : 1 ≤ (1+R)^n := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc
        1 = (1 : ℚ)*1 := by ring
        _ ≤ (1+R)^k * (1+R) := mul_le_mul ih (by linarith) zero_le_one (zero_le_one.trans ih)
  calc
    e + R * (e*(1+R)^n) ≤ e*(1+R)^n + R * (e*(1+R)^n) := by
      exact add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow he) le_rfl
    _ = e*(1+R)^(n+1) := by rw [pow_succ]; ring

theorem seedClose_horner_bound (m : B) (z : ComplexBits B) (hz : z.CutOn m)
    (e R : ℚ) (he : 0 ≤ e) (hR : 0 ≤ R)
    (hZ : m ≤ distanceLe z (ComplexBits.checked (0 : ℂ)) R)
    (a : List (ComplexBits B)) (seed : List (ℚ × ℚ))
    (ha : ∀ w ∈ a,w.CutOn m) (hseed : SeedClose m a seed e) :
    m ≤ distanceLe (mixedPolynomialEval a z)
      (mixedPolynomialEval (seed.map (fun r => ComplexBits.checked (gaussianRat r))) z)
      (e*(1+R)^a.length) := by
  unfold SeedClose at hseed
  induction hseed with
  | nil =>
    change m ≤ distanceLe ((ComplexBits.ofNat 0 : ComplexBits B)) (ComplexBits.ofNat 0)
      (e*(1+R)^0)
    rw [pow_zero,mul_one]
    exact distanceLe_self (ComplexBits.ofNat_cutOn 0 m) e
  | @cons w r a seed hwr hRest ih =>
    have hw := ha w List.mem_cons_self
    have ha' : ∀ v ∈ a,v.CutOn m := fun v hv => ha v (List.mem_cons_of_mem _ hv)
    let b := seed.map (fun r => ComplexBits.checked (B := B) (gaussianRat r))
    have hb : ∀ v ∈ b,v.CutOn m := by
      intro v hv
      obtain ⟨x,_,rfl⟩ := List.mem_map.mp hv
      exact ComplexBits.checked_cutOn _ _
    have hE : 0 ≤ e*(1+R)^a.length := mul_nonneg he (pow_nonneg (by linarith) _)
    have hstep := named_horner_step_bound w (ComplexBits.checked (gaussianRat r))
      (mixedPolynomialEval a z) (mixedPolynomialEval b z) z m hw
      (ComplexBits.checked_cutOn _ _) (mixedPolynomialEval_cutOn a z ha' hz)
      (mixedPolynomialEval_cutOn b z hb hz) hz e (e*(1+R)^a.length) R he hE hR
      hwr (ih ha') hZ
    change m ≤ distanceLe (w.add (z.mul (mixedPolynomialEval a z)))
      ((ComplexBits.checked (gaussianRat r)).add (z.mul (mixedPolynomialEval b z)))
      (e*(1+R)^(a.length+1))
    exact distanceLe_mono (ComplexBits.add_cutOn hw (ComplexBits.mul_cutOn hz
      (mixedPolynomialEval_cutOn a z ha' hz)))
      (ComplexBits.add_cutOn (ComplexBits.checked_cutOn _ _) (ComplexBits.mul_cutOn hz
        (mixedPolynomialEval_cutOn b z hb hz))) (add_nonneg he (mul_nonneg hR hE))
      (scalar_geometric_horner_bound he hR a.length) hstep

end JSP000930.Negative
