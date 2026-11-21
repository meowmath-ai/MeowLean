import JSP000930NamedDisplacementDiscControl
import JSP000930MixedNamedBoxGenericity
import JSP000930PositiveLocalRationalCutEnclosures

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000933.CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem trace_enclosure_bounds {p : ℕ → B} (h : Antitone p) (hnz : ∀ n,p n ≠ ⊥)
    {m : B} (hpm : ∀ n,p n ≤ m) {u : RatPresentation → B} {x : ℝ}
    (ht : CutDecisionTrace p u x) {a b : RatPresentation} (he : RationalEncloses u a b m) :
    (a.value : ℝ) ≤ x ∧ x ≤ (b.value : ℝ) :=
  ⟨trace_forcedMember_le h hnz ht a ⟨0,(hpm 0).trans he.1⟩,
    trace_forcedAbsent_ge h hnz ht b ⟨0,(hpm 0).trans he.2⟩⟩

theorem exists_thin_complex_enclosure (z : ComplexBits B) (m : B) (hm : m ≠ ⊥)
    (hz : z.CutOn m) (e : ℚ) (he : 0 < e) :
    ∃ (a b c d : RatPresentation) (s : B), s ≠ ⊥ ∧ s ≤ m ∧
      a.value < b.value ∧ c.value < d.value ∧
      b.value - a.value < e ∧ d.value - c.value < e ∧
      RationalEncloses z.re a b s ∧ RationalEncloses z.im c d s := by
  let J := {qr : RatPresentation × RatPresentation //
    qr.1.value < qr.2.value ∧ qr.2.value - qr.1.value < e}
  obtain ⟨U,r,hr,hrm,hrU⟩ := exists_nonzero_below_choice_r135 m hm
    (fun qr : J => z.re qr.1.1 ⊓ (z.re qr.1.2)ᶜ) (rational_enclosure_dense hz.1 e he)
  obtain ⟨V,s,hs,hsr,hsV⟩ := exists_nonzero_below_choice_r135 r hr
    (fun qr : J => z.im qr.1.1 ⊓ (z.im qr.1.2)ᶜ)
    (hrm.trans (rational_enclosure_dense hz.2 e he))
  exact ⟨U.1.1,U.1.2,V.1.1,V.1.2,s,hs,hsr.trans hrm,U.2.1,V.2.1,U.2.2,V.2.2,
    ⟨hsr.trans (hrU.trans inf_le_left),hsr.trans (hrU.trans inf_le_right)⟩,
    ⟨hsV.trans inf_le_left,hsV.trans inf_le_right⟩⟩

theorem norm_le_re_im_abs (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  have h : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  calc
    ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := congrArg norm h
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by simp [Complex.norm_mul,Complex.norm_real,Real.norm_eq_abs]

theorem distanceLe_of_common_box (x y : ComplexBits B) (m : B)
    (hx : x.CutOn m) (hy : y.CutOn m)
    (a b c d : RatPresentation) (ex : RationalEncloses x.re a b m)
    (fx : RationalEncloses x.im c d m) (ey : RationalEncloses y.re a b m)
    (fy : RationalEncloses y.im c d m) (ε : ℚ)
    (hw : (b.value - a.value) + (d.value - c.value) ≤ ε) :
    m ≤ distanceLe x y ε := by
  let u : Bool → ComplexBits B := fun i => if i then y else x
  have hu : ∀ i, (u i).CutOn m := by
    intro i
    cases i
    · exact hx
    · exact hy
  refine distanceLe_of_finite_metric_law u m hu false true ε ?_
  intro p w hp hnz hpm ht
  have hX : ComplexDecisionTrace p x (w false) := ht false
  have hY : ComplexDecisionTrace p y (w true) := ht true
  have hreX := trace_enclosure_bounds hp hnz hpm hX.1 ex
  have himX := trace_enclosure_bounds hp hnz hpm hX.2 fx
  have hreY := trace_enclosure_bounds hp hnz hpm hY.1 ey
  have himY := trace_enclosure_bounds hp hnz hpm hY.2 fy
  have hRe : |(w false).re - (w true).re| ≤ (b.value : ℝ) - (a.value : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [hreX.1,hreX.2,hreY.1,hreY.2]
  have hIm : |(w false).im - (w true).im| ≤ (d.value : ℝ) - (c.value : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith [himX.1,himX.2,himY.1,himY.2]
  have hWidth : ((b.value : ℝ) - (a.value : ℝ)) + ((d.value : ℝ) - (c.value : ℝ)) ≤ (ε : ℝ) := by
    exact_mod_cast hw
  have hDist : dist (w false) (w true) ≤ (ε : ℝ) := by
    rw [dist_eq_norm]
    exact (norm_le_re_im_abs _).trans (by
      simp only [Complex.sub_re,Complex.sub_im]
      exact (add_le_add hRe hIm).trans hWidth)
  exact pow_le_pow_left₀ dist_nonneg hDist 2

end JSP000930.Negative
