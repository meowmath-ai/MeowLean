import JSP000930PositivePairedNativeEntireGroundCompletion
import JSP000930AnalyticFiniteStability
import Mathlib.Analysis.Complex.Basic

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_rational_presentation_box (x ε : ℝ) (hε : 0 < ε) :
    ∃ l u : RatPresentation,
      x-ε < (l.value : ℝ) ∧ (l.value : ℝ) < x ∧
        x < (u.value : ℝ) ∧ (u.value : ℝ) < x+ε := by
  obtain ⟨l,hl,hxl⟩ := exists_rat_btwn (show x-ε < x by linarith)
  obtain ⟨u,hxu,hu⟩ := exists_rat_btwn (show x < x+ε by linarith)
  obtain ⟨a,ha⟩ := ratPresentation_value_surjective l
  obtain ⟨b,hb⟩ := ratPresentation_value_surjective u
  exact ⟨a,b,by rwa [ha],by rwa [ha],by rwa [hb],by rwa [hb]⟩

theorem complex_coordinate_rectangles_small (z : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ w : ℂ,
      dist w.re z.re < δ → dist w.im z.im < δ → dist w z < ε := by
  let f : ℝ × ℝ → ℂ := fun y => (y.1 : ℂ) + (y.2 : ℂ) * Complex.I
  have hf : Continuous f :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hfEq (w : ℂ) : f (w.re,w.im) = w := by
    apply Complex.ext <;> simp [f,Complex.mul_re,Complex.mul_im]
  have hc := Metric.continuousAt_iff.mp (hf.continuousAt (x := (z.re,z.im))) ε hε
  obtain ⟨δ,hδ,hu⟩ := hc
  refine ⟨δ,hδ,fun w hre him => ?_⟩
  have hProd : dist (w.re,w.im) (z.re,z.im) < δ := by
    rw [Prod.dist_eq]
    exact max_lt hre him
  simpa only [hfEq] using hu hProd

structure TaylorCoordinateBox where
  lower : RatPresentation
  upper : RatPresentation

def TaylorCoordinateBox.realizes (I : TaylorCoordinateBox) (x : ℝ) : Prop :=
  (I.lower.value : ℝ) ≤ x ∧ x ≤ (I.upper.value : ℝ)

def TaylorCoordinateBox.value (I : TaylorCoordinateBox) (u : RatPresentation → B) : B :=
  u I.lower ⊓ (u I.upper)ᶜ

theorem TaylorCoordinateBox.around (x δ : ℝ) (hδ : 0 < δ) :
    ∃ I : TaylorCoordinateBox,
      (I.lower.value : ℝ) < x ∧ x < (I.upper.value : ℝ) ∧
      ∀ y,I.realizes y → dist y x < δ := by
  obtain ⟨l,u,hl,hl',hu,hu'⟩ := exists_rational_presentation_box x δ hδ
  refine ⟨⟨l,u⟩,hl',hu,fun y h => ?_⟩
  rcases h with ⟨hyl,hyu⟩
  rw [Real.dist_eq,abs_lt]
  constructor <;> linarith

theorem TaylorCoordinateBox.trace_select {p : ℕ → B} (hAnti : Antitone p)
    {u : RatPresentation → B} {x : ℝ} (h : CutDecisionTrace p u x) (I : TaylorCoordinateBox)
    (hI : (I.lower.value : ℝ) < x ∧ x < (I.upper.value : ℝ)) :
    ∃ N,p N ≤ I.value u := by
  obtain ⟨a,ha⟩ := h.below I.lower hI.1
  obtain ⟨b,hb⟩ := h.above I.upper hI.2
  exact ⟨max a b,le_inf ((hAnti (le_max_left _ _)).trans ha)
    ((hAnti (le_max_right _ _)).trans hb)⟩

theorem TaylorCoordinateBox.trace_sound {p : ℕ → B} (hAnti : Antitone p)
    (hNZ : ∀ n,p n ≠ ⊥) {u : RatPresentation → B} {x : ℝ}
    (h : CutDecisionTrace p u x) (I : TaylorCoordinateBox) (N : ℕ)
    (hI : p N ≤ I.value u) : I.realizes x := by
  constructor
  · by_contra! hn
    obtain ⟨k,hk⟩ := h.above I.lower hn
    let m := max N k
    have hLow := ((hAnti (le_max_left N k)).trans hI).trans inf_le_left
    have hBot := disjoint_compl_right.out _ hLow ((hAnti (le_max_right N k)).trans hk)
    exact hNZ m hBot
  · by_contra! hn
    obtain ⟨k,hk⟩ := h.below I.upper hn
    let m := max N k
    have hUp := ((hAnti (le_max_left N k)).trans hI).trans inf_le_right
    have hBot := disjoint_compl_right.out _ ((hAnti (le_max_right N k)).trans hk) hUp
    exact hNZ m hBot

end JSP000930.Positive
