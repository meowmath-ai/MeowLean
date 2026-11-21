import JSP000930AnalyticMarkedProductPrefix

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.CantorCodes

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_center_window_geometry (p : SymbolicTrace J) (i : PinNumber p)
    (site : J → ComplexBits B) (m : B) (hm : m ≠ ⊥)
    (hS : ∀ j ∈ p.pins.map Prod.fst,(site j).CutOn m)
    (hApart : ∀ j ∈ p.pins.map Prod.fst,∀ k ∈ p.pins.map Prod.fst,j ≠ k →
      m ≤ ((site j).name =ᴮ (site k).name)ᶜ) :
    ∃ (s : B) (K R : ℕ),s ≠ ⊥ ∧ s ≤ m ∧ p.radius ≤ R ∧ (K : ℝ)/2 < (R : ℝ) ∧
      s ≤ halfRadiusBound (site (pinAt p i).1) K ∧ Nonempty (IncomingGeometry p site s) := by
  obtain ⟨b,hb,hBM,⟨G⟩⟩ := exists_incoming_geometry p site m hm hS hApart
  let z := site (pinAt p i).1
  have hz := cutOn_mono930 (hS _ (pinAt_mem_symbolicSite p i)) hBM
  have hCover : b ≤ ⨆ K : ℕ, halfRadiusBound z K :=
    (halfRadiusBound_cover z b hz).trans (iSup_le fun K =>
      iSup_le fun _ => le_iSup (halfRadiusBound z) K)
  obtain ⟨K,a,ha,haB,haK⟩ := exists_nonzero_below_choice_r135 b hb (halfRadiusBound z) hCover
  let R := max p.radius (K+1)
  have hKR : (K+1 : ℕ) ≤ R := le_max_right _ _
  have hKR' : (K : ℝ)+1 ≤ (R : ℝ) := by exact_mod_cast hKR
  have hK0 : (0 : ℝ) ≤ K := by positivity
  exact ⟨a,K,R,ha,haB.trans hBM,le_max_left _ _,by linarith,
    haK,⟨IncomingGeometry.mono p site G haB⟩⟩

theorem exists_earlier_center_budgets (p : SymbolicTrace J) (L r W : ℚ)
    (hL : 1 ≤ L) (hr : 0 < r) (hW : 0 < W) :
    ∃ (b e : ℚ),0 < b ∧ 0 < e ∧ 3*e ≤ b ∧ 2*e < W ∧
      e + b/r*(L+L)^p.pins.length ≤ p.budget := by
  let C : ℚ := r⁻¹ * (L+L)^p.pins.length
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr hr.le) (pow_nonneg (by linarith) _)
  have hone : 0 < 1+C := by linarith
  let b := (p.budget/4)/(1+C)
  have hb : 0 < b := div_pos (by linarith [p.budget_pos]) hone
  let e := min (p.budget/4) (min (b/4) (W/4))
  have he : 0 < e := lt_min (by linarith [p.budget_pos])
    (lt_min (by linarith) (by linarith))
  have hep : e ≤ p.budget/4 := min_le_left _ _
  have heb : e ≤ b/4 := (min_le_right _ _).trans (min_le_left _ _)
  have heW : e ≤ W/4 := (min_le_right _ _).trans (min_le_right _ _)
  have h := div_mul_cancel₀ (p.budget/4) hone.ne'
  change b*(1+C) = p.budget/4 at h
  have hbC : b*C ≤ p.budget/4 := by
    calc
      b*C ≤ b+b*C := by linarith
      _ = b*(1+C) := by ring
      _ = p.budget/4 := h
  have hrepr : b/r*(L+L)^p.pins.length = b*C := by unfold C; rw [div_eq_mul_inv]; ring
  exact ⟨b,e,hb,he,by linarith,by linarith,by rw [hrepr]; linarith [p.budget_pos]⟩

theorem earlier_center_retarget_allowance (p : SymbolicTrace J) (L r b e η : ℚ)
    (hL : 1 ≤ L) (hr : 0 < r)
    (hCap : η ≤ b) (hf : e+b/r*(L+L)^p.pins.length ≤ p.budget) :
    e+η/r*(L+L)^p.pins.length ≤ p.budget := by
  have hD : η/r ≤ b/r := div_le_div_of_nonneg_right hCap hr.le
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_right hD (pow_nonneg (by linarith) _))).trans hf

end JSP000930.Negative
