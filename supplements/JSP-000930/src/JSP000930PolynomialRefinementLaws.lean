import JSP000930PolynomialTraceValidity

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem eval_cutOn_of_coeff {p : PolyTrace B J} {m : B}
    (hp : m ≤ coeffValue p.coeff) {x : ComplexBits B} (hx : x.CutOn m) :
    (p.eval x).CutOn m :=
  mixedPolynomialEval_cutOn p.coeff x ((le_coeffValue_iff m p.coeff).mp hp) hx

theorem refinesValue_refl (site : J → ComplexBits B)
    (p : PolyTrace B J) {m : B} (hm : m ≤ coeffValue p.coeff) :
    m ≤ refinesValue site p p := by
  unfold refinesValue
  apply le_inf
  · have hh : p.pins ⊆ p.pins ∧ p.budget ≤ p.budget ∧ p.radius ≤ p.radius :=
      ⟨fun _ a => a, le_rfl, le_rfl⟩
    simp only [JSP000933.PositiveForcing.crispTruth, ite_eq_left hh, le_top]
  · apply le_inf
    · unfold agreementValue
      exact le_iInf fun z => le_top.trans bSet.bv_refl
    · unfold discValue
      apply le_iInf
      intro g
      exact distanceLe_self
        (eval_cutOn_of_coeff hm (ComplexBits.checked_cutOn (gridPoint g) m)) _

private theorem nonbot_crisp_truth {m : B} (hm : m ≠ ⊥) {P : Prop}
    (h : m ≤ JSP000933.PositiveForcing.crispTruth B P) : P := by
  by_contra hn
  have h0 : m ≤ ⊥ := by simpa only [JSP000933.PositiveForcing.crispTruth, ite_eq_right hn] using h
  exact hm (le_bot_iff.mp h0)

theorem refinesValue_trans (site : J → ComplexBits B)
    (r q p : PolyTrace B J) {m : B}
    (hr : m ≤ coeffValue r.coeff) (hq : m ≤ coeffValue q.coeff)
    (hp : m ≤ coeffValue p.coeff)
    (hrq : m ≤ refinesValue site r q) (hqp : m ≤ refinesValue site q p) :
    m ≤ refinesValue site r p := by
  by_cases h0 : m = ⊥
  · simpa only [h0] using (bot_le : (⊥ : B) ≤ refinesValue site r p)
  have h₁ : q.pins ⊆ r.pins ∧ r.budget ≤ q.budget ∧ q.radius ≤ r.radius :=
    nonbot_crisp_truth h0 (hrq.trans inf_le_left)
  have h₂ : p.pins ⊆ q.pins ∧ q.budget ≤ p.budget ∧ p.radius ≤ q.radius :=
    nonbot_crisp_truth h0 (hqp.trans inf_le_left)
  have h₃ : p.pins ⊆ r.pins ∧ r.budget ≤ p.budget ∧ p.radius ≤ r.radius :=
    ⟨h₂.1.trans h₁.1, h₁.2.1.trans h₂.2.1, h₂.2.2.trans h₁.2.2⟩
  have ha₁ : m ≤ agreementValue site r q := hrq.trans (inf_le_right.trans inf_le_left)
  have ha₂ : m ≤ agreementValue site q p := hqp.trans (inf_le_right.trans inf_le_left)
  have hd₁ : m ≤ discValue r q := hrq.trans (inf_le_right.trans inf_le_right)
  have hd₂ : m ≤ discValue q p := hqp.trans (inf_le_right.trans inf_le_right)
  unfold refinesValue
  apply le_inf
  · simp only [JSP000933.PositiveForcing.crispTruth, ite_eq_left h₃, le_top]
  · apply le_inf
    · unfold agreementValue
      apply le_iInf
      intro z
      let zq : {x : J // x ∈ q.pins} := ⟨z.val,h₂.1 z.property⟩
      exact bSet.bv_trans (ha₁.trans (iInf_le
        (fun a : {x : J // x ∈ q.pins} => (r.eval (site a.val)).name =ᴮ (q.eval (site a.val)).name) zq))
        (ha₂.trans (iInf_le
          (fun a : {x : J // x ∈ p.pins} => (q.eval (site a.val)).name =ᴮ (p.eval (site a.val)).name) z))
    · unfold discValue
      apply le_iInf
      intro g
      have hNat : (p.radius : ℚ) ≤ (q.radius : ℚ) := by exact_mod_cast h₂.2.2
      have hq' : g.1.1 ^ 2 + g.1.2 ^ 2 ≤ (q.radius : ℚ) ^ 2 :=
        g.2.trans (pow_le_pow_left₀ (by positivity) hNat 2)
      let g' : RatGrid q.radius := ⟨g.1,hq'⟩
      let x : ComplexBits B := ComplexBits.checked (gridPoint g)
      have hx : x.CutOn m := ComplexBits.checked_cutOn (gridPoint g) m
      have hD₁ : m ≤ distanceLe (r.eval x) (q.eval x) (q.budget - r.budget) :=
        hd₁.trans (iInf_le _ g')
      have hD₂ : m ≤ distanceLe (q.eval x) (p.eval x) (p.budget - q.budget) :=
        hd₂.trans (iInf_le _ g)
      change m ≤ distanceLe (r.eval x) (p.eval x) (p.budget - r.budget)
      have hbudget : (q.budget - r.budget) + (p.budget - q.budget) = p.budget - r.budget := by ring
      rw [← hbudget]
      exact distanceLe_triangle (eval_cutOn_of_coeff hr hx) (eval_cutOn_of_coeff hq hx)
        (eval_cutOn_of_coeff hp hx) (sub_nonneg.mpr h₁.2.1) (sub_nonneg.mpr h₂.2.1) hD₁ hD₂

end JSP000930.Negative
