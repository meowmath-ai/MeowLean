import JSP000930GenericPins
import JSP000933MarkedCompatiblePairs

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000933.BooleanNames
open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev FineTrace (B J : Type) (R : ℕ) (e : ℚ) :=
  {p : PolyTrace B J // R ≤ p.radius ∧ p.budget < e}

theorem finePolynomialTrace_cover
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (R : ℕ) (e : ℚ) (he : 0 < e) :
    (⨆ p : FineTrace B J R e, traceValue (polynomialQ site H) (some p.val)) = ⊤ := by
  apply top_unique
  by_contra hf
  let D := ⨆ p : FineTrace B J R e, traceValue (polynomialQ site H) (some p.val)
  change ¬ (⊤ : TotalBA (polynomialQ site H)) ≤ D at hf
  have hN : Dᶜ ≠ ⊥ := fun h => hf (le_of_eq (compl_eq_bot.mp h).symm)
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 Dᶜ hN
  obtain ⟨q,hqp,_,a,hqa,haR,haE⟩ := exists_tightened_total_condition site H p R e he
  have hRef : q.mask ≤ (polynomialQ site H).refines q.trace (some a) := by
    simpa only [hqa] using q.valid.trans ((polynomialQ site H).refl q.trace)
  have hA : imageCondition q ≤ D :=
    (image_le_traceValue_r429 q (some a) hRef).trans (le_iSup (fun t : FineTrace B J R e => traceValue (polynomialQ site H) (some t.val)) ⟨a,haR,haE⟩)
  exact imageCondition_ne_bot_r50 q
    (disjoint_compl_right.out _ hA ((imageCondition_mono_r50 hqp).trans hp))

private theorem nonbot_crisp_truth930 {m : B} (hm : m ≠ ⊥) {P : Prop}
    (h : m ≤ JSP000933.PositiveForcing.crispTruth B P) : P := by
  by_contra hN
  have hh : m ≤ ⊥ := by simpa only [JSP000933.PositiveForcing.crispTruth,ite_eq_right hN] using h
  exact hm (le_bot_iff.mp hh)

theorem commonTrace_disc_bound
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (a b : PolyTrace B J) (R : ℕ) (ha : R ≤ a.radius) (hb : R ≤ b.radius)
    (g : RatGrid R) :
    commonRefinementValue (polynomialQ site H) (some a) (some b) ≤
      distanceLe (a.eval (ComplexBits.checked (gridPoint g)))
        (b.eval (ComplexBits.checked (gridPoint g))) (a.budget + b.budget) := by
  unfold commonRefinementValue
  apply iSup_le
  intro p
  cases p with
  | none =>
    change (⊥ : B) ⊓ ⊥ ≤ _
    simp only [bot_inf_eq,bot_le]
  | some p =>
    let v := (polynomialQ site H).refines (some p) (some a) ⊓
      (polynomialQ site H).refines (some p) (some b)
    change v ≤ _
    by_cases hv : v = ⊥
    · simpa only [hv] using (bot_le : (⊥ : B) ≤
        distanceLe (a.eval (ComplexBits.checked (gridPoint g)))
          (b.eval (ComplexBits.checked (gridPoint g))) (a.budget + b.budget))
    have hgA : g.1.1^2 + g.1.2^2 ≤ (a.radius : ℚ)^2 :=
      g.2.trans (pow_le_pow_left₀ (by positivity)
        (show (R : ℚ) ≤ (a.radius : ℚ) by exact_mod_cast ha) 2)
    have hgB : g.1.1^2 + g.1.2^2 ≤ (b.radius : ℚ)^2 :=
      g.2.trans (pow_le_pow_left₀ (by positivity)
        (show (R : ℚ) ≤ (b.radius : ℚ) by exact_mod_cast hb) 2)
    let x : ComplexBits B := ComplexBits.checked (gridPoint g)
    have hx := ComplexBits.checked_cutOn (gridPoint g) v
    have hR₁ : v ≤ refinesValue site p a := inf_le_left.trans inf_le_right
    have hR₂ : v ≤ refinesValue site p b := inf_le_right.trans inf_le_right
    have hpV : v ≤ coeffValue p.coeff := inf_le_left.trans
      (inf_le_left.trans (inf_le_left.trans inf_le_left))
    have haV : v ≤ coeffValue a.coeff := inf_le_left.trans
      (inf_le_left.trans (inf_le_right.trans inf_le_left))
    have hbV : v ≤ coeffValue b.coeff := inf_le_right.trans
      (inf_le_left.trans (inf_le_right.trans inf_le_left))
    have hRadA : a.pins ⊆ p.pins ∧ p.budget ≤ a.budget ∧ a.radius ≤ p.radius :=
      nonbot_crisp_truth930 hv (hR₁.trans inf_le_left)
    have hRadB : b.pins ⊆ p.pins ∧ p.budget ≤ b.budget ∧ b.radius ≤ p.radius :=
      nonbot_crisp_truth930 hv (hR₂.trans inf_le_left)
    have hP₁ : v ≤ distanceLe (p.eval x) (a.eval x) (a.budget - p.budget) :=
      (hR₁.trans (inf_le_right.trans inf_le_right)).trans (iInf_le (fun j : RatGrid a.radius =>
        distanceLe (p.eval (ComplexBits.checked (gridPoint j)))
          (a.eval (ComplexBits.checked (gridPoint j))) (a.budget - p.budget)) ⟨g.val,hgA⟩)
    have hP₂ : v ≤ distanceLe (p.eval x) (b.eval x) (b.budget - p.budget) :=
      (hR₂.trans (inf_le_right.trans inf_le_right)).trans (iInf_le (fun j : RatGrid b.radius =>
        distanceLe (p.eval (ComplexBits.checked (gridPoint j)))
          (b.eval (ComplexBits.checked (gridPoint j))) (b.budget - p.budget)) ⟨g.val,hgB⟩)
    have hpX := eval_cutOn_of_coeff hpV hx
    have haX := eval_cutOn_of_coeff haV hx
    have hbX := eval_cutOn_of_coeff hbV hx
    have hEA : 0 ≤ a.budget - p.budget := sub_nonneg.mpr hRadA.2.1
    have hEB : 0 ≤ b.budget - p.budget := sub_nonneg.mpr hRadB.2.1
    have hBound := distanceLe_triangle haX hpX hbX hEA hEB
      (distanceLe_symm_mono hpX haX hEA le_rfl hP₁) hP₂
    exact distanceLe_mono haX hbX (add_nonneg hEA hEB)
      (by linarith [p.budget_pos]) hBound

theorem activeTrace_disc_bound
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (a b : PolyTrace B J) (R : ℕ) (ha : R ≤ a.radius) (hb : R ≤ b.radius)
    (g : RatGrid R) :
    traceValue (polynomialQ site H) (some a) ⊓ traceValue (polynomialQ site H) (some b) ≤
      baseEmbed (polynomialQ site H)
        (distanceLe (a.eval (ComplexBits.checked (gridPoint g)))
          (b.eval (ComplexBits.checked (gridPoint g))) (a.budget + b.budget)) := by
  apply (supportProjection_le_iff_r428 _ _ _).mp
  rw [traceValue_pair_support_r430]
  exact commonTrace_disc_bound site H a b R ha hb g

end JSP000930.Negative
