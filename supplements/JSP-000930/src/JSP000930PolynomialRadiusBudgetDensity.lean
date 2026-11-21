import JSP000930MarkedPolynomialForcing

open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

def PolyTrace.tighten (a : PolyTrace B J) (R : ℕ) (e : ℚ) (he : 0 < e) :
    PolyTrace B J :=
  ⟨a.coeff, a.pins, max a.radius R, min a.budget (e / 2),
    lt_min a.budget_pos (div_pos he (by norm_num))⟩

theorem tighten_valid (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (a : PolyTrace B J) (R : ℕ) (e : ℚ) (he : 0 < e) :
    polyValid site H (a.tighten R e he) = polyValid site H a := rfl

theorem tighten_refines (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (a : PolyTrace B J) (R : ℕ) (e : ℚ) (he : 0 < e) :
    polyValid site H a ≤
      (polynomialQ site H).refines (some (a.tighten R e he)) (some a) := by
  let q := a.tighten R e he
  change polyValid site H a ≤
    (polyValid site H q ⊓ polyValid site H a) ⊓ refinesValue site q a
  refine le_inf (le_inf le_rfl le_rfl) ?_
  unfold refinesValue
  have h : a.pins ⊆ q.pins ∧ q.budget ≤ a.budget ∧ a.radius ≤ q.radius :=
    ⟨fun _ h => h, min_le_left _ _, le_max_left _ _⟩
  refine le_inf ?_ (le_inf ?_ ?_)
  · simp only [JSP000933.PositiveForcing.crispTruth, ite_eq_left h, le_top]
  · unfold agreementValue
    exact le_iInf fun _ => le_top.trans bSet.bv_refl
  · unfold discValue
    apply le_iInf
    intro g
    exact distanceLe_self (eval_cutOn_of_coeff
      (show polyValid site H a ≤ coeffValue a.coeff from inf_le_left)
      (ComplexBits.checked_cutOn (gridPoint g) _)) _

def emptyPolynomialTrace (R : ℕ) (e : ℚ) (he : 0 < e) : PolyTrace B J :=
  ⟨[], ∅, R, e / 2, div_pos he (by norm_num)⟩

theorem emptyTrace_valid (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (R : ℕ) (e : ℚ) (he : 0 < e) :
    polyValid site H (emptyPolynomialTrace R e he) = ⊤ := by
  apply top_unique
  change (⊤ : B) ≤ ⊤ ⊓ paletteValue site H (emptyPolynomialTrace R e he)
  refine le_inf le_rfl ?_
  unfold paletteValue
  apply le_iInf
  intro z
  exact (Finset.notMem_empty z.1 z.2).elim

theorem exists_tightened_total_condition
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : TotalCondition (polynomialQ site H)) (R : ℕ) (e : ℚ) (he : 0 < e) :
    ∃ q : TotalCondition (polynomialQ site H), q ≤ p ∧ q.mask = p.mask ∧
      ∃ a : PolyTrace B J, q.trace = some a ∧ R ≤ a.radius ∧ a.budget < e := by
  classical
  cases hT : p.trace with
  | none =>
    let a : PolyTrace B J := emptyPolynomialTrace R e he
    have hValid : (polynomialQ site H).valid (some a) = ⊤ := emptyTrace_valid site H R e he
    let q : TotalCondition (polynomialQ site H) :=
      ⟨p.mask, some a, p.nonzero, by simpa only [hValid] using (le_top : p.mask ≤ ⊤)⟩
    refine ⟨q, ⟨le_rfl, ?_⟩, rfl, a, rfl, le_rfl, ?_⟩
    · rw [hT]
      change p.mask ≤ polyValid site H a
      change p.mask ≤ polyValid site H (emptyPolynomialTrace R e he)
      exact (emptyTrace_valid site H R e he).symm ▸ le_top
    · change e / 2 < e
      linarith
  | some a =>
    let b := a.tighten R e he
    have hp0 := p.valid
    rw [hT] at hp0
    have hp : p.mask ≤ polyValid site H a := hp0
    let q : TotalCondition (polynomialQ site H) :=
      ⟨p.mask, some b, p.nonzero, hp⟩
    refine ⟨q, ⟨le_rfl, ?_⟩, rfl, b, rfl, le_max_right _ _, ?_⟩
    · rw [hT]
      exact hp.trans (tighten_refines site H a R e he)
    · exact (min_le_right a.budget (e / 2)).trans_lt (by linarith)

end JSP000930.Negative
