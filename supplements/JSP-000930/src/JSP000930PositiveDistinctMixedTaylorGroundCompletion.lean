import JSP000930PositiveRationalCompletionDecisionTrace

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev CoefficientCoordinate := Bool × (ℕ × Bool)

def pairedCoefficientBits (U W : TaylorSlot → B) (j : CoefficientCoordinate)
    (q : RatPresentation) : B :=
  if j.1 then W (j.2.1,j.2.2,q) else U (j.2.1,j.2.2,q)

theorem distinct_mixed_taylor_ground_completion {X : ℕ → Type}
    (U W : TaylorSlot → B) (m : B) (hm : m ≠ ⊥)
    (hne : m ≤ (taylorCodeName U =ᴮ taylorCodeName W)ᶜ)
    (hU : ∀ n b, ProperCutOn m (fun q => U (n,b,q)))
    (hW : ∀ n b, ProperCutOn m (fun q => W (n,b,q)))
    (V : ∀ n,X n → B) (hV : ∀ n,m ≤ ⨆ x,V n x) :
    ∃ (start : B) (p : ℕ → B) (select : ∀ n,X n)
      (z : CoefficientCoordinate → ℝ)
      (box : ∀ j : CoefficientCoordinate,∀ n : ℕ,narrowRationalPair n),
      start ≠ ⊥ ∧ start ≤ m ∧ Antitone p ∧ (∀ n,p n ≠ ⊥) ∧ (∀ n,p n ≤ start) ∧
      (∀ n,p n ≤ V n (select n)) ∧
      (∃ n b,z (false,n,b) ≠ z (true,n,b)) ∧
      (∀ j n,RationalEncloses (pairedCoefficientBits U W j)
          (box j n).val.1 (box j n).val.2 (p (cutCoordIndex j n)) ∧
        ((box j n).val.1.value : ℝ) ≤ z j ∧ z j ≤ ((box j n).val.2.value : ℝ)) ∧
      ∀ j,
        (∀ q : RatPresentation,(q.value : ℝ) < z j →
          ∃ N,p N ≤ pairedCoefficientBits U W j q) ∧
        (∀ q : RatPresentation,z j < (q.value : ℝ) →
          ∃ N,p N ≤ (pairedCoefficientBits U W j q)ᶜ) := by
  obtain ⟨n,b,l,r,start,hs,hsM,hLR,hGap⟩ :=
    exists_coefficient_gap_of_named_taylor_ne U W m hm hne hU hW
  let β := pairedCoefficientBits U W
  have hβ (j : CoefficientCoordinate) : ProperCutOn start (β j) := by
    rcases j with ⟨c,k,e⟩
    cases c
    · exact properCutOn_mono hsM (hU k e)
    · exact properCutOn_mono hsM (hW k e)
  obtain ⟨p,select,z,box,hAnti,hNZ,hp,hV',he⟩ :=
    mixed_cut_ground_completion β start hs hβ V (fun l => hsM.trans (hV l))
  have hBound (j : CoefficientCoordinate) (q : RatPresentation) :=
    fixed_rational_cut_bounds_pass_to_completion (hβ j)
      (fun n => p (cutCoordIndex j n)) (fun n => hp _) (fun n => hNZ _)
      (box j) (z j) (he j) q
  have hr : (l.value : ℝ) < (r.value : ℝ) := by exact_mod_cast hLR
  refine ⟨start,p,select,z,box,hs,hsM,hAnti,hNZ,hp,hV',⟨n,b,?_⟩,he,?_⟩
  · rcases hGap with h | h
    · have hu := (hBound (false,n,b) r).1 h.1
      have hw := (hBound (true,n,b) l).2 h.2
      exact ne_of_gt (lt_of_le_of_lt hw (hr.trans_le hu))
    · have hw := (hBound (true,n,b) r).1 h.1
      have hu := (hBound (false,n,b) l).2 h.2
      exact ne_of_lt (lt_of_le_of_lt hu (hr.trans_le hw))
  · intro j
    exact completion_decides_strict_rational_tests (hβ j) p (cutCoordIndex j) hp (box j)
      (z j) (he j)

end JSP000930.Positive
