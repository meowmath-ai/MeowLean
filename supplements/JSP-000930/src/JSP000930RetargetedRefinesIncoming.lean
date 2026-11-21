import JSP000930OldWitnessNearCenter
import JSP000930NegativePinAvoidance

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 450000 in
theorem retargeted_refines_incoming (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace J) (i : PinNumber p) (c : ℚ × ℚ)
    (R : ℕ) (e : ℚ) (he : 0 < e) (hR : p.radius ≤ R)
    (q : PolyTrace B J) (m : B) (hm : m ≠ ⊥)
    (hCenter : m ≤ (polynomialQ site H).refines (some q)
      (some (oldCenteredTrace site H p i c R e he)))
    (hNew : (pinAt p i).1 ∈ q.pins)
    (hPin : m ≤ (q.eval (site (pinAt p i).1)).name =ᴮ (H (pinAt p i).1 (pinAt p i).2).name)
    (hSite : ∀ j ∈ p.pins.map Prod.fst,(site j).CutOn m)
    (hH : ∀ j ∈ p.pins.map Prod.fst,∀ n,(H j n).CutOn m)
    (hApart : ∀ j ∈ p.pins.map Prod.fst,∀ k ∈ p.pins.map Prod.fst,j ≠ k →
      m ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    (L η r : ℚ) (hL : 1 ≤ L) (hr : 0 < r) (hη : 0 ≤ η)
    (hRL : (p.radius : ℚ) ≤ L)
    (hNorm : ∀ j : PinNumber p,m ≤ distanceLe (site (pinAt p j).1)
      (ComplexBits.checked (0 : ℂ)) L)
    (hClose : m ≤ distanceLe (H (pinAt p i).1 (pinAt p i).2)
      (ComplexBits.checked (gaussianRat c)) η)
    (hMargin : SymbolicMargin p (symbolVal p site H) m r)
    (hAllowance : e + η/r*(L+L)^p.pins.length ≤ p.budget) :
    m ≤ (polynomialQ site H).refines (some q) (some (decodeSymbolicTrace site H p)) := by
  classical
  let z := (pinAt p i).1
  let f := decodeSymbolicTrace site H p
  let g := oldCenteredTrace site H p i c R e he
  let u := symbolVal p site H
  let a := η/r*(L+L)^p.pins.length
  change e+a ≤ p.budget at hAllowance
  have ha : 0 ≤ a := mul_nonneg (div_nonneg hη hr.le) (pow_nonneg (by linarith) _)
  have hu : ∀ j,(u j).CutOn m := by
    rintro (j|j)
    · exact hSite _ (pinAt_mem_symbolicSite p j)
    · exact hH _ (pinAt_mem_symbolicSite p j) _
  have hU : ∀ j b,b ∈ symbolicOtherSites p j →
      m ≤ ((u (.inl j)).name =ᴮ (u b).name)ᶜ := by
    intro j b hb
    obtain ⟨k,hk,rfl⟩ := (mem_symbolicOtherSites p j b).mp hb
    exact hApart _ (pinAt_mem_symbolicSite p j) _ (pinAt_mem_symbolicSite p k)
      (fun h => hk ((pinAt_first_inj p h).symm))
  have hf : m ≤ polyValid site H f := symbolicTrace_valid_from_environment site H p m hu hU
  have hq : m ≤ polyValid site H q := hCenter.trans (inf_le_left.trans inf_le_left)
  have hg : m ≤ polyValid site H g := hCenter.trans (inf_le_left.trans inf_le_right)
  have hRef : m ≤ refinesValue site q g := hCenter.trans inf_le_right
  obtain ⟨hPins,hb,hRad⟩ := structural_of_weighted_refines site q g m hm hRef
  have hQradius : R ≤ q.radius := hRad
  have hQbudget : q.budget ≤ e := hb
  obtain ⟨hAgree,hDrift⟩ := oldCenteredTrace_agreement_and_drift site H p i c R e he m
    hSite hH hApart L η r hL hr hη hRL hNorm hClose hMargin
  have hCoverage : f.pins ⊆ q.pins := by
    intro j hj
    by_cases hz : j = z
    · exact hz.symm ▸ hNew
    · apply hPins
      change j ∈ f.pins.erase z
      exact Finset.mem_erase.mpr ⟨hz,hj⟩
  have hFinal : f.pins ⊆ q.pins ∧ q.budget ≤ f.budget ∧ f.radius ≤ q.radius :=
    ⟨hCoverage,hQbudget.trans (by change e ≤ p.budget; linarith),hR.trans hQradius⟩
  change m ≤ (polyValid site H q ⊓ polyValid site H f) ⊓ refinesValue site q f
  refine le_inf (le_inf hq hf) ?_
  unfold refinesValue
  refine le_inf ?_ (le_inf ?_ ?_)
  · simp only [JSP000933.PositiveForcing.crispTruth,ite_eq_left hFinal,le_top]
  · unfold agreementValue
    apply le_iInf
    intro j
    by_cases hj : j.1 = z
    · have hI := symbolic_log_named_pin p m u i hu hU
      change m ≤ (f.eval (site z)).name =ᴮ (H z (pinAt p i).2).name at hI
      rw [hj]
      exact bSet.bv_trans hPin (bSet.bv_symm hI)
    · have hjG : j.1 ∈ g.pins := Finset.mem_erase.mpr ⟨hj,j.2⟩
      have hqG : m ≤ (q.eval (site j.1)).name =ᴮ (g.eval (site j.1)).name :=
        (hRef.trans (inf_le_right.trans inf_le_left)).trans (iInf_le (fun k : {k : J // k ∈ g.pins} =>
          (q.eval (site k.val)).name =ᴮ (g.eval (site k.val)).name) ⟨j.1,hjG⟩)
      exact bSet.bv_trans hqG (hAgree j.1 hjG)
  · unfold discValue
    apply le_iInf
    intro w
    have hRR : (p.radius : ℚ) ≤ (R : ℚ) := by exact_mod_cast hR
    let w' : RatGrid R := ⟨w.1,w.2.trans (pow_le_pow_left₀ (by positivity) hRR 2)⟩
    let x := ComplexBits.checked (B := B) (gridPoint w)
    have hx : x.CutOn m := ComplexBits.checked_cutOn _ _
    have hF := eval_cutOn_of_coeff (hf.trans inf_le_left) hx
    have hG := eval_cutOn_of_coeff (hg.trans inf_le_left) hx
    have hQ := eval_cutOn_of_coeff (hq.trans inf_le_left) hx
    have hD : m ≤ distanceLe (q.eval x) (g.eval x) (e-q.budget) :=
      (hRef.trans (inf_le_right.trans inf_le_right)).trans (iInf_le (fun t : RatGrid g.radius => distanceLe
        (q.eval (ComplexBits.checked (gridPoint t))) (g.eval (ComplexBits.checked (gridPoint t)))
        (g.budget - q.budget)) w')
    have h1 := distanceLe_symm_mono hF hG ha le_rfl (hDrift w)
    have hd := sub_nonneg.mpr hQbudget
    have h2 := distanceLe_triangle hQ hG hF hd ha hD h1
    have hFit : (e-q.budget)+a ≤ f.budget-q.budget := by
      change (e-q.budget)+a ≤ p.budget-q.budget
      linarith
    exact distanceLe_mono hQ hF (add_nonneg hd ha) hFit h2

end JSP000930.Negative
