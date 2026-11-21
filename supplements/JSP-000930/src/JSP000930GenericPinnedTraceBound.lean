import JSP000930NamedDistanceCongruence
import JSP000930GenericFineTraceCovers

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames JSP000933.MarkedForcing
  JSP000933.BooleanCompletion

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem activeTrace_pin_bound
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (a p : PolyTrace B J) (z : J) (hz : z ∈ p.pins) (hSite : (site z).CutOn (⊤ : B))
    (guard : B)
    (hExtend : ∀ (b : PolyTrace B J) (m : B),
      m ≤ guard → m ≤ coeffValue b.coeff → m ≤ coeffValue a.coeff →
      m ≤ discValue b a → b.budget ≤ a.budget →
      m ≤ distanceLe (b.eval (site z)) (a.eval (site z)) (a.budget - b.budget)) :
    (traceValue (polynomialQ site H) (some a) ⊓ traceValue (polynomialQ site H) (some p)) ⊓
        baseEmbed (polynomialQ site H) guard ≤
      baseEmbed (polynomialQ site H) (distanceLe (a.eval (site z)) (p.eval (site z)) a.budget) := by
  apply (supportProjection_le_iff_r428 _ _ _).mp
  rw [supportProjection_meet_base_r428,traceValue_pair_support_r430]
  unfold commonRefinementValue
  rw [iSup_inf_eq]
  apply iSup_le
  intro b
  cases b with
  | none =>
    change ((⊥ : B) ⊓ ⊥) ⊓ guard ≤ _
    simp only [bot_inf_eq,bot_le]
  | some q =>
    let w := (polynomialQ site H).refines (some q) (some a) ⊓
      (polynomialQ site H).refines (some q) (some p)
    let v := w ⊓ guard
    change v ≤ _
    have hw : v ≤ w := inf_le_left
    by_cases hV : v = ⊥
    · simpa only [hV] using (bot_le : (⊥ : B) ≤
        distanceLe (a.eval (site z)) (p.eval (site z)) a.budget)
    have hQ : v ≤ coeffValue q.coeff  :=
      hw.trans (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    have hA : v ≤ coeffValue a.coeff  :=
      hw.trans (inf_le_left.trans (inf_le_left.trans (inf_le_right.trans inf_le_left)))
    have hP : v ≤ coeffValue p.coeff  :=
      hw.trans (inf_le_right.trans (inf_le_left.trans (inf_le_right.trans inf_le_left)))
    have hRef : v ≤ refinesValue site q a  := hw.trans (inf_le_left.trans inf_le_right)
    have hC : v ≤ JSP000933.PositiveForcing.crispTruth B (a.pins ⊆ q.pins ∧ q.budget ≤ a.budget ∧ a.radius ≤ q.radius) :=
      hRef.trans inf_le_left
    have hG : a.pins ⊆ q.pins ∧ q.budget ≤ a.budget ∧ a.radius ≤ q.radius := by
      by_contra hn
      have h : v ≤ ⊥ := by simpa only [JSP000933.PositiveForcing.crispTruth,ite_eq_right hn] using hC
      exact hV (le_bot_iff.mp h)
    have hE : v ≤ (q.eval (site z)).name =ᴮ (p.eval (site z)).name :=
      (show v ≤ agreementValue site q p from hw.trans (inf_le_right.trans
        (inf_le_right.trans (inf_le_right.trans inf_le_left)))).trans
        (iInf_le (fun i : {j : J // j ∈ p.pins} =>
          (q.eval (site i.val)).name =ᴮ (p.eval (site i.val)).name) ⟨z,hz⟩)
    have hS : (site z).CutOn v := cutOn_mono930 hSite le_top
    have hQC := eval_cutOn_of_coeff hQ hS
    have hAC := eval_cutOn_of_coeff hA hS
    have hPC := eval_cutOn_of_coeff hP hS
    have hN : 0 ≤ a.budget - q.budget := sub_nonneg.mpr hG.2.1
    have hD : v ≤ discValue q a := hRef.trans (inf_le_right.trans inf_le_right)
    have hB := hExtend q v inf_le_right hQ hA hD hG.2.1
    have hSwap := distanceLe_symm_mono hQC hAC hN
      (sub_le_self a.budget q.budget_pos.le) hB
    exact distanceLe_congr_right930 hAC hQC hPC hE a.budget_pos.le hSwap

end JSP000930.Negative
