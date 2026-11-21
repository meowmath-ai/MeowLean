import JSP000930LocalNamedPinDensity
import JSP000933MarkedTraceRectangles

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion
open scoped Flypitch bSet

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

theorem polynomialQ_genuine_pin_dense
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (z : J)
    (hSite : ∀ i, (site i).CutOn (⊤ : B))
    (hApart : ∀ i : J, z ≠ i → (⊤ : B) ≤ ((site z).name =ᴮ (site i).name)ᶜ)
    (hY : ∀ n, (H z n).CutOn (⊤ : B)) (hD : DensePalette (H z))
    (p : TotalCondition (polynomialQ site H)) :
    ∃ (q : TotalCondition (polynomialQ site H)) (a : PolyTrace B J),
      q ≤ p ∧ q.trace = some a ∧ z ∈ a.pins := by
  obtain ⟨r,hr,_,a,ha,_,_⟩ := exists_tightened_total_condition site H p 0 1 (by norm_num)
  by_cases hz : z ∈ a.pins
  · exact ⟨r,a,hr,ha,hz⟩
  have hR := r.valid
  rw [ha] at hR
  have hKnown : r.mask ≤ polyValid site H a := hR
  obtain ⟨s,c,hs,hsR,hzC,hc⟩ := exists_refining_trace_with_pin site H a r.mask
    r.nonzero hKnown z hz (fun i => cutOn_mono930 (hSite i) le_top)
    (fun n => cutOn_mono930 (hY n) le_top)
    (fun i hi => le_top.trans (hApart i (fun he => hz (he.symm ▸ hi)))) hD
  let q : TotalCondition (polynomialQ site H) :=
    ⟨s,some c,hs,hc.trans (((polynomialQ site H).refine_valid _ _).trans inf_le_left)⟩
  have hqr : q ≤ r := by
    refine ⟨hsR,?_⟩
    rw [ha]
    exact hc
  exact ⟨q,c,hqr.trans hr,rfl,hzC⟩

noncomputable def activePinValue
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (z : J) :
    TotalBA (polynomialQ site H) :=
  ⨆ p : {p : PolyTrace B J // z ∈ p.pins}, traceValue (polynomialQ site H) (some p.val)

theorem activePinValue_top
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B) (z : J)
    (hSite : ∀ i, (site i).CutOn (⊤ : B))
    (hApart : ∀ i : J, z ≠ i → (⊤ : B) ≤ ((site z).name =ᴮ (site i).name)ᶜ)
    (hY : ∀ n, (H z n).CutOn (⊤ : B)) (hD : DensePalette (H z)) :
    activePinValue site H z = ⊤ := by
  apply top_unique
  by_contra hf
  have hN : (activePinValue site H z)ᶜ ≠ ⊥ := fun he =>
    hf (le_of_eq (compl_eq_bot.mp he).symm)
  obtain ⟨p,hp⟩ := imageCondition_dense_r50 _ hN
  obtain ⟨q,a,hqp,hqa,hza⟩ := polynomialQ_genuine_pin_dense site H z hSite hApart hY hD p
  have hQ := q.valid.trans ((polynomialQ site H).refl _)
  have hQ' : q.mask ≤ (polynomialQ site H).refines q.trace (some a) := by simpa only [hqa] using hQ
  have hA : imageCondition q ≤ activePinValue site H z :=
    (image_le_traceValue_r429 q (some a) hQ').trans (le_iSup (fun t : {p : PolyTrace B J // z ∈ p.pins} =>
      traceValue (polynomialQ site H) (some t.val)) ⟨a,hza⟩)
  exact imageCondition_ne_bot_r50 q
    (disjoint_compl_right.out _ hA ((imageCondition_mono_r50 hqp).trans hp))

end JSP000930.Negative
