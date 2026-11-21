import JSP000930AnalyticRealCutTruth
import JSP000930AnalyticCutCauchy

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

private theorem cutCrisp_join (β : RatPresentation → B) (q : RatPresentation) :
    (⨆ r : RatPresentation, β r ⊓ crispTruth B (q.value < r.value)) =
      ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), β r := by
  apply iSup_congr
  intro r
  by_cases h : q.value < r.value
  · simp [crispTruth,h]
  · simp [crispTruth,h]

theorem forces_realCut_weighted_iff {n : ℕ} (v : DVec (V B) n) (X : STerm n)
    (β : RatPresentation → B) (hX : bTerm v X = weightedRationalSet β) (p : B) :
    p ≤ bTruth v (realCut_f X) ↔
      (p ≤ ⨆ q : RatPresentation, β q) ∧
      (p ≤ ⨆ q : RatPresentation, (β q)ᶜ) ∧
      (∀ q r : RatPresentation, q.value ≤ r.value → p ⊓ β r ≤ β q) ∧
      (∀ q : RatPresentation, p ⊓ β q ≤ ⨆ r : RatPresentation, ⨆ (_ : q.value < r.value), β r) := by
  rw [bTruth_realCut_weighted v X β hX]
  simp only [cutCrisp_join,le_inf_iff]
  constructor
  · rintro ⟨hn,hp,hl,hr⟩
    refine ⟨hn,hp,?_,?_⟩
    · intro q r hqr
      have h := hl.trans (iInf_le _ r)
      rw [← _root_.deduction] at h
      have h' := h.trans (iInf_le _ q)
      rw [← _root_.deduction] at h'
      simpa [crispTruth,hqr] using h'
    · intro q
      have h := hr.trans (iInf_le _ q)
      rwa [← _root_.deduction] at h
  · rintro ⟨hn,hp,hl,hr⟩
    refine ⟨hn,hp,?_,?_⟩
    · refine le_iInf fun r => ?_
      rw [← _root_.deduction]
      refine le_iInf fun q => ?_
      rw [← _root_.deduction]
      by_cases h : q.value ≤ r.value
      · simpa [crispTruth,h] using hl q r h
      · simp [crispTruth,h]
    · refine le_iInf fun q => ?_
      rw [← _root_.deduction]
      exact hr q

theorem roundedLiminf_forces_realCut {n : ℕ} (v : DVec (V B) n)
    (u : ℕ → RatPresentation → B) (p : B)
    (hc : p ≤ ⨆ N : ℕ, cutCauchyTail u 1 N)
    (hn : ∀ n : ℕ, p ≤ ⨆ r : RatPresentation, u n r)
    (hp : ∀ n : ℕ, p ≤ ⨆ r : RatPresentation, (u n r)ᶜ) :
    let w : DVec (V B) (n+1) := DVec.cons (roundedLiminfName u) v
    let X : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
    p ≤ bTruth w (realCut_f X) := by
  let w : DVec (V B) (n+1) := DVec.cons (roundedLiminfName u) v
  let X : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  change p ≤ bTruth w (realCut_f X)
  have hX : bTerm w X = weightedRationalSet (roundedLiminfBits u) :=
    bTerm_current_r181 v (roundedLiminfName u)
  apply (forces_realCut_weighted_iff w X (roundedLiminfBits u) hX p).2
  obtain ⟨hlo,hhi⟩ := cutCauchy_limit_proper_nonempty u p hc hn hp
  refine ⟨hlo,hhi,?_,?_⟩
  · intro q r hqr
    exact inf_le_right.trans (roundedLiminfBits_downward u hqr)
  · intro q
    exact inf_le_right.trans_eq (roundedLiminfBits_rounded u q)

end JSP000930.AnalyticSyntax
