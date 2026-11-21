import JSP000930NamedComplexMetricLaw
import JSP000930AnalyticLiteralEvaluation

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Analytic

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B] [Countable J] [Nonempty J]

theorem cutSubset_of_decision_law (vars : J → ComplexBits B) (m : B)
    (hVars : ∀ j,(vars j).CutOn m) (u v : RatPresentation → B) (hu : ProperCutOn m u)
    (law : ∀ (p : ℕ → B) (w : J → ℂ), Antitone p → (∀ n,p n ≠ ⊥) →
      (∀ n,p n ≤ m) → (∀ j,ComplexDecisionTrace p (vars j) (w j)) →
      ∃ x y : ℝ,CutDecisionTrace p u x ∧ CutDecisionTrace p v y ∧ x ≤ y) :
    m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v := by
  by_contra hFail
  obtain ⟨q,r,s,hs,hsm,hqr,hlo,hhi⟩ := nonzero_cut_order_countercell hu hFail
  have hSat (j : J) : (vars j).CutOn s :=
    ⟨properCutOn_mono hsm (hVars j).1,properCutOn_mono hsm (hVars j).2⟩
  obtain ⟨p,w,hp,hn,hps,ht⟩ := exists_complex_decision_completion vars s hs hSat
  obtain ⟨x,y,tx,ty,hxy⟩ := law p w hp hn (fun n => (hps n).trans hsm) ht
  have hL := trace_forcedMember_le hp hn tx r ⟨0,(hps 0).trans hlo⟩
  have hH := trace_forcedAbsent_ge hp hn ty q ⟨0,(hps 0).trans hhi⟩
  have hQr : (q.value : ℝ) < (r.value : ℝ) := by exact_mod_cast hqr
  exact (not_lt_of_ge (hL.trans (hxy.trans hH))) hQr

theorem complexEq_of_decision_law (vars : J → ComplexBits B) (m : B)
    (hVars : ∀ j,(vars j).CutOn m) (u v : ComplexBits B) (hu : u.CutOn m) (hv : v.CutOn m)
    (law : ∀ (p : ℕ → B) (w : J → ℂ), Antitone p → (∀ n,p n ≠ ⊥) →
      (∀ n,p n ≤ m) → (∀ j,ComplexDecisionTrace p (vars j) (w j)) →
      ∃ z : ℂ,ComplexDecisionTrace p u z ∧ ComplexDecisionTrace p v z) :
    m ≤ u.name =ᴮ v.name := by
  rw [ComplexBits.name_eq]
  have hCoord (im : Bool) :
      m ≤ weightedRationalSet (u.coord im) =ᴮ weightedRationalSet (v.coord im) := by
    have hU : ProperCutOn m (u.coord im) := by
      cases im
      · exact hu.1
      · exact hu.2
    have hV : ProperCutOn m (v.coord im) := by
      cases im
      · exact hv.1
      · exact hv.2
    rw [bSet.eq_iff_subset_subset]
    apply le_inf
    · apply cutSubset_of_decision_law vars m hVars _ _ hU
      intro p w hp hn hpm ht
      obtain ⟨z,hu',hv'⟩ := law p w hp hn hpm ht
      exact ⟨complexCoord z im,complexCoord z im,hu'.coordinate im,hv'.coordinate im,le_rfl⟩
    · apply cutSubset_of_decision_law vars m hVars _ _ hV
      intro p w hp hn hpm ht
      obtain ⟨z,hu',hv'⟩ := law p w hp hn hpm ht
      exact ⟨complexCoord z im,complexCoord z im,hv'.coordinate im,hu'.coordinate im,le_rfl⟩
  exact le_inf (hCoord false) (hCoord true)

end JSP000930.Negative
