import JSP000930PositiveDenseFiniteFreshTaylorCertificates
import JSP000930AnalyticTaylorLimit

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B] [Countable I] [Nonempty I]

theorem complex_countable_completion_with_tests {X : ℕ → Type}
    (A : I → ComplexBits B) (m : B) (hm : m ≠ ⊥) (hA : ∀ j,(A j).CutOn m)
    (V : ∀ n,X n → B) (hV : ∀ n,m ≤ ⨆ x,V n x) :
    ∃ (p : ℕ → B) (f : ∀ n,X n) (a : I → ℂ),
      Antitone p ∧ (∀ n,p n ≠ ⊥) ∧ (∀ n,p n ≤ m) ∧
      (∀ n,p n ≤ V n (f n)) ∧ ∀ j,ComplexDecisionTrace p (A j) (a j) := by
  let β (j : I × Bool) : RatPresentation → B := cutSide (A j.1) j.2
  have hβ (j : I × Bool) : ProperCutOn m (β j) := by
    obtain ⟨i,b⟩ := j
    cases b
    · exact (hA i).1
    · exact (hA i).2
  obtain ⟨p,f,z,hAnti,hNZ,hp,hTest,hTr⟩ :=
    mixed_cut_decision_completion β m hm hβ V hV
  let a (i : I) : ℂ := ⟨z (i,false),z (i,true)⟩
  exact ⟨p,f,a,hAnti,hNZ,hp,hTest,fun i => ⟨hTr (i,false),hTr (i,true)⟩⟩

end JSP000930.Positive
