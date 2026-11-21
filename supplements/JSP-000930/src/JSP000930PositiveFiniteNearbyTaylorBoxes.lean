import JSP000930PositiveRationalSeparationBoxes

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def complexSide (z : ℂ) (b : Bool) : ℝ := if b then z.im else z.re

def cutSide (z : ComplexBits B) (b : Bool) : RatPresentation → B := if b then z.im else z.re

def TaylorFinBoxes (N : ℕ) := Fin N × Bool → TaylorCoordinateBox

def TaylorFinBoxes.matches {N : ℕ} (W : TaylorFinBoxes N) (a : ℕ → ℂ) : Prop :=
  ∀ j : Fin N × Bool,(W j).realizes (complexSide (a j.1.val) j.2)

def TaylorFinBoxes.mask {N : ℕ} (W : TaylorFinBoxes N) (A : ℕ → ComplexBits B) : B :=
  ⨅ j : Fin N × Bool,(W j).value (cutSide (A j.1.val) j.2)

theorem finite_complex_boxes_select {N : ℕ} {p : ℕ → B} (hAnti : Antitone p)
    (A : ℕ → ComplexBits B) (a : ℕ → ℂ)
    (hA : ∀ n,ComplexDecisionTrace p (A n) (a n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (W : TaylorFinBoxes N) (k : ℕ),
      p k ≤ W.mask A ∧
      ∀ f : ℕ → ℂ,W.matches f → ∀ n < N,dist (f n) (a n) < ε := by
  classical
  choose δ hδ hNear using fun j : Fin N => complex_coordinate_rectangles_small (a j.val) ε hε
  choose W hL hU hBox using fun j : Fin N × Bool =>
    TaylorCoordinateBox.around (complexSide (a j.1.val) j.2) (δ j.1) (hδ j.1)
  have ht (j : Fin N × Bool) : CutDecisionTrace p
      (cutSide (A j.1.val) j.2) (complexSide (a j.1.val) j.2) := by
    obtain ⟨i,b⟩ := j
    cases b
    · exact (hA i.val).1
    · exact (hA i.val).2
  choose k hk using fun j : Fin N × Bool =>
    TaylorCoordinateBox.trace_select hAnti (ht j) (W j) ⟨hL j,hU j⟩
  let M : ℕ := Finset.univ.sup k
  refine ⟨W,M,?_,?_⟩
  · apply le_iInf
    intro j
    have hkj : k j ≤ M := Finset.le_sup (f := k) (Finset.mem_univ j)
    exact (hAnti hkj).trans (hk j)
  · intro f hf n hn
    let i : Fin N := ⟨n,hn⟩
    exact hNear i (f n) (hBox (i,false) _ (hf (i,false)))
      (hBox (i,true) _ (hf (i,true)))

theorem finite_complex_boxes_of_decision_traces {N : ℕ}
    {p : ℕ → B} (hAnti : Antitone p) (hNZ : ∀ n,p n ≠ ⊥)
    (A : ℕ → ComplexBits B) (a : ℕ → ℂ)
    (hA : ∀ n,ComplexDecisionTrace p (A n) (a n))
    (W : TaylorFinBoxes N) (k : ℕ) (hk : p k ≤ W.mask A) :
    W.matches a := by
  intro j
  have h : p k ≤ (W j).value (cutSide (A j.1.val) j.2) := hk.trans (iInf_le _ j)
  have ht : CutDecisionTrace p (cutSide (A j.1.val) j.2)
      (complexSide (a j.1.val) j.2) := by
    obtain ⟨i,b⟩ := j
    cases b
    · exact (hA i.val).1
    · exact (hA i.val).2
  exact TaylorCoordinateBox.trace_sound hAnti hNZ ht (W j) k h

end JSP000930.Positive
