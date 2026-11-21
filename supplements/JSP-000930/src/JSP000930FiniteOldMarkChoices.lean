import JSP000930OldDenseProductCenters

namespace JSP000930.Negative

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem exists_finitely_refined_marks [Fintype I] (T : I → B → Prop)
    (hMono : ∀ i {a b : B},a ≤ b → T i b → T i a)
    (m : B) (hm : m ≠ ⊥)
    (hD : ∀ i (b : B),b ≠ ⊥ → b ≤ m → ∃ a : B,a ≠ ⊥ ∧ a ≤ b ∧ T i a) :
    ∃ a : B,a ≠ ⊥ ∧ a ≤ m ∧ ∀ i,T i a := by
  classical
  have hF (s : Finset I) (b : B) (hb : b ≠ ⊥) (hbM : b ≤ m) :
      ∃ a : B,a ≠ ⊥ ∧ a ≤ b ∧ ∀ i ∈ s,T i a := by
    induction s using Finset.induction_on generalizing b with
    | empty =>
      refine ⟨b,hb,le_rfl,?_⟩
      intro i hi
      simp at hi
    | @insert i s hi ih =>
      obtain ⟨a,ha,haB,hA⟩ := hD i b hb hbM
      obtain ⟨c,hc,hcA,hC⟩ := ih a ha (haB.trans hbM)
      refine ⟨c,hc,hcA.trans haB,?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl|hj
      · exact hMono _ hcA hA
      · exact hC _ hj
  obtain ⟨a,ha,haM,hA⟩ := hF Finset.univ m hm le_rfl
  exact ⟨a,ha,haM,fun i => hA i (Finset.mem_univ i)⟩

end JSP000930.Negative
