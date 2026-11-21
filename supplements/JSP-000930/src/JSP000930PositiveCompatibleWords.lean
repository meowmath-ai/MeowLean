import JSP000930PositiveMixedFreshRowDensity

namespace JSP000930.Positive.Cohen

open JSP000933.BooleanCompletion JSP000933.MarkedForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

theorem words_comparable_or_disagree (u v : List Bool) :
    (∃ s, v = u ++ s) ∨ (∃ s, u = v ++ s) ∨
      ∃ (n : ℕ) (hu : n < u.length) (hv : n < v.length), u[n]'hu ≠ v[n]'hv := by
  induction u generalizing v with
  | nil => exact Or.inl ⟨v,rfl⟩
  | cons a u ih =>
    cases v with
    | nil => exact Or.inr (Or.inl ⟨a :: u,rfl⟩)
    | cons b v =>
      by_cases h : a = b
      · subst b
        rcases ih v with ⟨s,hs⟩ | ⟨s,hs⟩ | ⟨n,hn,hm,hne⟩
        · exact Or.inl ⟨s,congrArg (List.cons a) hs⟩
        · exact Or.inr (Or.inl ⟨s,congrArg (List.cons a) hs⟩)
        · exact Or.inr (Or.inr ⟨n+1, by simpa using Nat.succ_lt_succ hn,
            by simpa using Nat.succ_lt_succ hm, by simpa using hne⟩)
      · exact Or.inr (Or.inr ⟨0, by simp, by simp, by simpa using h⟩)

theorem wordValue_disjoint_of_disagree (i : I) (u v : List Bool)
    (n : ℕ) (hu : n < u.length) (hv : n < v.length) (h : u[n]'hu ≠ v[n]'hv) :
    Disjoint (wordValue B i u) (wordValue B i v) :=
  ((bitSlice_disjoint (B := B) (i,n) h).mono_left
    (iInf_le (fun k : Fin u.length => bitSlice B (i,k.val) (u.get k)) ⟨n,hu⟩)).mono_right
    (iInf_le (fun k : Fin v.length => bitSlice B (i,k.val) (v.get k)) ⟨n,hv⟩)

end JSP000930.Positive.Cohen
