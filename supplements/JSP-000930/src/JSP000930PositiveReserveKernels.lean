import Mathlib.Order.CompleteBooleanAlgebra
import Mathlib.Data.Set.Function

namespace JSP000930.Positive

universe u v w

theorem exists_cutoff_without_small_palette
    {K : Type u} {I : Type v} {M : Type w}
    (cut : K → I) (hlarge : IsEmpty (K ↪ I × M)) :
    ∃ i : I, IsEmpty ({k : K // cut k = i} ↪ M) := by
  classical
  by_contra h
  have H (i : I) : Nonempty ({k : K // cut k = i} ↪ M) := by
    by_contra hi
    exact h ⟨i, ⟨fun x => hi ⟨x⟩⟩⟩
  let e (i : I) := Classical.choice (H i)
  let F : K → I × M := fun k => (cut k, e (cut k) ⟨k, rfl⟩)
  have hF : Function.Injective F := by
    intro k l hkl
    have hcut : cut k = cut l := congrArg Prod.fst hkl
    have hfiber (i : I) (hk : cut k = i) (hl : cut l = i)
        (hv : e i ⟨k, hk⟩ = e i ⟨l, hl⟩) : k = l :=
      congrArg Subtype.val ((e i).injective hv)
    apply hfiber (cut l) hcut rfl
    have hv : e (cut k) ⟨k, rfl⟩ = e (cut l) ⟨l, rfl⟩ := congrArg Prod.snd hkl
    have he : e (cut k) ⟨k, rfl⟩ = e (cut l) ⟨k, hcut⟩ := by
      have hx (i : I) (hi : cut k = i) :
          e (cut k) ⟨k, rfl⟩ = e i ⟨k, hi⟩ := by
        cases hi
        rfl
      exact hx (cut l) hcut
    exact he.symm.trans hv
  exact hlarge.false ⟨F, hF⟩

variable {B : Type u} [CompleteBooleanAlgebra B]

theorem value_eq_bot_of_dense_avoidance (a : B)
    (hdense : ∀ p : B, p ≠ ⊥ → ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ⊓ a = ⊥) :
    a = ⊥ := by
  by_contra ha
  obtain ⟨q, hq, hqa, hn⟩ := hdense a ha
  exact hq ((inf_eq_left.mpr hqa).symm.trans hn)

theorem family_separated_top_of_pairwise_dense_avoidance
    {K : Type v} (collision : K → K → B)
    (h : ∀ i j, i ≠ j → ∀ p : B, p ≠ ⊥ →
      ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ⊓ collision i j = ⊥) :
    (⨅ i : K, ⨅ j : K, ⨅ _ : i ≠ j, (collision i j)ᶜ) = ⊤ := by
  apply top_unique
  refine le_iInf fun i => le_iInf fun j => le_iInf fun hij => ?_
  rw [value_eq_bot_of_dense_avoidance (collision i j) (h i j hij), compl_bot]

end JSP000930.Positive
