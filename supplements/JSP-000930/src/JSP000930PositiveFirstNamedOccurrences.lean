import JSP000930PositiveWeightedInjectionGraphs
import JSP000933RelativeChoiceNormalization

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.RelativeOCA

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B] [LinearOrder I] [WellFoundedLT I]

noncomputable def firstNamedOccurrence (x : I → bSet B) (i : I) : B :=
  (⨆ j : {j : I // j < i}, x i =ᴮ x j.val)ᶜ

theorem firstNamedOccurrence_separates (x : I → bSet B) {i j : I} (hij : i ≠ j) :
    (firstNamedOccurrence x i ⊓ firstNamedOccurrence x j) ⊓
      (x i =ᴮ x j) = ⊥ := by
  apply le_bot_iff.mp
  rcases lt_or_gt_of_ne hij with h | h
  · have he : (x i =ᴮ x j) ≤ ⨆ k : {k : I // k < j}, x j =ᴮ x k.val :=
      (le_of_eq bv_eq_symm).trans (le_iSup (fun k : {k : I // k < j} => x j =ᴮ x k.val) ⟨i,h⟩)
    have h₁ : (firstNamedOccurrence x i ⊓ firstNamedOccurrence x j) ⊓
        (x i =ᴮ x j) ≤ firstNamedOccurrence x j := inf_le_left.trans inf_le_right
    have h₂ : (firstNamedOccurrence x i ⊓ firstNamedOccurrence x j) ⊓
        (x i =ᴮ x j) ≤ ⨆ k : {k : I // k < j}, x j =ᴮ x k.val :=
      inf_le_right.trans he
    exact (le_inf h₁ h₂).trans_eq (by
      simpa only [firstNamedOccurrence,inf_comm] using
        (inf_compl_eq_bot' : (⨆ k : {k : I // k < j}, x j =ᴮ x k.val) ⊓
          (⨆ k : {k : I // k < j}, x j =ᴮ x k.val)ᶜ = (⊥ : B)))
  · have he : (x i =ᴮ x j) ≤ ⨆ k : {k : I // k < i}, x i =ᴮ x k.val :=
      le_iSup (fun k : {k : I // k < i} => x i =ᴮ x k.val) ⟨j,h⟩
    have h₁ : (firstNamedOccurrence x i ⊓ firstNamedOccurrence x j) ⊓
        (x i =ᴮ x j) ≤ firstNamedOccurrence x i := inf_le_left.trans inf_le_left
    have h₂ : (firstNamedOccurrence x i ⊓ firstNamedOccurrence x j) ⊓
        (x i =ᴮ x j) ≤ ⨆ k : {k : I // k < i}, x i =ᴮ x k.val :=
      inf_le_right.trans he
    exact (le_inf h₁ h₂).trans_eq (by
      simpa only [firstNamedOccurrence,inf_comm] using
        (inf_compl_eq_bot' : (⨆ k : {k : I // k < i}, x i =ᴮ x k.val) ⊓
          (⨆ k : {k : I // k < i}, x i =ᴮ x k.val)ᶜ = (⊥ : B)))

theorem firstNamedOccurrence_covers (x : I → bSet B) (a : bSet B) :
    (⨆ i, a =ᴮ x i) ≤ ⨆ i, firstNamedOccurrence x i ⊓ (a =ᴮ x i) := by
  let U (i : I) : B := a =ᴮ x i
  rw [← firstChoiceCell_join_r435 U]
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply le_inf ?_ (firstChoiceCell_le_r435 U i)
  unfold firstNamedOccurrence
  apply le_compl_iff_disjoint_right.mpr
  apply disjoint_iSup_iff.mpr
  intro j
  apply disjoint_iff_inf_le.mpr
  let d := firstChoiceCell U i ⊓ (x i =ᴮ x j.val)
  have hd : d ≤ U j.val :=
    bv_trans (inf_le_left.trans (firstChoiceCell_le_r435 U i)) inf_le_right
  have hd' : d ≤ (priorChoiceJoin U i)ᶜ := inf_le_left.trans inf_le_right
  have hd'' : d ≤ priorChoiceJoin U i := hd.trans (le_iSup (fun k : {k : I // k < i} => U k.val) j)
  exact (le_inf hd' hd'').trans_eq (by rw [inf_comm,inf_compl_eq_bot'])

theorem injects_into_of_named_cover (x y : I → bSet B) (D R : bSet B)
    (hc : ∀ a,(a ∈ᴮ D) ≤ ⨆ i, (a =ᴮ x i))
    (hy : ∀ i,(⊤ : B) ≤ y i ∈ᴮ R)
    (hs : ∀ i j, i ≠ j → (y i =ᴮ y j) = ⊥) :
    (⊤ : B) ≤ injects_into D R := by
  classical
  apply weightedGraph_injects_into x y (firstNamedOccurrence x) D R
  · intro i j
    by_cases h : i = j
    · subst j
      exact bv_refl
    · rw [firstNamedOccurrence_separates x h]
      exact bot_le
  · intro i j
    by_cases h : i = j
    · subst j
      exact bv_refl
    · rw [hs i j h,inf_bot_eq]
      exact bot_le
  · exact fun a => (hc a).trans (firstNamedOccurrence_covers x a)
  · exact hy

end JSP000930.Positive
