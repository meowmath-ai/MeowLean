import JSP000930NegativeActualFiniteRowCountableFibres
import Mathlib.Logic.Equiv.Basic

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA

variable {B I K : Type} {D : I → Type} {E : K → Type}

noncomputable def rowProductQ_equivLabels [CompleteBooleanAlgebra B]
    (P : ∀ i,ValuedPoset B (D i)) (Q : ∀ k,ValuedPoset B (E k))
    (e : I ≃ K) (f : ∀ i,D i ≃ E (e i))
    (hV : ∀ i p,(Q (e i)).valid (f i p) = (P i).valid p)
    (hR : ∀ i p q,(Q (e i)).refines (f i p) (f i q) = (P i).refines p q) :
    WeightedDenseLabels (rowProductQ P) (rowProductQ Q) where
  label := e.piCongr f
  valid p := by
    apply le_antisymm
    · apply le_iInf
      intro i
      have h := iInf_le (fun k => (Q k).valid (e.piCongr f p k)) (e i)
      rw [Equiv.piCongr_apply_apply,hV] at h
      exact h
    · apply le_iInf
      intro k
      obtain ⟨i,rfl⟩ := e.surjective k
      rw [Equiv.piCongr_apply_apply,hV]
      exact iInf_le _ i
  refines p q := by
    apply le_antisymm
    · apply le_iInf
      intro i
      have h := iInf_le
        (fun k => (Q k).refines (e.piCongr f p k) (e.piCongr f q k)) (e i)
      rw [Equiv.piCongr_apply_apply,Equiv.piCongr_apply_apply,hR] at h
      exact h
    · apply le_iInf
      intro k
      obtain ⟨i,rfl⟩ := e.surjective k
      rw [Equiv.piCongr_apply_apply,Equiv.piCongr_apply_apply,hR]
      exact iInf_le _ i
  dense := by
    intro p m hm hp
    obtain ⟨a,rfl⟩ := (e.piCongr f).surjective p
    exact ⟨a,m,hm,le_rfl,hp.trans ((rowProductQ Q).refl _)⟩

noncomputable def distinguishRowIndex (i : I) : Unit ⊕ {j : I // j ≠ i} ≃ I := by
  classical
  refine ⟨Sum.elim (fun _ => i) Subtype.val,
    (fun j => if h : j = i then Sum.inl () else Sum.inr ⟨j,h⟩),?_,?_⟩
  · rintro (u|⟨j,hj⟩)
    · cases u
      simp
    · simp [hj]
  · intro j
    by_cases h : j = i
    · subst j; simp
    · simp [h]

noncomputable def rowProductQ_distinguish [NontrivialCompleteBooleanAlgebra B]
    (Q : ∀ i,ValuedPoset B (D i)) (i : I) :
    WeightedDenseLabels
      (rowProductQ (pointedRowFamily (Q i) (fun j : {j : I // j ≠ i} => Q j.val)))
      (rowProductQ Q) :=
  rowProductQ_equivLabels _ Q (distinguishRowIndex i)
    (fun j => by cases j <;> exact Equiv.refl _)
    (fun j => by cases j <;> exact fun _ => rfl)
    (fun j => by cases j <;> exact fun _ _ => rfl)

end JSP000930.Negative
