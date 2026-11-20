import JSP000933FiniteSupportPoset
import JSP000933BooleanCompletion

namespace JSP000933
namespace FiniteSupport

variable {A : Type} [LinearOrder A] {N : A → Type} {R : Rules N}

def mergeTrace (a : A) (p q r : Trace N) : Trace N :=
  fun i => if i < a then r i else
    match p i with
    | some s => some s
    | none => q i

private theorem cut_mergeTrace_lt_r76 {a i : A} (hi : i < a) (p q r : Trace N) :
    cut (mergeTrace a p q r) i = cut r i := by
  funext j
  by_cases hj : j < i
  · simp [cut,mergeTrace,hj,hj.trans hi]
  · simp [cut,hj]

theorem compatible_of_prefix_and_disjointTail_r76 (p q : Condition R) (a : A)
    (ha : ∀ i, present p.trace i → present q.trace i → i < a)
    (h : BooleanCompletion.Compatible (restrict p a) (restrict q a)) :
    BooleanCompletion.Compatible p q := by
  obtain ⟨r,hrp,hrq⟩ := h
  let m := mergeTrace a p.trace q.trace r.1.trace
  have hmLt (i : A) (hi : i < a) : m i = r.1.trace i := by
    simp [m,mergeTrace,hi]
  have hmCut (i : A) (hi : i < a) : cut m i = cut r.1.trace i :=
    cut_mergeTrace_lt_r76 hi _ _ _
  have hp : ∀ i, coordinateLE R.leAt i m p.trace := by
    intro i s hs
    by_cases hi : i < a
    · have hCut : cut p.trace a i = some s := (cut_apply_of_lt hi).trans hs
      obtain ⟨t,ht,hle⟩ := hrp i s hCut
      exact ⟨t,(hmLt i hi).trans ht,by
        rw [hmCut i hi]
        exact hle⟩
    · exact ⟨s,by simp [m,mergeTrace,hi,hs],R.refl ..⟩
  have hq : ∀ i, coordinateLE R.leAt i m q.trace := by
    intro i s hs
    by_cases hi : i < a
    · have hCut : cut q.trace a i = some s := (cut_apply_of_lt hi).trans hs
      obtain ⟨t,ht,hle⟩ := hrq i s hCut
      exact ⟨t,(hmLt i hi).trans ht,by
        rw [hmCut i hi]
        exact hle⟩
    · have hpNone : p.trace i = none := by
        cases hP : p.trace i with
        | none => rfl
        | some t => exact False.elim (hi (ha i ⟨t,hP⟩ ⟨s,hs⟩))
      exact ⟨s,by simp [m,mergeTrace,hi,hpNone,hs],R.refl ..⟩
  have hFinite : ({i | present m i} : Set A).Finite := by
    apply ((r.1.finite.union p.finite).union q.finite).subset
    rintro i ⟨s,hs⟩
    by_cases hi : i < a
    · exact Or.inl (Or.inl ⟨s,(hmLt i hi).symm.trans hs⟩)
    · cases hP : p.trace i with
      | none =>
        exact Or.inr ⟨s,by simpa [m,mergeTrace,hi,hP] using hs⟩
      | some t => exact Or.inl (Or.inr ⟨t,hP⟩)
  have hValid (i : A) (s : N i) (hs : m i = some s) : R.valid i (cut m i) s := by
    by_cases hi : i < a
    · rw [hmCut i hi]
      exact r.1.valid i s ((hmLt i hi).symm.trans hs)
    · cases hP : p.trace i with
      | none =>
        have hs' : q.trace i = some s := by simpa [m,mergeTrace,hi,hP] using hs
        exact R.persist_valid i _ _ s (fun j _ => hq j) (q.valid i s hs')
      | some t =>
        have hts : t = s := by simpa [m,mergeTrace,hi,hP] using hs
        have hs' : p.trace i = some s := hP.trans (congrArg some hts)
        exact R.persist_valid i _ _ s (fun j _ => hp j) (p.valid i s hs')
  exact ⟨⟨m,hFinite,hValid⟩,hp,hq⟩

end FiniteSupport
end JSP000933
