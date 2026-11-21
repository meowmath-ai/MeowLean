import JSP000930PositiveAppendOutsidePrefix

namespace JSP000930.Negative.Cohen

open JSP000930.Positive.Cohen JSP000933.MarkedForcing

variable {I : Type}

theorem wordMatches_of_refines {p q : Trace (I × ℕ)} (h : q ≤ p)
    {i : I} {w : List Bool} (hw : WordMatches p i w) : WordMatches q i w := by
  intro n
  obtain ⟨hm, hb⟩ := hw n
  change Extends q.1 p.1 at h
  exact ⟨h.1 hm, (h.2 _ hm).trans hb⟩

theorem exists_refine_word_only_row (p : Trace (I × ℕ)) (i : I) (w : List Bool)
    (hAgree : ∀ n : Fin w.length, (i,n.val) ∈ p.1.dom →
      p.1.bit (i,n.val) = w.get n) :
    ∃ q : Trace (I × ℕ), q ≤ p ∧ WordMatches q i w ∧ NoNewOtherRow p q i := by
  classical
  let a := wordConstraint i w
  have h : ∀ x ∈ p.1.dom, x ∈ a.dom → p.1.bit x = a.bit x := by
    rintro ⟨j, n⟩ hp hj
    obtain ⟨he, hn⟩ := (mem_wordConstraint i w (j,n)).mp hj
    change j = i at he
    subst j
    exact (hAgree ⟨n, hn⟩ hp).trans (wordConstraint_bit i w ⟨n, hn⟩).symm
  let q := normalize (merge p.1 a)
  have hp : q ≤ p := extends_trans (normalized_extends _) (merge_extends_left _ _)
  have ha : Extends q.1 a :=
    extends_trans (normalized_extends _) (merge_extends_right _ _ h)
  refine ⟨q, hp, ?_, ?_⟩
  · intro n
    have hn : (i,n.val) ∈ a.dom :=
      (mem_wordConstraint i w _).mpr ⟨rfl, n.isLt⟩
    exact ⟨ha.1 hn, (ha.2 _ hn).trans (wordConstraint_bit i w n)⟩
  · intro x hx hne
    change x ∈ p.1.dom ∪ a.dom at hx
    exact (Finset.mem_union.mp hx).elim id (fun ha =>
      (hne ((mem_wordConstraint i w x).mp ha).1).elim)

theorem exists_refine_vector_only_rows (p : Trace (I × ℕ)) (F : Finset I)
    (v : I → List Bool) :
    ∃ q : Trace (I × ℕ), q ≤ p ∧
      (∀ i ∈ F, WordMatches q i (completeRowWord p i ++ v i)) ∧
      (∀ x ∈ q.1.dom, x.1 ∉ F → x ∈ p.1.dom) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    exact ⟨p, le_rfl, (fun i hi => (Finset.notMem_empty i hi).elim),
      (fun _ hx _ => hx)⟩
  | @insert i F hi ih =>
    obtain ⟨q, hqp, hWords, hOutside⟩ := ih
    let w := completeRowWord p i ++ v i
    have hAgree : ∀ n : Fin w.length, (i,n.val) ∈ q.1.dom → q.1.bit (i,n.val) = w.get n := by
      intro n hn
      have hm := hOutside (i,n.val) hn hi
      change Extends q.1 p.1 at hqp
      exact (hqp.2 _ hm).trans (completeRowWord_agrees_append p i (v i) n hm)
    obtain ⟨r, hrq, hwi, hno⟩ := exists_refine_word_only_row q i w hAgree
    refine ⟨r, hrq.trans hqp, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hwi
      · exact wordMatches_of_refines hrq (hWords _ hj)
    · intro x hx hnot
      have hne : x.1 ≠ i := fun he => hnot (he.symm ▸ Finset.mem_insert_self i F)
      have hnot' : x.1 ∉ F := fun hf => hnot (Finset.mem_insert_of_mem hf)
      exact hOutside x (hno x hx hne) hnot'

end JSP000930.Negative.Cohen
