import JSP000930PositiveActualBinaryWordCylinders

namespace JSP000930.Positive.Cohen

open JSP000933.MarkedForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

def NoNewOtherRow (p q : Trace (I × ℕ)) (i : I) : Prop :=
  ∀ x ∈ q.1.dom, x.1 ≠ i → x ∈ p.1.dom

def completeRowWord (p : Trace (I × ℕ)) (i : I) : List Bool :=
  List.ofFn (fun k : Fin (((p.1.dom.image Prod.snd).sup id) + 1) =>
    p.1.bit (i,k.val))

theorem completeRowWord_agrees_append (p : Trace (I × ℕ)) (i : I) (v : List Bool)
    (n : Fin (completeRowWord p i ++ v).length) (hn : (i,n.val) ∈ p.1.dom) :
    p.1.bit (i,n.val) = (completeRowWord p i ++ v).get n := by
  have he : n.val ≤ (p.1.dom.image Prod.snd).sup id :=
    Finset.le_sup (f := id) (show n.val ∈ p.1.dom.image Prod.snd from
      Finset.mem_image.mpr ⟨(i,n.val),hn,rfl⟩)
  have hu : n.val < (completeRowWord p i).length := by
    simpa only [completeRowWord,List.length_ofFn] using Nat.lt_succ_of_le he
  change p.1.bit (i,n.val) = (completeRowWord p i ++ v)[n.val]'n.isLt
  rw [List.getElem_append_left hu]
  simp only [completeRowWord,List.getElem_ofFn]

theorem exists_append_no_new_other_row (p : Trace (I × ℕ)) (i : I) (v : List Bool) :
    ∃ q : Trace (I × ℕ), q ≤ p ∧ WordMatches q i (completeRowWord p i ++ v) ∧
      NoNewOtherRow p q i := by
  classical
  let w := completeRowWord p i ++ v
  let a := wordConstraint i w
  have h : ∀ x ∈ p.1.dom,x ∈ a.dom → p.1.bit x = a.bit x := by
    rintro ⟨j,n⟩ hp hq
    obtain ⟨he,hn⟩ := (mem_wordConstraint i w (j,n)).mp hq
    change j = i at he
    subst j
    exact (completeRowWord_agrees_append p i v ⟨n,hn⟩ hp).trans
      (wordConstraint_bit i w ⟨n,hn⟩).symm
  let q := normalize (merge p.1 a)
  have hp : q ≤ p :=
    extends_trans (normalized_extends _) (merge_extends_left p.1 a)
  have ha : Extends q.1 a :=
    extends_trans (normalized_extends _) (merge_extends_right p.1 a h)
  refine ⟨q,hp,fun n => ?_,fun x hx hne => ?_⟩
  · have hn : (i,n.val) ∈ a.dom := (mem_wordConstraint i w _).mpr ⟨rfl,n.isLt⟩
    exact ⟨ha.1 hn,(ha.2 _ hn).trans (wordConstraint_bit i w n)⟩
  · change x ∈ p.1.dom ∪ a.dom at hx
    rcases Finset.mem_union.mp hx with hOld | hNew
    · exact hOld
    · exact False.elim (hne ((mem_wordConstraint i w x).mp hNew).1)

theorem restriction_unchanged_off_fresh_row {p q : Trace (I × ℕ)} {i : I}
    (hq : q ≤ p) (hNew : NoNewOtherRow p q i) (S : Set (I × ℕ))
    (hS : ∀ n,(i,n) ∉ S) :
    (restrict p S).1 ≤ (restrict q S).1 := by
  change Extends q.1 p.1 at hq
  change Extends (restrict p S).1.1 (restrict q S).1.1
  refine ⟨?_,?_⟩
  · intro x hx
    obtain ⟨hxq,hxS⟩ := (restrict_mem_dom q S x).mp hx
    have he : x.1 ≠ i := by
      intro h
      exact hS x.2 (show (i,x.2) ∈ S from (show x = (i,x.2) from Prod.ext h rfl) ▸ hxS)
    exact (restrict_mem_dom p S x).mpr ⟨hNew x hxq he,hxS⟩
  · intro x hx
    obtain ⟨hxq,hxS⟩ := (restrict_mem_dom q S x).mp hx
    have he : x.1 ≠ i := by
      intro h
      exact hS x.2 (show (i,x.2) ∈ S from (show x = (i,x.2) from Prod.ext h rfl) ▸ hxS)
    have hp := hNew x hxq he
    rw [restrict_bit_eq p S x hp hxS,restrict_bit_eq q S x hxq hxS]
    exact (hq.2 x hp).symm

end JSP000930.Positive.Cohen
