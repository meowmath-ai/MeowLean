import JSP000933RelativeNextDisjointLabel

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

structure RelativeDisjointLabels (W : OmegaOneIndex→Finset OmegaOneIndex→B) (m : B) where
  pick : OmegaOneIndex→DiscreteChoiceOn LabelCandidate m
  admissible : ∀ i x,(pick i).value x≤W x.1 x.2
  increasing : ∀ i j,i<j→∀ y,(pick j).value y≤
    guardByChoice (pick i) (fun z => laterDisjointValue z y)

theorem exists_relativeDisjointLabels_r448 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (m : B)
    (hU : m≤unboundedValue (rowLabelWeight W))
    (hF : ∀ v,m≤(unboundedValue (vertexFiber W v))ᶜ) :
    Nonempty (RelativeDisjointLabels W m) := by
  classical
  let Good := {C : DiscreteChoiceOn LabelCandidate m // ∀ x,C.value x≤W x.1 x.2}
  have hStep (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i<j→Good) :
      ∃ C : DiscreteChoiceOn LabelCandidate m,(∀ x,C.value x≤W x.1 x.2) ∧
        ∀ (i : ↥(Set.Iio j)) y,C.value y≤guardByChoice (prev i.val i.property).val
          (fun z => laterDisjointValue z y) := by
    letI : Countable (↥(Set.Iio j)) := OmegaOneIndex_initial_countable_r61 j
    exact exists_nextDisjointLabel_r447 hB W m hU hF (fun i : ↥(Set.Iio j) => (prev i.val i.property).val)
  let take (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i<j→Good) : Good :=
    ⟨Classical.choose (hStep j prev),(Classical.choose_spec (hStep j prev)).1⟩
  let seq : OmegaOneIndex→Good := WellFounded.fix wellFounded_lt take
  have hSeq (j : OmegaOneIndex) : seq j=take j (fun i _ => seq i) :=
    WellFounded.fix_eq wellFounded_lt take j
  refine ⟨⟨fun i => (seq i).val,fun i => (seq i).property,fun i j hij y => ?_⟩⟩
  change (seq j).val.value y≤guardByChoice (seq i).val (fun z => laterDisjointValue z y)
  conv_lhs => rw [hSeq j]
  exact (Classical.choose_spec (hStep j (fun i _ => seq i))).2 ⟨i,hij⟩ y

theorem relativeDisjointLabels_overlap_r448 {W : OmegaOneIndex→Finset OmegaOneIndex→B}
    {m : B} (S : RelativeDisjointLabels W m) {i j : OmegaOneIndex} (hij : i<j)
    (x y : LabelCandidate) :
    (S.pick i).value x⊓(S.pick j).value y≤laterDisjointValue x y := by
  rw [inf_comm]
  exact (inf_le_inf (S.increasing i j hij y) le_rfl).trans
    (guardByChoice_elim_r445 (S.pick i) (fun z => laterDisjointValue z y) x)

end RelativeOCA
end JSP000933
