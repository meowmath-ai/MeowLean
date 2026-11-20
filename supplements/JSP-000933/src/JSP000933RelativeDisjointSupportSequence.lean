import JSP000933RelativeNextDisjointSupport

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B] [DecidableEq I]

structure RelativeDisjointSupports (W : OmegaOneIndex→Finset I→B) (m : B) where
  pick : OmegaOneIndex→DiscreteChoiceOn (SupportCandidate I) m
  admissible : ∀ i x,(pick i).value x≤W x.1 x.2
  increasing : ∀ i j,i<j→∀ y,(pick j).value y≤
    guardByChoice (pick i) (fun z => laterSupportDisjointValue z y)

theorem exists_relativeDisjointSupports_c15 (hB : BoundsCountableOmegaOneNames B)
    (W : OmegaOneIndex→Finset I→B) (m : B)
    (hU : m≤unboundedValue (rowSupportWeight W))
    (hF : ∀ v,m≤(unboundedValue (supportFiber W v))ᶜ) :
    Nonempty (RelativeDisjointSupports W m) := by
  classical
  let Good := {C : DiscreteChoiceOn (SupportCandidate I) m // ∀ x,C.value x≤W x.1 x.2}
  have hStep (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i<j→Good) :
      ∃ C : DiscreteChoiceOn (SupportCandidate I) m,(∀ x,C.value x≤W x.1 x.2) ∧
        ∀ (i : ↥(Set.Iio j)) y,C.value y≤guardByChoice (prev i.val i.property).val
          (fun z => laterSupportDisjointValue z y) := by
    letI : Countable (↥(Set.Iio j)) := OmegaOneIndex_initial_countable_r61 j
    exact exists_nextDisjointSupport_c14 hB W m hU hF (fun i : ↥(Set.Iio j) => (prev i.val i.property).val)
  let take (j : OmegaOneIndex) (prev : ∀ i : OmegaOneIndex,i<j→Good) : Good :=
    ⟨Classical.choose (hStep j prev),(Classical.choose_spec (hStep j prev)).1⟩
  let seq : OmegaOneIndex→Good := WellFounded.fix wellFounded_lt take
  have hSeq (j : OmegaOneIndex) : seq j=take j (fun i _ => seq i) :=
    WellFounded.fix_eq wellFounded_lt take j
  refine ⟨⟨fun i => (seq i).val,fun i => (seq i).property,fun i j hij y => ?_⟩⟩
  change (seq j).val.value y≤guardByChoice (seq i).val (fun z => laterSupportDisjointValue z y)
  conv_lhs => rw [hSeq j]
  exact (Classical.choose_spec (hStep j (fun i _ => seq i))).2 ⟨i,hij⟩ y

theorem relativeDisjointSupports_overlap_c15 {W : OmegaOneIndex→Finset I→B}
    {m : B} (S : RelativeDisjointSupports W m) {i j : OmegaOneIndex} (hij : i<j)
    (x y : (SupportCandidate I)) :
    (S.pick i).value x⊓(S.pick j).value y≤laterSupportDisjointValue x y := by
  rw [inf_comm]
  exact (inf_le_inf (S.increasing i j hij y) le_rfl).trans
    (guardByChoice_elim_r445 (S.pick i) (fun z => laterSupportDisjointValue z y) x)

end RelativeOCA
end JSP000933
