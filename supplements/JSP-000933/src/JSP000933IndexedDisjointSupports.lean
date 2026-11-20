import JSP000933BooleanRectangleThinning

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

private theorem exists_disjointLabelNext_r154 {I E : Type} [Countable E]
    (s : I → Finset OmegaOneIndex) (hI : ¬ Countable I)
    (hit : ∀ x, ({i : I | x ∈ s i} : Set I).Countable) (old : E → I) :
    ∃ i, ∀ j, i ≠ old j ∧ Disjoint (s i) (s (old j)) := by
  classical
  let Vert : Set OmegaOneIndex := ⋃ j : E, (s (old j) : Set OmegaOneIndex)
  have hV : Vert.Countable := Set.countable_iUnion (fun j : E => (s (old j)).finite_toSet.countable)
  letI : Countable (↥Vert) := hV.to_subtype
  let Bad : Set I := Set.range old ∪ ⋃ v : ↥Vert, {i : I | v.1 ∈ s i}
  have hB : Bad.Countable := (Set.countable_range old).union (Set.countable_iUnion (fun v => hit v.1))
  have hNot : ¬ (Set.univ : Set I) ⊆ Bad := fun h => hI (Set.countable_univ_iff.mp (hB.mono h))
  obtain ⟨i,_,hi⟩ := Set.not_subset.mp hNot
  refine ⟨i,fun j => ⟨fun he => hi (Or.inl ⟨j,he.symm⟩),?_⟩⟩
  rw [Finset.disjoint_left]
  intro v hv hOld
  exact hi (Or.inr (Set.mem_iUnion.mpr ⟨⟨v,Set.mem_iUnion.mpr ⟨j,hOld⟩⟩,hv⟩))

theorem exists_disjointLabelSequence_r154 {I : Type}
    (s : I → Finset OmegaOneIndex) (hI : ¬ Countable I)
    (hit : ∀ x, ({i : I | x ∈ s i} : Set I).Countable) :
    ∃ e : OmegaOneIndex → I, Function.Injective e ∧
      ∀ i j, i ≠ j → Disjoint (s (e i)) (s (e j)) := by
  classical
  let next (i : OmegaOneIndex) (old : ∀ j, j < i → I) : I := by
    letI : Countable (↥(Set.Iio i)) := OmegaOneIndex_initial_countable_r61 i
    exact Classical.choose (exists_disjointLabelNext_r154 s hI hit (fun j : ↥(Set.Iio i) => old j.1 j.2))
  let e : OmegaOneIndex → I := WellFounded.fix wellFounded_lt next
  have hNext (i : OmegaOneIndex) : e i = next i (fun j _ => e j) :=
    WellFounded.fix_eq wellFounded_lt next i
  have h (i : OmegaOneIndex) : ∀ j < i, e i ≠ e j ∧ Disjoint (s (e i)) (s (e j)) := by
    letI : Countable (↥(Set.Iio i)) := OmegaOneIndex_initial_countable_r61 i
    rw [hNext i]
    exact fun j hj => Classical.choose_spec (exists_disjointLabelNext_r154 s hI hit
      (fun j : ↥(Set.Iio i) => e j.1)) ⟨j,hj⟩
  refine ⟨e,fun i j he => ?_,fun i j hn => ?_⟩
  · rcases lt_trichotomy i j with hlt | heq | hlt
    · exact False.elim ((h j i hlt).1 he.symm)
    · exact heq
    · exact False.elim ((h i j hlt).1 he)
  · rcases lt_or_gt_of_ne hn with hlt | hlt
    · exact ((h j i hlt).2).symm
    · exact (h i j hlt).2

end CantorCodes
end JSP000933
