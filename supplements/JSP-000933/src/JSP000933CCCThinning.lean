import JSP000933CCCAvoidance

namespace JSP000933
namespace OpenGraphForcing

universe u

theorem exists_fixedCard_uncountable_r59 {X : Type u} (F : Set (Finset X))
    (hF : ¬ F.Countable) :
    ∃ n : ℕ, ¬ {a : Finset X | a ∈ F ∧ a.card = n}.Countable := by
  classical
  by_contra hNone
  have hEach (n : ℕ) : ({a : Finset X | a ∈ F ∧ a.card = n}).Countable := by
    by_contra h
    exact hNone ⟨n,h⟩
  apply hF
  apply (Set.countable_iUnion hEach).mono
  intro a ha
  exact Set.mem_iUnion.mpr ⟨a.card,ha,rfl⟩

private theorem exists_disjoint_next_r59 {X E : Type u} [Countable E]
    (F : Set (Finset X)) (hF : ¬ F.Countable)
    (hit : ∀ x : X, {s : Finset X | s ∈ F ∧ x ∈ s}.Countable)
    (old : E → Finset X) :
    ∃ q ∈ F, ∀ e, q ≠ old e ∧ Disjoint q (old e) := by
  classical
  let S : Set X := ⋃ e : E, (old e : Set X)
  have hS : S.Countable := Set.countable_iUnion (fun e => (old e).finite_toSet.countable)
  letI : Countable S := hS.to_subtype
  let T : Set (Finset X) := Set.range old ∪ ⋃ x : S, {s : Finset X | s ∈ F ∧ x.1 ∈ s}
  have hT : T.Countable := (Set.countable_range old).union (Set.countable_iUnion (fun x => hit x.1))
  have hSub : ¬ F ⊆ T := fun h => hF (hT.mono h)
  obtain ⟨q,hq,hNot⟩ := Set.not_subset.mp hSub
  refine ⟨q,hq,fun e => ⟨?_,?_⟩⟩
  · intro h
    exact hNot (Or.inl ⟨e,h.symm⟩)
  · rw [Finset.disjoint_left]
    intro x hxq hxe
    have hxS : x ∈ S := Set.mem_iUnion.mpr ⟨e,hxe⟩
    exact hNot (Or.inr (Set.mem_iUnion.mpr ⟨⟨x,hxS⟩,hq,hxq⟩))

theorem exists_disjoint_uncountable_subfamily_r59 {X ι : Type u}
    [LinearOrder ι] [WellFoundedLT ι]
    (hι : ¬ Countable ι) (small : ∀ j : ι, Countable (↥(Set.Iio j)))
    (F : Set (Finset X)) (hF : ¬ F.Countable)
    (hit : ∀ x : X, {s : Finset X | s ∈ F ∧ x ∈ s}.Countable) :
    ∃ G : Set (Finset X), G ⊆ F ∧ ¬ G.Countable ∧
      ∀ a ∈ G, ∀ b ∈ G, a ≠ b → Disjoint a b := by
  classical
  let take (j : ι) (old : ∀ i : ι, i < j → Finset X) : Finset X := by
    letI : Countable (↥(Set.Iio j)) := small j
    exact Classical.choose (exists_disjoint_next_r59 F hF hit (fun (i : ↥(Set.Iio j)) => old i.1 i.2))
  let s : ι → Finset X := WellFounded.fix wellFounded_lt take
  have hEq (j : ι) : s j = take j (fun i _ => s i) := WellFounded.fix_eq wellFounded_lt take j
  have hS (j : ι) : s j ∈ F ∧ ∀ i < j, s j ≠ s i ∧ Disjoint (s j) (s i) := by
    letI : Countable (↥(Set.Iio j)) := small j
    rw [hEq j]
    have hs := Classical.choose_spec (exists_disjoint_next_r59 F hF hit (fun i : ↥(Set.Iio j) => s i.1))
    exact ⟨hs.1,fun i hi => hs.2 ⟨i,hi⟩⟩
  have hInj : Function.Injective s := by
    intro i j h
    rcases lt_trichotomy i j with hij | hEq | hji
    · exact False.elim (((hS j).2 i hij).1 h.symm)
    · exact hEq
    · exact False.elim (((hS i).2 j hji).1 h)
  refine ⟨Set.range s,?_,?_,?_⟩
  · rintro _ ⟨j,rfl⟩
    exact (hS j).1
  · intro h
    have hAll : (Set.univ : Set ι).Countable :=
      (h.preimage hInj).mono (show (Set.univ : Set ι) ⊆ s ⁻¹' Set.range s from fun i _ => Set.mem_range_self i)
    exact hι (Set.countable_univ_iff.mp hAll)
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ h
    rcases lt_or_gt_of_ne (fun he => h (congrArg s he)) with hij | hji
    · exact (((hS j).2 i hij).2).symm
    · exact ((hS i).2 j hji).2

def FiniteClique {X : Type u} (K : Set (X × X)) (a : Finset X) : Prop :=
  ∀ x ∈ a, ∀ y ∈ a, x ≠ y → (x,y) ∈ K

theorem FiniteClique.subset_r59 {X : Type u} {K : Set (X × X)} {a b : Finset X}
    (h : FiniteClique K a) (hba : b ⊆ a) : FiniteClique K b :=
  fun x hx y hy hxy => h x (hba hx) y (hba hy) hxy

theorem restore_shared_vertex_r59 {X : Type u} [DecidableEq X] {K : Set (X × X)}
    {a b : Finset X} {c : X} (ha : FiniteClique K a) (hb : FiniteClique K b)
    (hca : c ∈ a) (hcb : c ∈ b) (hE : FiniteClique K (a.erase c ∪ b.erase c)) :
    FiniteClique K (a ∪ b) := by
  intro x hx y hy hxy
  by_cases hxc : x = c
  · subst x
    rcases Finset.mem_union.mp hy with h | h
    · exact ha c hca y h hxy
    · exact hb c hcb y h hxy
  · by_cases hyc : y = c
    · subst y
      rcases Finset.mem_union.mp hx with h | h
      · exact ha x h c hca hxy
      · exact hb x h c hcb hxy
    · have hxe : x ∈ a.erase c ∪ b.erase c := by
        rcases Finset.mem_union.mp hx with h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hxc,h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hxc,h⟩))
      have hye : y ∈ a.erase c ∪ b.erase c := by
        rcases Finset.mem_union.mp hy with h | h
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_erase.mpr ⟨hyc,h⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_erase.mpr ⟨hyc,h⟩))
      exact hE x hxe y hye hxy

theorem eraseOnContaining_injective_r59 {X : Type u} [DecidableEq X] (c : X) :
    Function.Injective (fun a : {a : Finset X // c ∈ a} => a.1.erase c) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (insert c) hab
  simpa only [Finset.insert_erase a.2,Finset.insert_erase b.2] using h

end OpenGraphForcing
end JSP000933
