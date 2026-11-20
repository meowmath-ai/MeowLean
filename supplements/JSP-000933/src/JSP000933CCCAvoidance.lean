import JSP000933CCCExceptional

namespace JSP000933
namespace OpenGraphForcing

universe u

def UncountablyChromatic {X : Type u} (K : Set (X × X)) : Prop :=
  ¬ ∃ U : ℕ → Set X, (⋃ n, U n) = Set.univ ∧ ∀ n, Independent K (U n)

theorem Independent.empty_r58 {X : Type u} {K : Set (X × X)} :
    Independent K (∅ : Set X) := by simp [Independent]

theorem Independent.singleton_r58 {X : Type u} {K : Set (X × X)} (x : X)
    (hirr : ∀ x, (x,x) ∉ K) : Independent K ({x} : Set X) := by
  intro y hy z hz
  have hy' : y = x := Set.mem_singleton_iff.mp hy
  have hz' : z = x := Set.mem_singleton_iff.mp hz
  simpa only [hy',hz'] using hirr x

theorem exists_outside_countable_independents_r58 {X : Type u} {K : Set (X × X)}
    (hK : UncountablyChromatic K) (S : Set (Set X)) (hS : S.Countable)
    (hInd : ∀ s ∈ S, Independent K s) : ∃ x : X, ∀ s ∈ S, x ∉ s := by
  classical
  by_contra hNo
  have hCov (x : X) : ∃ s ∈ S, x ∈ s := by
    by_contra hn
    exact hNo ⟨x,fun s hs hx => hn ⟨s,hs,hx⟩⟩
  let D : Set (Set X) := insert ∅ S
  have hD : D.Countable := hS.insert _
  obtain ⟨U,hU⟩ := hD.exists_eq_range (show D.Nonempty from ⟨∅,Set.mem_insert _ _⟩)
  apply hK
  refine ⟨U,?_ ,fun n => ?_⟩
  · ext x
    have hx := hCov x
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      obtain ⟨s,hs,hxs⟩ := hx
      have hd : s ∈ Set.range U := by rw [← hU]; exact Set.mem_insert_of_mem _ hs
      obtain ⟨n,rfl⟩ := hd
      exact Set.mem_iUnion.mpr ⟨n,hxs⟩
  · have hh : U n ∈ D := by rw [hU]; exact Set.mem_range_self _
    rcases Set.mem_insert_iff.mp hh with h | h
    · simpa only [h] using Independent.empty_r58 (K := K)
    · exact hInd _ h

variable {X ι : Type u} [TopologicalSpace X] [LinearOrder ι]

structure AvoidanceSchedule (X ι : Type u) where
  closedCode : ι → Set X
  graphCode : ι → Σ n : ℕ, Set (Sample X n)

def AvoidsEarlier (K : Set (X × X)) (S : AvoidanceSchedule X ι)
    (j : ι) (old : ↥(Set.Iio j) → X) (x : X) : Prop :=
  (∀ i : ↥(Set.Iio j), x ≠ old i) ∧
  (∀ e : ↥(Set.Iio j), Independent K (S.closedCode e.1) → x ∉ S.closedCode e.1) ∧
  ∀ e : ↥(Set.Iio j), ∀ p : Fin (S.graphCode e.1).1 → ↥(Set.Iio j),
    Independent K (edgeCluster K (S.graphCode e.1).2 (fun i => old (p i))) →
      x ∉ edgeCluster K (S.graphCode e.1).2 (fun i => old (p i))

theorem exists_avoidanceStage_r58 {K : Set (X × X)} (hK : UncountablyChromatic K)
    (hirr : ∀ x, (x,x) ∉ K) (S : AvoidanceSchedule X ι) (j : ι)
    [Countable (↥(Set.Iio j))]
    (old : ↥(Set.Iio j) → X) :
    ∃ x : X, AvoidsEarlier K S j old x := by
  classical
  let E := ↥(Set.Iio j)
  let I := Σ e : E, Fin (S.graphCode e.1).1 → E
  let prev (i : E) : Set X := {old i}
  let closed (i : E) : Set X := if Independent K (S.closedCode i.1) then S.closedCode i.1 else ∅
  let raw (p : I) : Set X :=
    edgeCluster K (S.graphCode p.1.1).2 (fun i => old (p.2 i))
  let C (p : I) : Set X := if Independent K (raw p) then raw p else ∅
  let T : Set (Set X) := (Set.range prev ∪ Set.range closed) ∪ Set.range C
  have hT : T.Countable :=
    ((Set.countable_range prev).union (Set.countable_range closed)).union (Set.countable_range C)
  have hInd (U : Set X) (hU : U ∈ T) : Independent K U := by
    rcases hU with (h | h) | h
    · obtain ⟨i,rfl⟩ := h
      exact Independent.singleton_r58 (old i) hirr
    · obtain ⟨i,rfl⟩ := h
      dsimp only [closed]
      split
      · assumption
      · exact Independent.empty_r58
    · obtain ⟨i,rfl⟩ := h
      dsimp only [C]
      split
      · assumption
      · exact Independent.empty_r58
  obtain ⟨x,hx⟩ := exists_outside_countable_independents_r58 hK T hT hInd
  refine ⟨x,?_,?_,?_⟩
  · intro i h
    exact hx (prev i) (Or.inl (Or.inl (Set.mem_range_self _))) (Set.mem_singleton_iff.mpr h)
  · intro i h
    have hm := hx (closed i) (Or.inl (Or.inr (Set.mem_range_self _)))
    simpa only [closed,ite_eq_left h] using hm
  · intro e p hp
    have hm := hx (C ⟨e,p⟩) (Or.inr (Set.mem_range_self _))
    simpa only [C,raw,ite_eq_left hp] using hm

theorem exists_avoidingSequence_r58 [WellFoundedLT ι] {K : Set (X × X)}
    (hK : UncountablyChromatic K) (hirr : ∀ x, (x,x) ∉ K)
    (small : ∀ j : ι, Countable (↥(Set.Iio j))) (S : AvoidanceSchedule X ι) :
    ∃ seq : ι → X, Function.Injective seq ∧
      ∀ j, AvoidsEarlier K S j (fun i => seq i.1) (seq j) := by
  classical
  let next (j : ι) (prev : ∀ i : ι, i < j → X) : X := by
    letI : Countable (↥(Set.Iio j)) := small j
    exact Classical.choose (exists_avoidanceStage_r58 hK hirr S j (fun i => prev i.1 i.2))
  let seq : ι → X := WellFounded.fix wellFounded_lt next
  have hEq (j : ι) : seq j = next j (fun i _ => seq i) :=
    WellFounded.fix_eq wellFounded_lt next j
  have hAvoid (j : ι) : AvoidsEarlier K S j (fun i => seq i.1) (seq j) := by
    letI : Countable (↥(Set.Iio j)) := small j
    rw [hEq j]
    exact Classical.choose_spec (exists_avoidanceStage_r58 hK hirr S j (fun i => seq i.1))
  refine ⟨seq,fun i j h => ?_,hAvoid⟩
  rcases lt_trichotomy i j with hi | he | hj
  · exact False.elim ((hAvoid j).1 ⟨i,hi⟩ h.symm)
  · exact he
  · exact False.elim ((hAvoid i).1 ⟨j,hj⟩ h)

end OpenGraphForcing
end JSP000933
