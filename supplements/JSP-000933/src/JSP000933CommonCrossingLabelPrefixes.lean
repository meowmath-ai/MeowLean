import JSP000933ActualCrossingCliquesCountable

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

def labelsComparable (u v : Word) : Prop := List.IsPrefix u v ∨ List.IsPrefix v u

def labelsIncomp (u v : Word) : Prop := ¬ labelsComparable u v

theorem labelsComparable_symm_r255 {u v : Word} (h : labelsComparable u v) : labelsComparable v u :=
  Or.symm h

private theorem take_of_take_r255 {A : Type*} (w : List A) (i j : ℕ) (h : i≤j) :
    (w.take j).take i = w.take i := by
  induction i generalizing j w with
  | zero => simp
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases w with
      | nil => simp
      | cons x w => simp [List.take,ih (w := w) (j := j) (Nat.le_of_succ_le_succ h)]

theorem prefixes_comparable_common_r255 {u v w : Word}
    (hu : List.IsPrefix u w) (hv : List.IsPrefix v w) : labelsComparable u v := by
  have hU := List.prefix_iff_eq_take.mp hu
  have hV := List.prefix_iff_eq_take.mp hv
  rcases le_total u.length v.length with h | h
  · apply Or.inl
    apply List.prefix_iff_eq_take.mpr
    rw [hV,take_of_take_r255 w _ _ h]
    exact hU
  · apply Or.inr
    apply List.prefix_iff_eq_take.mpr
    rw [hU,take_of_take_r255 w _ _ h]
    exact hV

theorem commonComparable_prefix_left_r255 {u v w : Word}
    (h : labelsIncomp u v) (hu : labelsComparable w u) (hv : labelsComparable w v) :
    List.IsPrefix w u := by
  rcases hu with he | hu
  · exact he
  · rcases hv with ht | ht
    · exact False.elim (h (Or.inl (hu.trans ht)))
    · exact False.elim (h (prefixes_comparable_common_r255 hu ht))

theorem labelPrefixIndices_finite_r255 (e : ℕ ↪ Word) (u : Word) :
    {k : ℕ | List.IsPrefix (e k) u}.Finite := by
  let v := (Finset.range (u.length + 1)).image (fun j => u.take j)
  have hfin : (e ⁻¹' (v : Set Word)).Finite := Set.Finite.preimage_embedding e v.finite_toSet
  apply hfin.subset
  intro k hk
  have hTake := List.prefix_iff_eq_take.mp hk
  obtain ⟨s,hs⟩ := hk
  have hlen := congrArg List.length hs
  simp only [List.length_append] at hlen
  change e k ∈ v
  exact Finset.mem_image.mpr ⟨(e k).length,Finset.mem_range.mpr (by omega),hTake.symm⟩

noncomputable def sharedLabelIndices (e : ℕ ↪ Word) (i j : ℕ) : Finset ℕ := by
  classical
  exact ((labelPrefixIndices_finite_r255 e (e i)).toFinset).filter (fun k => List.IsPrefix (e k) (e j))

@[simp] theorem mem_sharedLabelIndices_r255 (e : ℕ ↪ Word) (i j m : ℕ) :
    m ∈ sharedLabelIndices e i j ↔ List.IsPrefix (e m) (e i) ∧ List.IsPrefix (e m) (e j) := by
  classical
  simp [sharedLabelIndices]

theorem sharedLabelIndices_comm_r255 (e : ℕ ↪ Word) (i j : ℕ) :
    sharedLabelIndices e i j = sharedLabelIndices e j i := by
  ext m
  simp only [mem_sharedLabelIndices_r255,and_comm]

noncomputable def commonLabelBound (e : ℕ ↪ Word) (i j : ℕ) : ℕ :=
  (sharedLabelIndices e i j).sup id + 1

theorem lt_commonLabelBound_r255 (e : ℕ ↪ Word) (i j m : ℕ)
    (hm : m∈sharedLabelIndices e i j) : m<commonLabelBound e i j :=
  Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)

theorem commonComparable_mem_shared_r255 (e : ℕ ↪ Word) (i j m : ℕ)
    (h : labelsIncomp (e i) (e j))
    (hI : labelsComparable (e m) (e i)) (hJ : labelsComparable (e m) (e j)) :
    m∈sharedLabelIndices e i j := by
  have h' : labelsIncomp (e j) (e i) := fun hh => h (labelsComparable_symm_r255 hh)
  exact (mem_sharedLabelIndices_r255 e i j m).mpr
    ⟨commonComparable_prefix_left_r255 h hI hJ,commonComparable_prefix_left_r255 h' hJ hI⟩

end SetLanguage
end JSP000933
