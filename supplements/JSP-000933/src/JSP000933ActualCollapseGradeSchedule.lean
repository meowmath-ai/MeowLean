import JSP000933ActualBlockFixtureTower

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def CollapseBadAt {k : ℕ} (D : ActualBlockSnapshot k) (j : ℕ) : Prop :=
  ∃ x : BlockInput D.history, ¬GroundAllBudgets false 4 x.val ∧
    GroundAllBudgets true (dyadicGapDen j) (D.act x)

open scoped Classical in
noncomputable def collapsePick {k : ℕ} (D : ActualBlockSnapshot k) (j : ℕ) : BlockInput D.history :=
  if h : CollapseBadAt D j then Classical.choose h else emptyBlockInput D.history

theorem collapsePick_bad_spec_r377 {k : ℕ} {D : ActualBlockSnapshot k} {j : ℕ} (h : CollapseBadAt D j) :
    ¬GroundAllBudgets false 4 (collapsePick D j).val ∧
      GroundAllBudgets true (dyadicGapDen j) (D.act (collapsePick D j)) := by
  simpa only [collapsePick,dite_eq_left h] using (Classical.choose_spec h)

theorem collapsePick_good_empty_r377 {k : ℕ} {D : ActualBlockSnapshot k} {j : ℕ} (h : ¬CollapseBadAt D j) :
    collapsePick D j=emptyBlockInput D.history := by simp only [collapsePick,dite_eq_right h]

open scoped Classical in
noncomputable def fixtureGradeAt {n : ℕ} (A : BlockFixture n) : ℕ → ℕ
  | 0 => 0
  | k+1 =>
    if h : k<n then
      if CollapseBadAt (fixtureSnapshot A ⟨k,h⟩) (fixtureGradeAt A k) then fixtureGradeAt A k+1
      else fixtureGradeAt A k
    else fixtureGradeAt A k

def fixtureHit {n : ℕ} (A : BlockFixture n) (i : Fin n) : Prop :=
  CollapseBadAt (fixtureSnapshot A i) (fixtureGradeAt A i.val)

theorem fixtureGrade_hit_r377 {n : ℕ} (A : BlockFixture n) (i : Fin n) (h : fixtureHit A i) :
    fixtureGradeAt A (i.val+1)=fixtureGradeAt A i.val+1 := by
  change CollapseBadAt (fixtureSnapshot A ⟨i.val, i.isLt⟩) (fixtureGradeAt A i.val) at h
  simp only [fixtureGradeAt, dite_eq_left i.isLt, ite_eq_left h]

theorem fixtureGrade_miss_r377 {n : ℕ} (A : BlockFixture n) (i : Fin n) (h : ¬fixtureHit A i) :
    fixtureGradeAt A (i.val+1)=fixtureGradeAt A i.val := by
  change ¬CollapseBadAt (fixtureSnapshot A ⟨i.val, i.isLt⟩) (fixtureGradeAt A i.val) at h
  simp only [fixtureGradeAt, dite_eq_left i.isLt, ite_eq_right h]

theorem fixtureGrade_mono_r377 {n : ℕ} (A : BlockFixture n) : Monotone (fixtureGradeAt A) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k<n
  · by_cases h : fixtureHit A ⟨k,hk⟩
    · rw [fixtureGrade_hit_r377 A ⟨k,hk⟩ h]
      exact Nat.le_succ _
    · rw [fixtureGrade_miss_r377 A ⟨k,hk⟩ h]
  · simp only [fixtureGradeAt,dite_eq_right hk,le_rfl]

theorem fixtureGrade_le_index_r377 {n : ℕ} (A : BlockFixture n) (k : ℕ) : fixtureGradeAt A k≤k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    by_cases hk : k<n
    · by_cases h : fixtureHit A ⟨k,hk⟩
      · rw [fixtureGrade_hit_r377 A ⟨k,hk⟩ h]
        exact Nat.succ_le_succ ih
      · rw [fixtureGrade_miss_r377 A ⟨k,hk⟩ h]
        exact ih.trans (Nat.le_succ _)
    · rw [fixtureGradeAt,dite_eq_right hk]
      exact ih.trans (Nat.le_succ _)

theorem fixtureGrade_prefix_congr_r377 {n N : ℕ} (hN : n≤N) (A : BlockFixture N) (C : BlockFixture n)
    (hE : ∀ i : Fin n, fixtureSnapshot A ⟨i.val,i.isLt.trans_le hN⟩=fixtureSnapshot C i) :
    ∀ k≤n, fixtureGradeAt A k=fixtureGradeAt C k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hK
    have hk : k<n := Nat.lt_of_succ_le hK
    have hKN : k<N := hk.trans_le hN
    have he : fixtureSnapshot A ⟨k,hKN⟩ = fixtureSnapshot C ⟨k,hk⟩ := hE ⟨k,hk⟩
    simp only [fixtureGradeAt, dite_eq_left hKN, dite_eq_left hk]
    rw [he, ih hk.le]

theorem fixtureGrade_hit_injective_r377 {n : ℕ} (A : BlockFixture n) {i j : Fin n}
    (hi : fixtureHit A i) (hj : fixtureHit A j) (h : fixtureGradeAt A i.val=fixtureGradeAt A j.val) : i=j := by
  apply Fin.ext
  rcases lt_trichotomy i.val j.val with hlt | he | hgt
  · have hh := fixtureGrade_mono_r377 A (Nat.succ_le_of_lt hlt)
    rw [fixtureGrade_hit_r377 A i hi,h] at hh
    omega
  · exact he
  · have hh := fixtureGrade_mono_r377 A (Nat.succ_le_of_lt hgt)
    rw [fixtureGrade_hit_r377 A j hj,← h] at hh
    omega

end SetLanguage
end JSP000933
