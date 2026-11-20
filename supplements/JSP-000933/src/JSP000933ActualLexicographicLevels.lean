import JSP000933ActualLexicographicWeights

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem wordAt_succ_split_r282 (u : Word) (n : ℕ) (hu : u.length=n+1) :
    ∃ w : Word, ∃ b : Bool, w.length=n ∧ u=w++[b] := by
  cases he : u.reverse with
  | nil =>
    have h := congrArg List.length he
    simp only [List.length_reverse,List.length_nil] at h
    omega
  | cons b w =>
    have h : u=w.reverse++[b] := by
      simpa only [List.reverse_reverse,List.reverse_cons] using congrArg List.reverse he
    refine ⟨w.reverse,b,?_,h⟩
    rw [h] at hu
    simp only [List.length_append,List.length_cons,List.length_nil] at hu
    omega

theorem namedLexWordWeight_child_le_r282 (f : Word → B) (u : Word) (b : Bool) :
    namedLexWordWeight f (u++[b])≤namedLexWordWeight f u := by
  cases b
  · rw [namedLexWordWeight_false_r281]
    exact inf_le_left
  · rw [namedLexWordWeight_true_r281]
    exact inf_le_left

theorem namedLexWordWeight_disjoint_sameLength_r282 (f : Word → B) (n : ℕ) :
    ∀ u v : Word, u.length=n → v.length=n → u≠v →
      namedLexWordWeight f u⊓namedLexWordWeight f v≤⊥ := by
  induction n with
  | zero =>
    intro u v hu hv hne
    have h₁ : u=[] := List.length_eq_zero_iff.mp hu
    have h₂ : v=[] := List.length_eq_zero_iff.mp hv
    exact (hne (h₁.trans h₂.symm)).elim
  | succ n ih =>
    intro w z hw hz hne
    obtain ⟨u,b,hu,rfl⟩ := wordAt_succ_split_r282 w n hw
    obtain ⟨v,c,hv,rfl⟩ := wordAt_succ_split_r282 z n hz
    by_cases he : u=v
    · subst v
      cases b <;> cases c
      · exact (hne rfl).elim
      · rw [namedLexWordWeight_false_r281,namedLexWordWeight_true_r281]
        exact ((le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans_eq
          inf_compl_eq_bot')
      · rw [inf_comm,namedLexWordWeight_false_r281,namedLexWordWeight_true_r281]
        exact ((le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans_eq
          inf_compl_eq_bot')
      · exact (hne rfl).elim
    · exact (inf_le_inf (namedLexWordWeight_child_le_r282 f u b)
        (namedLexWordWeight_child_le_r282 f v c)).trans (ih u v hu hv he)

noncomputable def namedLexLevel (f : Word → B) (n : ℕ) : B :=
  ⨆ w : {w : Word // w.length=n}, namedLexWordWeight f w.val

theorem namedLexLevel_succ_r282 (f : Word → B) (n : ℕ) :
    namedLexLevel f (n+1)=namedLexLevel f n := by
  unfold namedLexLevel
  apply le_antisymm
  · apply iSup_le
    intro w
    obtain ⟨u,b,hu,he⟩ := wordAt_succ_split_r282 w.val n w.property
    exact le_iSup_of_le ⟨u,hu⟩
      ((congrArg (namedLexWordWeight f) he).le.trans (namedLexWordWeight_child_le_r282 f u b))
  · apply iSup_le
    intro u
    rw [← namedLexWordWeight_split_r281 f u.val]
    apply sup_le
    · exact le_iSup (fun w : {w : Word // w.length = n+1} => namedLexWordWeight f w.val) ⟨u.val++[false],by simp [u.property]⟩
    · exact le_iSup (fun w : {w : Word // w.length = n+1} => namedLexWordWeight f w.val) ⟨u.val++[true],by simp [u.property]⟩

theorem namedLexLevel_value_r282 (f : Word → B) (n : ℕ) :
    namedLexLevel f n=f [] := by
  induction n with
  | zero =>
    unfold namedLexLevel
    apply le_antisymm
    · apply iSup_le
      intro u
      rw [List.length_eq_zero_iff.mp u.property,namedLexWordWeight_nil_r281]
    · exact le_iSup_of_le ⟨[],rfl⟩ le_rfl
  | succ n ih => rw [namedLexLevel_succ_r282,ih]

end SetLanguage
end JSP000933
