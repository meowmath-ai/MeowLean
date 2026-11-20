import JSP000933ActualLexicographicLevels

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def lexAtWeight (f : Word → B) (n : ℕ) (u : Word) : B :=
  if u.length=n then namedLexWordWeight f u else ⊥

theorem iSup_lexAtWeight_r283 (f : Word → B) (n : ℕ) : (⨆ u, lexAtWeight f n u)=f [] := by
  rw [← namedLexLevel_value_r282 f n]
  unfold namedLexLevel
  apply le_antisymm
  · apply iSup_le
    intro u
    by_cases hu : u.length=n
    · rw [lexAtWeight,ite_eq_left hu]
      exact le_iSup (fun v : {v : Word // v.length = n} => namedLexWordWeight f v.val) ⟨u,hu⟩
    · rw [lexAtWeight,ite_eq_right hu]
      exact bot_le
  · apply iSup_le
    intro u
    exact le_iSup_of_le u.val (by simp only [lexAtWeight,ite_eq_left u.property,le_rfl])

noncomputable def lexWordPartition (f : Word → B) (n : ℕ) : IndexedPartition B Word (f []) where
  weight := lexAtWeight f n
  covers := iSup_lexAtWeight_r283 f n
  separate := by
    intro u v hne
    apply disjoint_iff_inf_le.mpr
    by_cases hu : u.length=n <;> by_cases hv : v.length=n
    · simpa only [lexAtWeight,ite_eq_left hu,ite_eq_left hv] using
        namedLexWordWeight_disjoint_sameLength_r282 f n u v hu hv hne
    · simp only [lexAtWeight,ite_eq_right hv,inf_bot_eq,le_rfl]
    · simp only [lexAtWeight,ite_eq_right hu,bot_inf_eq,le_rfl]
    · simp only [lexAtWeight,ite_eq_right hu,bot_inf_eq,le_rfl]

theorem partition_eq_of_weight_r283 {I : Type} {p : B} {P Q : IndexedPartition B I p}
    (h : P.weight=Q.weight) : P=Q := by
  obtain ⟨w,hW,hS⟩ := P
  obtain ⟨v,hV,hT⟩ := Q
  change w=v at h
  subst v
  rfl

theorem lexWordPartition_seed_r283 (f : Word → B) :
    lexWordPartition f 0=seedWordPartition (f []) [] := by
  apply partition_eq_of_weight_r283
  funext u
  by_cases hu : u=[]
  · subst u
    simp only [lexWordPartition,lexAtWeight,List.length_nil,ite_eq_left rfl,ite_true,
      namedLexWordWeight_nil_r281,seedWordPartition_weight_r217]
  · have hLen : u.length≠0 := fun he => hu (List.length_eq_zero_iff.mp he)
    simp only [lexWordPartition,lexAtWeight,ite_eq_right hLen,seedWordPartition,ite_eq_right hu]

theorem lexWordPartition_refines_r283 (f : Word → B) (n : ℕ) :
    WordPartitionRefines (lexWordPartition f n) (lexWordPartition f (n+1)) := by
  intro u v hne
  change lexAtWeight f n u⊓lexAtWeight f (n+1) v≠⊥ at hne
  have hu : u.length=n := by
    by_contra hn
    exact hne (by simp only [lexAtWeight,ite_eq_right hn,bot_inf_eq])
  have hv : v.length=n+1 := by
    by_contra hn
    exact hne (by simp only [lexAtWeight,ite_eq_right hn,inf_bot_eq])
  obtain ⟨w,b,hw,he⟩ := wordAt_succ_split_r282 v n hv
  have hWU : w=u := by
    by_contra hN
    apply hne
    apply le_bot_iff.mp
    simp only [lexAtWeight,ite_eq_left hu,ite_eq_left hv]
    have hChild : namedLexWordWeight f v≤namedLexWordWeight f w :=
      (congrArg (namedLexWordWeight f) he).le.trans (namedLexWordWeight_child_le_r282 f w b)
    exact (inf_le_inf_left _ hChild).trans
      (namedLexWordWeight_disjoint_sameLength_r282 f n u w hu hw (Ne.symm hN))
  rw [he,hWU]
  exact wordExtends_appendBit_r221 u b

noncomputable def actualLexTower (K : Word × Word → B) (x : ℕ → B) :
    WordPartitionTower B (actualFiberFeasible K x []) [] (fun _ => actualFiberFeasible K x) where
  level := lexWordPartition (actualFiberFeasible K x)
  seed := lexWordPartition_seed_r283 _
  step := lexWordPartition_refines_r283 _
  code := by
    intro n w
    change lexAtWeight _ _ w≤actualFiberFeasible K x w
    by_cases hw : w.length=n+1
    · rw [lexAtWeight,ite_eq_left hw]
      exact namedLexWordWeight_le_feasible_r281 _ (actualFiberFeasible_binary_r281 K x) w
    · rw [lexAtWeight,ite_eq_right hw]
      exact bot_le
  lengthBound := by
    intro n w hw
    change lexAtWeight _ n w=⊥
    rw [lexAtWeight,ite_eq_right (ne_of_lt hw)]

noncomputable def actualLexSelector (K : Word × Word → B) (x : ℕ → B) : ℕ → B :=
  (actualLexTower K x).limitBits

end SetLanguage
end JSP000933
