import JSP000933ActualMixedWholeBlockChoices

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem capTower_below_of_le_r332 {p : B} (d : ℕ → ℕ → B)
    (h : ∀ n, p≤bitsBelowValue (d (n+1)) (d n)) :
    ∀ i j, i≤j → p≤bitsBelowValue (d j) (d i) := by
  intro i j
  induction j with
  | zero =>
    intro hI
    have he : i=0 := Nat.eq_zero_of_le_zero hI
    subst i
    exact bitsBelowValue_of_pointwise_r272 (fun _ => le_rfl)
  | succ j ih =>
    intro hI
    by_cases he : i=j+1
    · subst i
      exact bitsBelowValue_of_pointwise_r272 (fun _ => le_rfl)
    · have hIJ : i≤j := by omega
      exact bitsBelowValue_trans_r324 (h j) (ih hIJ)

theorem blockChoiceTerm_below_r332 (p : B) (d : ℕ → ℕ → B) (n i j m : ℕ)
    {q : B} (hq : q≤p) (hD : p≤bitsBelowValue (d n) (d j)) :
    q⊓(actualBlockChoiceWeight p d n i⊓crispTruth B (m∈justSourceBlock i))≤d j m := by
  by_cases h : m∈justSourceBlock i
  · have hW := (actualBlockChoiceWeight_whole_r331 p d n i).trans (iInf_le _ ⟨m,h⟩)
    exact (le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans hW))).trans
      (bitsBelowValue_apply_r256 (hq.trans hD) m)
  · simp [crispTruth,h]

theorem actualBlockChoiceUnion_belowFirst_r332 (p : B) (d : ℕ → ℕ → B)
    (hD : ∀ n, p≤bitsBelowValue (d (n+1)) (d n)) :
    p≤bitsBelowValue (actualBlockChoiceUnion p d) (d 0) := by
  unfold bitsBelowValue
  apply le_iInf
  intro m
  change p≤(actualBlockChoiceUnion p d m)ᶜ⊔d 0 m
  apply (le_materialImp_iff_r126 _ _ _).mpr
  unfold actualBlockChoiceUnion
  simp only [inf_iSup_eq]
  exact iSup_le (fun n => iSup_le (fun i =>
    blockChoiceTerm_below_r332 p d n i 0 m le_rfl (capTower_below_of_le_r332 d hD 0 n (Nat.zero_le _))))

theorem actualBlockChoiceUnion_boundedDifference_r332 (p : B) (d : ℕ → ℕ → B)
    (hLarge : ∀ n, p≤actualLongBlockLarge (d n)) (hD : ∀ n, p≤bitsBelowValue (d (n+1)) (d n))
    (j : ℕ) :
    p≤⨆ N : ℕ, afterCutDisjointValue (actualBlockChoiceUnion p d) (bitsComplement (d j)) N := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  have hQ : q≤⨅ n : Fin j, ⨆ i, actualBlockChoiceWeight p d n.val i :=
    le_iInf (fun n => hqp.trans_eq (actualBlockChoiceWeight_covers_r331 p d hLarge n.val).symm)
  obtain ⟨g,r,hr,hrq,hR⟩ := exists_nonzero_finiteChoices_fin_r135 j
    (fun n : Fin j => actualBlockChoiceWeight p d n.val) q hq hQ
  let N := (Finset.univ : Finset (Fin j)).sup (fun n => justSourceStart (g n+1))
  refine ⟨r,hr,hrq,le_iSup_of_le N (afterCutDisjointValue_intro_r268 (fun m hm => ?_))⟩
  have hSub : r⊓actualBlockChoiceUnion p d m≤d j m := by
    unfold actualBlockChoiceUnion
    simp only [inf_iSup_eq]
    apply iSup_le
    intro n
    apply iSup_le
    intro i
    by_cases h : n<j
    · let b : Fin j := ⟨n,h⟩
      by_cases he : i=g b
      · subst i
        have hBound : justSourceStart (g b+1)≤N :=
          Finset.le_sup (f := fun i : Fin j => justSourceStart (g i + 1)) (Finset.mem_univ b)
        have hn : m∉justSourceBlock (g b) := by
          intro hMem
          have hMem' : m∈Finset.Ico (justSourceStart (g b)) (justSourceStart (g b+1)) := hMem
          exact (not_lt_of_ge (hBound.trans hm)) (Finset.mem_Ico.mp hMem').2
        simp [crispTruth,hn]
      · exact ((le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans (hR b))).trans
          (actualBlockChoiceWeight_disjoint_r331 p d n he)).trans bot_le
    · exact blockChoiceTerm_below_r332 p d n i j m (hrq.trans hqp)
        (capTower_below_of_le_r332 d hD j n (Nat.le_of_not_gt h))
  exact (le_inf ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans hSub)
    (inf_le_right.trans inf_le_right)).trans_eq inf_compl_eq_bot'

end SetLanguage
end JSP000933
