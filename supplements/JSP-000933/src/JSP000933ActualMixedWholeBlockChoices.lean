import JSP000933ActualUniformCapTower

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def actualBlockChoiceWeight (p : B) (d : ℕ → ℕ → B) (n i : ℕ) : B :=
  p⊓firstNatWeight (fun j => crispTruth B (n≤j)⊓actualIncludesBlock (d n) j) i

theorem actualBlockChoiceWeight_covers_r331 (p : B) (d : ℕ → ℕ → B)
    (hD : ∀ n, p≤actualLongBlockLarge (d n)) (n : ℕ) :
    (⨆ i, actualBlockChoiceWeight p d n i)=p := by
  unfold actualBlockChoiceWeight
  rw [← inf_iSup_eq,firstNatWeight_covers_r317]
  apply inf_eq_left.mpr
  apply ((hD n).trans (iInf_le _ n)).trans
  apply iSup_le
  intro i
  apply le_iSup_of_le i.val
  exact le_inf (by simpa only [crispTruth,ite_eq_left i.property] using
    (le_top : actualIncludesBlock (d n) i.val≤⊤)) le_rfl

theorem actualBlockChoiceWeight_disjoint_r331 (p : B) (d : ℕ → ℕ → B) (n : ℕ)
    {i j : ℕ} (he : i≠j) :
    actualBlockChoiceWeight p d n i⊓actualBlockChoiceWeight p d n j≤⊥ :=
  (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)).trans
    (firstNatWeight_disjoint_r317 _ he)

theorem actualBlockChoiceWeight_index_r331 {p r : B} {d : ℕ → ℕ → B} {n i : ℕ}
    (hr : r≠⊥) (h : r≤actualBlockChoiceWeight p d n i) : n≤ i :=
  prop_of_le_crisp_nonzero_r190 hr (h.trans (inf_le_right.trans (inf_le_left.trans inf_le_left)))

theorem actualBlockChoiceWeight_whole_r331 (p : B) (d : ℕ → ℕ → B) (n i : ℕ) :
    actualBlockChoiceWeight p d n i≤actualIncludesBlock (d n) i :=
  inf_le_right.trans (inf_le_left.trans inf_le_right)

noncomputable def actualBlockChoiceUnion (p : B) (d : ℕ → ℕ → B) (m : ℕ) : B :=
  ⨆ n : ℕ, ⨆ i : ℕ, actualBlockChoiceWeight p d n i⊓crispTruth B (m∈justSourceBlock i)

theorem actualBlockChoiceUnion_large_r331 (p : B) (d : ℕ → ℕ → B)
    (hD : ∀ n, p≤actualLongBlockLarge (d n)) :
    p≤actualLongBlockLarge (actualBlockChoiceUnion p d) := by
  unfold actualLongBlockLarge
  apply le_iInf
  intro n
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨i,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq (actualBlockChoiceWeight p d n)
    (hqp.trans_eq (actualBlockChoiceWeight_covers_r331 p d hD n).symm)
  have hNI := actualBlockChoiceWeight_index_r331 hr hR
  refine ⟨r,hr,hrq,le_iSup_of_le ⟨i,hNI⟩ ?_⟩
  unfold actualIncludesBlock actualBlockChoiceUnion
  apply le_iInf
  intro m
  have hC : r≤crispTruth B (m.val∈justSourceBlock i) := by
    simpa only [crispTruth,ite_eq_left m.property] using (le_top : r≤⊤)
  exact le_iSup_of_le n (le_iSup_of_le i (le_inf hR hC))

end SetLanguage
end JSP000933
