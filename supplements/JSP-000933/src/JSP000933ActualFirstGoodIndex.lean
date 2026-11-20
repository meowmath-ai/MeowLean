import JSP000933ActualRobustGoodAnchors

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def firstNatWeight (V : ℕ → B) (n : ℕ) : B :=
  V n⊓(⨅ m : Fin n, (V m.val)ᶜ)

theorem firstNatWeight_covers_r317 (V : ℕ → B) : (⨆ n, firstNatWeight V n)=(⨆ n, V n) := by
  classical
  apply le_antisymm
  · exact iSup_le (fun n => le_iSup_of_le n inf_le_left)
  · apply le_of_dense_named_refinements_r219
    intro p hp hP
    obtain ⟨j,q,hq,hqp,hJ⟩ := exists_nonzero_below_choice_r135 p hp V hP
    have he : ∃ n, p⊓V n≠⊥ := ⟨j,fun hz => hq (le_bot_iff.mp ((le_inf hqp hJ).trans_eq hz))⟩
    let n := Nat.find he
    let r := p⊓V n
    have hr : r≠⊥ := Nat.find_spec he
    have hc (m : Fin n) : r≤(V m.val)ᶜ := by
      apply le_compl_iff_disjoint_right.mpr
      apply disjoint_iff_inf_le.mpr
      have hz : p⊓V m.val=⊥ := not_not.mp (Nat.find_min he m.isLt)
      exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans_eq hz
    exact ⟨r,hr,inf_le_left,le_iSup_of_le n (le_inf inf_le_right (le_iInf hc))⟩

theorem firstNatWeight_disjoint_r317 (V : ℕ → B) {i j : ℕ} (hne : i≠j) :
    firstNatWeight V i⊓firstNatWeight V j≤⊥ := by
  have hStep (i j : ℕ) (h : i<j) : firstNatWeight V i⊓firstNatWeight V j≤⊥ := by
    have hL : firstNatWeight V i⊓firstNatWeight V j≤V i := inf_le_left.trans inf_le_left
    have hR : firstNatWeight V i⊓firstNatWeight V j≤(V i)ᶜ :=
      inf_le_right.trans (inf_le_right.trans (iInf_le _ (⟨i,h⟩ : Fin j)))
    exact (le_inf hL hR).trans_eq inf_compl_eq_bot'
  rcases lt_or_gt_of_ne hne with h | h
  · exact hStep i j h
  · exact (inf_comm _ _).le.trans (hStep j i h)

noncomputable def firstNamedIndexOutput (V : (ℕ → B) → ℕ → B)
    (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B) (m : ℕ) : B :=
  ⨆ i : ℕ, firstNatWeight (V x) i⊓f i x m

theorem firstNamedIndexOutput_mask_r317 (V : (ℕ → B) → ℕ → B)
    (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B) (i : ℕ) :
    firstNatWeight (V x) i≤realEqValue (firstNamedIndexOutput V f x) (f i x) := by
  let p := firstNatWeight (V x) i
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro m
  change p⊓firstNamedIndexOutput V f x m=p⊓f i x m
  apply le_antisymm
  · unfold firstNamedIndexOutput
    rw [inf_iSup_eq]
    apply iSup_le
    intro j
    by_cases he : i=j
    · subst j
      exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans
        (firstNatWeight_disjoint_r317 (V x) he)).trans bot_le
  · exact le_inf inf_le_left (le_iSup (fun j => firstNatWeight (V x) j ⊓ f j x m) i)

theorem firstNamedIndexOutput_tail_r317 (V : (ℕ → B) → ℕ → B)
    (f : ℕ → (ℕ → B) → ℕ → B) (R : (ℕ → B) → ℕ → B)
    (k : ℕ) {p : B} (x : ℕ → B) (hCov : p≤⨆ i, V x i)
    (hEach : ∀ i, p⊓V x i≤eventuallySmallError true k (f i x) (R x)) :
    p≤eventuallySmallError true k (firstNamedIndexOutput V f x) (R x) := by
  have h := hCov.trans_eq (firstNatWeight_covers_r317 (V x)).symm
  apply (le_inf le_rfl h).trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro i
  let q := p⊓firstNatWeight (V x) i
  have hQ : q≤eventuallySmallError true k (f i x) (R x) :=
    (inf_le_inf_left _ inf_le_left).trans (hEach i)
  have hM := eventuallySmallError_mask_r313 true k
    ((show q≤firstNatWeight (V x) i from inf_le_right).trans (firstNamedIndexOutput_mask_r317 V f x i))
    (le_top.trans_eq (realEqValue_refl_r127 (R x)).symm)
  exact ((le_inf le_rfl hQ).trans_eq hM.symm).trans inf_le_right

end SetLanguage
end JSP000933
