import JSP000933ActualLargeFaceSplit
import Mathlib.SetTheory.Cardinal.Order

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def leastActiveWeight {I : Type} (v : I → B) (i : I) : B :=
  v i⊓(⨅ j : {j : I // WellOrderingRel j i}, (v j.val)ᶜ)

theorem iSup_leastActiveWeight_r309 {I : Type} (v : I → B) :
    (⨆ i, leastActiveWeight v i)=(⨆ i, v i) := by
  classical
  apply le_antisymm
  · exact iSup_le (fun i => le_iSup_of_le i inf_le_left)
  · apply le_of_dense_named_refinements_r219
    intro p hp hP
    obtain ⟨i,q,hq,hqp,hQ⟩ := exists_nonzero_below_choice_r135 p hp v hP
    let S : Set I := {i | p⊓v i≠⊥}
    have hS : S.Nonempty := ⟨i,fun he => hq (le_bot_iff.mp ((le_inf hqp hQ).trans_eq he))⟩
    obtain ⟨j,hJ,hMin⟩ := (WellOrderingRel.isWellOrder (α := I)).wf.has_min S hS
    let r := p⊓v j
    have hEarlier (k : {k : I // WellOrderingRel k j}) : r≤(v k.val)ᶜ := by
      apply le_compl_iff_disjoint_right.mpr
      apply disjoint_iff_inf_le.mpr
      have hBot : p⊓v k.val=⊥ := by
        by_contra hn
        exact hMin k.val hn k.property
      exact (le_inf (inf_le_left.trans inf_le_left) inf_le_right).trans_eq hBot
    exact ⟨r,hJ,inf_le_left,le_iSup_of_le j (le_inf inf_le_right (le_iInf hEarlier))⟩

theorem leastActiveWeight_disjoint_r309 {I : Type} (v : I → B) {i j : I} (hNe : i≠j) :
    leastActiveWeight v i⊓leastActiveWeight v j≤⊥ := by
  have hT : WellOrderingRel i j ∨ WellOrderingRel j i := by
    change embeddingToCardinal i<embeddingToCardinal j ∨ embeddingToCardinal j<embeddingToCardinal i
    exact lt_or_gt_of_ne (fun h => hNe (embeddingToCardinal.injective h))
  have hStep (i j : I) (h : WellOrderingRel i j) :
      leastActiveWeight v i⊓leastActiveWeight v j≤⊥ := by
    have hL : leastActiveWeight v i⊓leastActiveWeight v j≤v i := inf_le_left.trans inf_le_left
    have hR : leastActiveWeight v i⊓leastActiveWeight v j≤(v i)ᶜ :=
      inf_le_right.trans (inf_le_right.trans (iInf_le (fun k : {k : I // WellOrderingRel k j} => (v k.val)ᶜ) ⟨i,h⟩))
    exact (le_inf hL hR).trans_eq inf_compl_eq_bot'
  rcases hT with h | h
  · exact hStep i j h
  · exact (inf_comm _ _).le.trans (hStep j i h)

theorem leastActiveWeight_mask_r309 {I : Type} {v w : I → B} {p : B}
    (h : ∀ i, p⊓v i=p⊓w i) (i : I) :
    p⊓leastActiveWeight v i=p⊓leastActiveWeight w i :=
  mask_inf_congr_r126 (h i) (mask_iInf_congr_r126 (fun j => mask_compl_congr_r126 (h j.val)))

noncomputable def namedLeastChoice (R : (ℕ → B) → (ℕ → B) → B) (x : ℕ → B) (n : ℕ) : B :=
  ⨆ y : ℕ → B, leastActiveWeight (R x) y⊓y n

theorem leastActiveWeight_realEq_choice_r309 (R : (ℕ → B) → (ℕ → B) → B) (x y : ℕ → B) :
    leastActiveWeight (R x) y≤realEqValue (namedLeastChoice R x) y := by
  classical
  let p := leastActiveWeight (R x) y
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro n
  change p⊓namedLeastChoice R x n=p⊓y n
  apply le_antisymm
  · unfold namedLeastChoice
    rw [inf_iSup_eq]
    apply iSup_le
    intro z
    by_cases he : y=z
    · subst z
      exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
    · exact ((le_inf inf_le_left (inf_le_right.trans inf_le_left)).trans
        (leastActiveWeight_disjoint_r309 (R x) he)).trans bot_le
  · exact le_inf inf_le_left (le_iSup (fun z : ℕ → B => leastActiveWeight (R x) z ⊓ z n) y)

theorem namedLeastChoice_spec_r309 (R : (ℕ → B) → (ℕ → B) → B) (x : ℕ → B)
    (hExt : RealTestExt (R x)) :
    (⨆ y : ℕ → B, R x y)≤R x (namedLeastChoice R x) := by
  rw [← iSup_leastActiveWeight_r309 (R x)]
  apply iSup_le
  intro y
  let q := leastActiveWeight (R x) y
  have he : q≤realEqValue (namedLeastChoice R x) y := leastActiveWeight_realEq_choice_r309 R x y
  have hy : q≤R x y := inf_le_left
  have hh := hExt q (namedLeastChoice R x) y he
  exact ((le_inf le_rfl hy).trans_eq hh.symm).trans inf_le_right

theorem namedLeastChoice_mask_r309 (R : (ℕ → B) → (ℕ → B) → B)
    (hExt : ∀ z, RealTestExt (fun x => R x z)) {p : B} {x y : ℕ → B}
    (he : p≤realEqValue x y) : p≤realEqValue (namedLeastChoice R x) (namedLeastChoice R y) := by
  apply (le_realEqValue_iff_r126 _ _ _).mpr
  intro n
  unfold namedLeastChoice
  exact mask_iSup_congr_r126 (fun z => mask_inf_congr_r126
    (leastActiveWeight_mask_r309 (fun w => hExt w p x y he) z) rfl)

end SetLanguage
end JSP000933
