import JSP000933InternalAvoidanceStage

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem exists_BooleanAvoidanceSequence_r146
    (D : (ℕ → B) → B) (hD : RealTestExt D) (K : Word × Word → B) (p : B)
    (hNo : ∀ c : CoverCode B, p ≤ (goodCoverValue id D K c)ᶜ)
    (hIrr : ∀ z, p ⊓ D z ≤ (colorValue K z z)ᶜ)
    (S : BooleanAvoidanceSchedule B) :
    ∃ Y : OmegaOneIndex → ℕ → B,
      (∀ i, p ≤ D (Y i)) ∧
      (∀ i j, i ≠ j → Disjoint p (realEqValue (Y i) (Y j))) ∧
      ∀ j, AvoidsOn D K p S j (fun i => Y i.1) (Y j) := by
  classical
  let Good := {x : ℕ → B // p ≤ D x}
  have hLocal (j : OmegaOneIndex) (old : ∀ i : OmegaOneIndex, i < j → Good) :
      ∃ x : ℕ → B, AvoidsOn D K p S j (fun i => (old i.1 i.2).1) x :=
    exists_AvoidsOn_r145 D hD K p hNo hIrr S j (fun i => (old i.1 i.2).1)
      (fun i => (old i.1 i.2).2)
  let next (j : OmegaOneIndex) (old : ∀ i : OmegaOneIndex, i < j → Good) : Good :=
    ⟨Classical.choose (hLocal j old),(Classical.choose_spec (hLocal j old)).1⟩
  let seq : OmegaOneIndex → Good := WellFounded.fix wellFounded_lt next
  let Y (i : OmegaOneIndex) := (seq i).1
  have hs (j : OmegaOneIndex) : seq j = next j (fun i _ => seq i) :=
    WellFounded.fix_eq wellFounded_lt next j
  have hA (j : OmegaOneIndex) : AvoidsOn D K p S j (fun i => Y i.1) (Y j) := by
    change AvoidsOn D K p S j (fun i => (seq i.1).1) (seq j).1
    rw [hs j]
    exact Classical.choose_spec (hLocal j (fun i _ => seq i))
  refine ⟨Y,fun i => (seq i).2,?_ ,hA⟩
  intro i j hne
  apply le_compl_iff_disjoint_right.mp
  rcases lt_or_gt_of_ne hne with h | h
  · rw [realEqValue_symm_r127 (Y i) (Y j)]
    exact (hA j).2.1 ⟨i,h⟩
  · exact (hA i).2.1 ⟨j,h⟩

end CantorCodes
end JSP000933
