import JSP000933RelativeCodeSchedules
import JSP000933InternalAvoidanceStage

namespace JSP000933
namespace RelativeOCA

open OpenGraphForcing CantorCodes

variable {B : Type} [CompleteBooleanAlgebra B]

abbrev RelativeClusterIndex (j : OmegaOneIndex) :=
  Σ n : ℕ,EarlierIndex j×(Fin n→EarlierIndex j)

noncomputable def relativeClosedObstacle (D : (ℕ→B)→B)
    (S : RelativeAvoidanceSchedule B) (e : OmegaOneIndex) (x : ℕ→B) : B :=
  D x⊓(openValue (S.closedCode e) x)ᶜ

noncomputable def relativeClusterObstacle (D : (ℕ→B)→B) (K : Word×Word→B)
    (S : RelativeAvoidanceSchedule B) {j : OmegaOneIndex}
    (old : EarlierIndex j→ℕ→B) (q : RelativeClusterIndex j) (x : ℕ→B) : B :=
  D x⊓weightedCluster K (S.sampleCode q.1 q.2.1.val) (fun i => old (q.2.2 i)) x

def RelativeAvoidsOn (D : (ℕ→B)→B) (K : Word×Word→B) (m : B)
    (S : RelativeAvoidanceSchedule B) (j : OmegaOneIndex)
    (old : EarlierIndex j→ℕ→B) (x : ℕ→B) : Prop :=
  (m≤D x) ∧ (∀ i,m≤(realEqValue x (old i))ᶜ) ∧
    (∀ i : EarlierIndex j,m≤(qualifiedObstacle K (relativeClosedObstacle D S i.val) x)ᶜ) ∧
    (∀ q : RelativeClusterIndex j,m≤(qualifiedObstacle K (relativeClusterObstacle D K S old q) x)ᶜ)

theorem exists_relativeAvoidsStep_r442 (D : (ℕ→B)→B) (hD : RealTestExt D)
    (K : Word×Word→B) (m : B)
    (hNo : ∀ c : CoverCode B,m≤(goodCoverValue id D K c)ᶜ)
    (hIrr : ∀ z,m⊓D z≤(colorValue K z z)ᶜ)
    (S : RelativeAvoidanceSchedule B) (j : OmegaOneIndex)
    (old : EarlierIndex j→ℕ→B) (hOld : ∀ i,m≤D (old i)) :
    ∃ x : ℕ→B,RelativeAvoidsOn D K m S j old x := by
  let E := EarlierIndex j
  let C := RelativeClusterIndex j
  letI : Countable E := OmegaOneIndex_initial_countable_r61 j
  let f : (E⊕E)⊕C→(ℕ→B)→B :=
    Sum.elim (Sum.elim (fun i x => realEqValue x (old i))
      (fun e => qualifiedObstacle K (relativeClosedObstacle D S e.val)))
      (fun q => qualifiedObstacle K (relativeClusterObstacle D K S old q))
  have hf (i : (E⊕E)⊕C) (x y : ℕ→B) :
      Disjoint (m⊓(f i x⊓f i y)) (colorValue K x y) := by
    rcases i with (i | e) | q
    · exact equalitySingleton_independent_r141 K m (old i)
        ((le_inf le_rfl (hOld i)).trans (hIrr (old i))) x y
    · exact qualifiedObstacle_independent_r141 K (relativeClosedObstacle D S e.val) m x y
    · exact qualifiedObstacle_independent_r141 K (relativeClusterObstacle D K S old q) m x y
  obtain ⟨x,hx,hA⟩ := exists_real_avoids_independentFamily_r140 D hD K m hNo f hf
  exact ⟨x,hx,fun i => hA (.inl (.inl i)),fun e => hA (.inl (.inr e)),fun q => hA (.inr q)⟩

theorem exists_relativeAvoidanceSequence_r442 (D : (ℕ→B)→B) (hD : RealTestExt D)
    (K : Word×Word→B) (m : B)
    (hNo : ∀ c : CoverCode B,m≤(goodCoverValue id D K c)ᶜ)
    (hIrr : ∀ z,m⊓D z≤(colorValue K z z)ᶜ)
    (S : RelativeAvoidanceSchedule B) :
    ∃ Y : OmegaOneIndex→ℕ→B,(∀ i,m≤D (Y i)) ∧
      (∀ i j,i≠j → Disjoint m (realEqValue (Y i) (Y j))) ∧
      ∀ j,RelativeAvoidsOn D K m S j (fun i => Y i.val) (Y j) := by
  classical
  let Good := {x : ℕ→B // m≤D x}
  have hLocal (j : OmegaOneIndex) (old : ∀ i : OmegaOneIndex,i<j→Good) :
      ∃ x : ℕ→B,RelativeAvoidsOn D K m S j (fun i => (old i.val i.property).val) x :=
    exists_relativeAvoidsStep_r442 D hD K m hNo hIrr S j (fun i => (old i.val i.property).val)
      (fun i => (old i.val i.property).property)
  let next (j : OmegaOneIndex) (old : ∀ i : OmegaOneIndex,i<j→Good) : Good :=
    ⟨Classical.choose (hLocal j old),(Classical.choose_spec (hLocal j old)).1⟩
  let seq : OmegaOneIndex→Good := WellFounded.fix wellFounded_lt next
  let Y (i : OmegaOneIndex) := (seq i).val
  have hs (j : OmegaOneIndex) : seq j=next j (fun i _ => seq i) :=
    WellFounded.fix_eq wellFounded_lt next j
  have hA (j : OmegaOneIndex) : RelativeAvoidsOn D K m S j (fun i => Y i.val) (Y j) := by
    change RelativeAvoidsOn D K m S j (fun i => (seq i.val).val) (seq j).val
    rw [hs j]
    exact Classical.choose_spec (hLocal j (fun i _ => seq i))
  refine ⟨Y,fun i => (seq i).property,?_,hA⟩
  intro i j hij
  apply le_compl_iff_disjoint_right.mp
  rcases lt_or_gt_of_ne hij with h | h
  · rw [realEqValue_symm_r127 (Y i) (Y j)]
    exact (hA j).2.1 ⟨i,h⟩
  · exact (hA i).2.1 ⟨j,h⟩

end RelativeOCA
end JSP000933
