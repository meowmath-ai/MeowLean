import JSP000933ActualGroundStageValues

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def ActualStageHistory : ℕ → Type
  | 0 => PUnit
  | n+1 => ActualStageHistory n × ActualGroundStage

def historyNextLeft : {n : ℕ} → ActualStageHistory n → ℕ
  | 0, _ => 0
  | _+1, h => h.2.nextLeft

def historyNextOut : {n : ℕ} → ActualStageHistory n → ℕ
  | 0, _ => 0
  | _+1, h => h.2.out+1

noncomputable def actualHistoryValue (c : ℕ → B) (L : (ℕ → B) → ℕ → B) :
    (n : ℕ) → ActualStageHistory n → B
  | 0, _ => ⊤
  | n+1, h => actualHistoryValue c L n h.1⊓
      actualStageValue c L n (historyNextLeft h.1) (historyNextOut h.1) h.2

def seedActualStageHistory (p : B) : IndexedPartition B (ActualStageHistory 0) p where
  weight _ := p
  covers := le_antisymm (iSup_le (fun _ => le_rfl))
    (le_iSup (fun _ : ActualStageHistory 0 => p) PUnit.unit)
  separate := by
    intro x y h
    have he : x = y := by
      change PUnit at x y
      exact Subsingleton.elim x y
    exact (h he).elim

theorem extend_actualStageHistory_r352 {p : B} (c : ℕ → B) (L : (ℕ → B) → ℕ → B)
    (hC : ∀ k a o, p≤⨆ d : ActualGroundStage, actualStageValue c L k a o d)
    (n : ℕ) (P : IndexedPartition B (ActualStageHistory n) p)
    (hP : ∀ h, P.weight h≤actualHistoryValue c L n h) :
    ∃ Q : IndexedPartition B (ActualStageHistory (n+1)) p,
      (∀ h, Q.weight h≤P.weight h.1) ∧ ∀ h, Q.weight h≤actualHistoryValue c L (n+1) h := by
  classical
  let T (x : ActualStageHistory n) (d : ActualGroundStage) :=
    actualStageValue c L n (historyNextLeft x) (historyNextOut x) d
  have hRow (x : ActualStageHistory n) :
      ∃ R : IndexedPartition B ActualGroundStage (P.weight x), ∀ d, R.weight d≤T x d :=
    exists_indexedPartition_of_join_r215 (P.weight x) (T x)
      ((P.weight_le_r215 x).trans (hC n (historyNextLeft x) (historyNextOut x)))
  choose row hR using hRow
  let w (x : ActualStageHistory (n+1)) := (row x.1).weight x.2
  have hBound (x : ActualStageHistory (n+1)) : w x≤P.weight x.1 :=
    (row x.1).weight_le_r215 x.2
  have hCov : (⨆ x, w x)=p := by
    apply le_antisymm (iSup_le (fun x => (hBound x).trans (P.weight_le_r215 x.1)))
    rw [← P.covers]
    apply iSup_le
    intro old
    rw [← (row old).covers]
    exact iSup_le (fun d => le_iSup w ((old,d) : ActualStageHistory (n+1)))
  have hSep (x y : ActualStageHistory (n+1)) (hxy : x≠y) : Disjoint (w x) (w y) := by
    by_cases h : x.1=y.1
    · have he : x.2≠y.2 := fun he => hxy (Prod.ext h he)
      change Disjoint ((row x.1).weight x.2) ((row y.1).weight y.2)
      have hW : (row y.1).weight y.2=(row x.1).weight y.2 :=
        congrArg (fun z => (row z).weight y.2) h.symm
      rw [hW]
      exact (row x.1).separate x.2 y.2 he
    · exact (P.separate x.1 y.1 h).mono (hBound x) (hBound y)
  exact ⟨⟨w,hCov,hSep⟩,hBound,fun x => le_inf ((hBound x).trans (hP x.1)) (hR x.1 x.2)⟩

structure ActualStageTower (B : Type) [NontrivialCompleteBooleanAlgebra B]
    (p : B) (c : ℕ → B) (L : (ℕ → B) → ℕ → B) where
  level : (n : ℕ) → IndexedPartition B (ActualStageHistory n) p
  refines : ∀ n h, (level (n+1)).weight h≤(level n).weight h.1
  valid : ∀ n h, (level n).weight h≤actualHistoryValue c L n h

theorem exists_actualStageTower_r352 {p : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (L : (ℕ → B) → ℕ → B)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (hLarge : p≤actualLongBlockLarge c) : Nonempty (ActualStageTower B p c L) := by
  classical
  let W (n : ℕ) := {P : IndexedPartition B (ActualStageHistory n) p //
    ∀ h, P.weight h≤actualHistoryValue c L n h}
  let seed : W 0 := ⟨seedActualStageHistory p,fun _ => le_top⟩
  have hstep (n : ℕ) (P : W n) : ∃ Q : W (n+1), ∀ h, Q.val.weight h≤P.val.weight h.1 := by
    obtain ⟨Q,hLink,hQ⟩ := extend_actualStageHistory_r352 c L
      (actualStageValue_covers_r351 F c L hC hL hLarge) n P.val P.property
    exact ⟨⟨Q,hQ⟩,hLink⟩
  let f : (n : ℕ) → W n := Nat.rec (motive := W) seed (fun n P => Classical.choose (hstep n P))
  exact ⟨⟨fun n => (f n).val,fun n => Classical.choose_spec (hstep n (f n)),fun n => (f n).property⟩⟩

end SetLanguage
end JSP000933
