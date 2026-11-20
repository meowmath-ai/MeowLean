import JSP000933RelativeFailureBoxes
import JSP000933BooleanRectangleCompatibility

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

def labelSamples (Y : OmegaOneIndex→ℕ→B) {n : ℕ}
    (a : LabelCandidate→Fin (n+1)→OmegaOneIndex)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B) (x : LabelCandidate) : BooleanSample B n :=
  sampleFromTuple Y (a x) (W x.1 x.2)

theorem prefixOfLabel_subset_r457 {n : ℕ} (a : Fin (n+1)→OmegaOneIndex)
    (s : Finset OmegaOneIndex) (h : ∀ i,a i∈s) :
    prefixFinset_r64 a⊆s := by
  intro x hx
  obtain ⟨i,rfl⟩ := mem_prefixFinset_r64.mp hx
  exact h i.castSucc

theorem relativeExceptional_bounded_r457 (hB : BoundsCountableOmegaOneNames B)
    (D : (ℕ→B)→B) (K : Word×Word→B) (m : B)
    (Y : OmegaOneIndex→ℕ→B) {n : ℕ}
    (lower : CardRelativeCCC m (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) n)
    (a : LabelCandidate→Fin (n+1)→OmegaOneIndex)
    (W T : OmegaOneIndex→Finset OmegaOneIndex→B)
    (hT : ∀ i s,T i s≤W i s)
    (hOwn : ∀ i s,W i s≤cliqueAdmitted m (fun i => D (Y i))
      (fun i j => colorValue K (Y i) (Y j)) s)
    (hMono : ∀ i s,W i s≠⊥ → StrictMono (a (i,s)))
    (hMem : ∀ i s,W i s≠⊥ → ∀ j,a (i,s) j∈s)
    (hDis : ∀ i j,i<j→∀ s t,¬Disjoint s t → Disjoint (W i s) (W j t))
    (hFail : ∀ i s,T i s⊓weightedCluster K (labelSamples Y a W)
      ((labelSamples Y a W (i,s)).stem) ((labelSamples Y a W (i,s)).tip)=⊥) :
    unboundedValue (rowLabelWeight T)=⊥ := by
  classical
  let F := labelSamples Y a W
  let A := cliqueAdmitted m (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j))
  let f (x : LabelCandidate) := prefixFinset_r64 (a x)
  rw [failureBoxWeight_unbounded_r456 hB K F T hFail]
  apply le_bot_iff.mp
  apply iSup_le
  intro c
  let U := failureBoxWeight K F T c
  have hU (i : OmegaOneIndex) (s : Finset OmegaOneIndex) : U i s≤W i s :=
    inf_le_left.trans (inf_le_left.trans (hT i s))
  have hSub (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (h : W i s≠⊥) : f (i,s)⊆s :=
    prefixOfLabel_subset_r457 (a (i,s)) s (hMem i s h)
  have hVA (i : OmegaOneIndex) (s : Finset OmegaOneIndex) :
      projectedLabelWeight U f i s≤A s := by
    apply iSup_le
    intro t
    have hA : U i t.val ≤ A (f (i,t.val)) := by
      by_cases ht : W i t.val=⊥
      · exact ((hU i t.val).trans_eq ht).trans bot_le
      · exact (hU i t.val).trans ((hOwn i t.val).trans
          (cliqueAdmitted_anti_r121 _ _ _ (hSub i t.val ht)))
    exact hA.trans_eq (congrArg A t.property)
  have hSize (i : OmegaOneIndex) (s : Finset OmegaOneIndex) (hs : s.card≠n) :
      projectedLabelWeight U f i s=⊥ := by
    apply le_bot_iff.mp
    apply iSup_le
    intro t
    by_cases ht : W i t.val=⊥
    · exact (hU i t.val).trans_eq ht
    · exact False.elim (hs ((congrArg Finset.card t.property).symm.trans
        (card_prefixFinset_r64 (hMono i t.val ht))))
  have hPairs (i j : OmegaOneIndex) (hij : i<j) (s t : Finset OmegaOneIndex) :
      (U i s⊓U j t)⊓A (f (i,s)∪f (j,t))=⊥ := by
    let p := (U i s⊓U j t)⊓A (f (i,s)∪f (j,t))
    change p=⊥
    by_contra hp
    have hu : p≤U i s := inf_le_left.trans inf_le_left
    have hv : p≤U j t := inf_le_left.trans inf_le_right
    have hw : p≤W i s := hu.trans (hU i s)
    have hz : p≤W j t := hv.trans (hU j t)
    have hs : W i s≠⊥ := fun h => hp (le_bot_iff.mp (hw.trans_eq h))
    have ht : W j t≠⊥ := fun h => hp (le_bot_iff.mp (hz.trans_eq h))
    have hd : Disjoint s t := by
      by_contra hn
      exact hp ((hDis i j hij s t hn).out _ hw hz)
    have hm : p ≤ matchedValue K (F (i,s)).stem (F (j,t)).stem := by
      apply le_iInf
      intro k
      let z := a (i,s) k.castSucc
      let w := a (j,t) k.castSucc
      have hP : z∈f (i,s) := mem_prefixFinset_r64.mpr ⟨k,rfl⟩
      have hQ : w∈f (j,t) := mem_prefixFinset_r64.mpr ⟨k,rfl⟩
      have hn : z≠w := by
        intro he
        change a (i,s) k.castSucc = a (j,t) k.castSucc at he
        exact (Finset.disjoint_left.mp hd (hMem i s hs k.castSucc))
          (he.symm ▸ hMem j t ht k.castSucc)
      exact inf_le_right.trans (cliqueAdmitted_le_edge_r121 _ _ _
        (Finset.mem_union.mpr (Or.inl hP)) (Finset.mem_union.mpr (Or.inr hQ)) hn)
    have hIn : p≤weightedClusterHit K F (F (i,s)).stem c.1 c.2 :=
      le_iSup_of_le (j,t) (le_inf (le_inf hz hm) (hv.trans (inf_le_left.trans inf_le_right)))
    have hOut : p≤(weightedClusterHit K F (F (i,s)).stem c.1 c.2)ᶜ := hu.trans inf_le_right
    exact hp (disjoint_compl_right.out _ hIn hOut)
  have hDone := lower (projectedLabelWeight U f) hVA hSize
    (fun i j hij s t => projectedLabelWeight_pairs_zero_r455 U f A hPairs i j hij s t)
  rw [projectedLabelWeight_rows_r455] at hDone
  exact hDone.le

end RelativeOCA
end JSP000933
