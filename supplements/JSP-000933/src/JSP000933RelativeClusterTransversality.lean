import JSP000933RelativeHighCluster
import JSP000933RelativeAvoidanceSequence
import JSP000933BooleanClusterTransversality

namespace JSP000933
namespace RelativeOCA

open CantorCodes OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

theorem relativeCluster_diagonalPair_r459 (hB : BoundsCountableOmegaOneNames B)
    (D : (ℕ→B)→B) (K : Word×Word→B) (m : B)
    (hIrr : ∀ x,m⊓D x≤(colorValue K x x)ᶜ)
    (hSym : ∀ x y,(m⊓(D x⊓D y))⊓colorValue K x y≤colorValue K y x)
    (Y : OmegaOneIndex→ℕ→B) (hY : ∀ i,m≤D (Y i))
    (e : OmegaOneIndex→ℕ→B) (hE : EnumeratesBooleanReals e)
    (hAvoid : ∀ j,RelativeAvoidsOn D K m (relativeScheduleFromEnum e) j (fun i => Y i.val) (Y j))
    {n : ℕ} (lower : CardRelativeCCC m (fun i => D (Y i)) (fun i j => colorValue K (Y i) (Y j)) n)
    (a : LabelCandidate→Fin (n+1)→OmegaOneIndex)
    (W : OmegaOneIndex→Finset OmegaOneIndex→B)
    (hW : unboundedValue (rowLabelWeight W)≠⊥)
    (hOwn : ∀ i s,W i s≤cliqueAdmitted m (fun i => D (Y i))
      (fun i j => colorValue K (Y i) (Y j)) s)
    (hMono : ∀ i s,W i s≠⊥ → StrictMono (a (i,s)))
    (hMem : ∀ i s,W i s≠⊥ → ∀ j,a (i,s) j∈s)
    (hDis : ∀ i j,i<j→∀ s t,¬Disjoint s t → Disjoint (W i s) (W j t)) :
    ∃ u v : LabelCandidate,u≠v ∧ ∃ q : B,q≠⊥ ∧ q≤W u.1 u.2 ∧ q≤W v.1 v.2 ∧
      ∀ j,q≤colorValue K (Y (a u j)) (Y (a v j)) := by
  classical
  let F := labelSamples Y a W
  let S := relativeScheduleFromEnum e
  obtain ⟨G,cot,j,p,hp,hpW,hCot,hTable,hCluster,hEq⟩ :=
    exists_relativeHighCluster_r458 hB D K m Y e hE lower a W hW hOwn hMono hMem hDis
  let l := a j (Fin.last n)
  let P := (F j).stem
  let z := (F j).tip
  let L := S.sampleCode n cot
  let raw (x : ℕ→B) := D x⊓weightedCluster K L P x
  have hTrans (x : ℕ→B) : p⊓weightedCluster K F P x=p⊓weightedCluster K L P x := by
    rw [hEq P x]
    exact weightedCluster_mask_r450 p G L (tableAgreement_samples_r450 G L p hTable) K P x
  have hWMark (i : LabelCandidate) : W i.1 i.2≤ m := by
    by_cases hi : W i.1 i.2=⊥
    · rw [hi]
      exact bot_le
    · exact (hOwn i.1 i.2).trans
        ((cliqueAdmitted_le_vertex_r121 _ _ _ (hMem i.1 i.2 hi (Fin.last n))).trans inf_le_left)
  have hjW : W j.1 j.2≠⊥ := fun he => hp (le_bot_iff.mp (hpW.trans_eq he))
  let stemAt (i : Fin n) : EarlierIndex l :=
    ⟨a j i.castSucc,hMono j.1 j.2 hjW (Fin.castSucc_lt_last i)⟩
  let q : RelativeClusterIndex l := ⟨n,⟨cot,hCot⟩,stemAt⟩
  have hAvoidRaw : m≤(qualifiedObstacle K raw z)ᶜ := (hAvoid l).2.2.2 q
  have hpM : p≤ m := hpW.trans (hWMark j)
  have hpRaw : p≤raw z :=
    le_inf (hpM.trans (hY l)) (((le_inf le_rfl hCluster).trans_eq (hTrans z)).trans inf_le_right)
  have hpNonInd : p≤(independenceTest K raw)ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have hP : p⊓independenceTest K raw≤ m⊓qualifiedObstacle K raw z :=
      le_inf (inf_le_left.trans hpM) (le_inf inf_le_right (inf_le_left.trans hpRaw))
    exact hP.trans (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp hAvoidRaw))
  have hExists : p≤⨆ x : ℕ→B,⨆ y : ℕ→B,(raw x⊓raw y)⊓colorValue K x y := by
    simpa only [independenceTest,compl_iInf,compl_sup,compl_compl] using hpNonInd
  obtain ⟨x,b,hb,hbp,hbx⟩ := exists_nonzero_below_choice_r135 p hp
    (fun x => ⨆ y : ℕ→B,(raw x⊓raw y)⊓colorValue K x y) hExists
  obtain ⟨y,r,hr,hrb,hry⟩ := exists_nonzero_below_choice_r135 b hb
    (fun y => (raw x⊓raw y)⊓colorValue K x y) hbx
  have hrp := hrb.trans hbp
  have hLift (v : ℕ→B) (h : r≤weightedCluster K L P v) :
      r≤weightedCluster K F P v :=
    (((le_inf hrp h).trans_eq (hTrans v).symm)).trans inf_le_right
  have hRev (i : LabelCandidate) (k : Fin n) :
      (F i).weight⊓colorValue K (P k) ((F i).stem k)≤colorValue K ((F i).stem k) (P k) := by
    have hM : (F i).weight⊓colorValue K (P k) ((F i).stem k)≤ m :=
      inf_le_left.trans (hWMark i)
    exact (le_inf (le_inf hM (le_inf (hM.trans (hY (a j k.castSucc)))
      (hM.trans (hY (a i k.castSucc))))) inf_le_right).trans (hSym _ _)
  obtain ⟨u,v,s,hs,_,hsU,hsV,hsMat,hsTip⟩ := samples_of_clusterEdge_r150 K F P x y r hr
    (hLift x (hry.trans (inf_le_left.trans (inf_le_left.trans inf_le_right))))
    (hLift y (hry.trans (inf_le_left.trans (inf_le_right.trans inf_le_right))))
    (hry.trans inf_le_right) hRev
  have hUV : u≠v := by
    intro he
    subst v
    have hm : s≤ m := hsU.trans (hWMark u)
    have hn : s≤(colorValue K (F u).tip (F u).tip)ᶜ :=
      (le_inf hm (hm.trans (hY (a u (Fin.last n))))).trans (hIrr _)
    exact hs (disjoint_compl_right.out _ hsTip hn)
  refine ⟨u,v,hUV,s,hs,hsU,hsV,fun i => ?_⟩
  exact Fin.lastCases hsTip (fun k => hsMat.trans (iInf_le _ k)) i

end RelativeOCA
end JSP000933
