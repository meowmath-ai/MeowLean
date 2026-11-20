import JSP000933WeightedExceptionalBound

namespace JSP000933
namespace CantorCodes

open OpenGraphForcing

variable {B I : Type} [CompleteBooleanAlgebra B]

def sampleFromTuple (Y : OmegaOneIndex → ℕ → B) {n : ℕ}
    (a : Fin (n+1) → OmegaOneIndex) (b : B) : BooleanSample B n :=
  ⟨fun i => Y (a i.castSucc),Y (a (Fin.last n)),b⟩

private theorem weightedCluster_transport_r152 (K : Word × Word → B)
    {n : ℕ} (data : Σ n, ℕ → BooleanSample B n) (F : ℕ → BooleanSample B n)
    (he : data = ⟨n,F⟩) (stem : Fin n → ℕ → B) (tip : ℕ → B) :
    weightedCluster K data.2 (fun i => stem (Fin.cast (congrArg Sigma.fst he) i)) tip =
      weightedCluster K F stem tip := by
  subst data
  rfl

theorem booleanRectangularPair_r152 (hCCC : BooleanCCC B)
    (D : (ℕ → B) → B) (K : Word × Word → B) (mark : B)
    (hIrr : ∀ x, mark ⊓ D x ≤ (colorValue K x x)ᶜ)
    (hSym : ∀ x y, (mark ⊓ (D x ⊓ D y)) ⊓ colorValue K x y ≤ colorValue K y x)
    (S : BooleanAvoidanceSchedule B) (Y : OmegaOneIndex → ℕ → B)
    (hY : ∀ i, mark ≤ D (Y i))
    (hAvoid : ∀ j, AvoidsOn D K mark S j (fun i => Y i.1) (Y j))
    {n : ℕ} (a : I → Fin (n+1) → OmegaOneIndex) (w : I → B)
    (hI : ¬ Countable I) (hw : ∀ i, w i ≠ ⊥ ∧ w i ≤ mark)
    (hMono : ∀ i, StrictMono (a i)) (hLast : Function.Injective (fun i => a i (Fin.last n)))
    (hRect : ∀ i j r t, r ≠ t → w i ⊓ w j ≤ colorValue K (Y (a i r)) (Y (a j t)))
    (hLower : LowerStemPairs K (fun i => sampleFromTuple Y (a i) (w i))) :
    ∃ i j : I, i ≠ j ∧ ∃ q : B, q ≠ ⊥ ∧ q ≤ w i ∧ q ≤ w j ∧
      ∀ r t, q ≤ colorValue K (Y (a i r)) (Y (a j t)) := by
  classical
  let F (i : I) := sampleFromTuple Y (a i) (w i)
  obtain ⟨G,hG,hEq⟩ := exists_weightedClusterSequence_r149 hCCC K F
  obtain ⟨e,he⟩ := S.sample_onto ⟨n,G⟩
  obtain ⟨i,hi,hN⟩ := exists_high_clusterPiece_r151 K F hI (fun i => (hw i).1)
    (fun i => a i (Fin.last n)) hLast e hLower
  let last := a i (Fin.last n)
  let z := (F i).tip
  let P := (F i).stem
  let c := w i ⊓ weightedCluster K G P z
  have hc : c ≠ ⊥ := by
    intro hn
    apply hN
    change w i ⊓ weightedCluster K F P z = ⊥
    rw [hEq P z]
    exact hn
  let e0 : EarlierIndex last := ⟨e,hi⟩
  let stemIdx (r : Fin n) : EarlierIndex last :=
    ⟨a i r.castSucc,hMono i (Fin.castSucc_lt_last r)⟩
  let param : EarlierClusterParam S last :=
    ⟨e0,fun r => stemIdx (Fin.cast (congrArg Sigma.fst he) r)⟩
  let raw (x : ℕ → B) := D x ⊓ weightedCluster K G P x
  have hRawEq :
      avoidClusterRaw D K S (fun j : EarlierIndex last => Y j.1) param = raw := by
    funext x
    change D x ⊓ weightedCluster K (S.sampleCode e).2
      (fun r => P (Fin.cast (congrArg Sigma.fst he) r)) x = _
    rw [weightedCluster_transport_r152 K (S.sampleCode e) G he P x] <;> rfl
  have hAvoidRaw : mark ≤ (qualifiedObstacle K raw z)ᶜ := by
    have h := (hAvoid last).2.2.2 param
    rw [hRawEq] at h
    exact h
  have hcMark : c ≤ mark := inf_le_left.trans (hw i).2
  have hcRaw : c ≤ raw z := le_inf (hcMark.trans (hY last)) inf_le_right
  have hcNonInd : c ≤ (independenceTest K raw)ᶜ := by
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    have hh : c ⊓ independenceTest K raw ≤ mark ⊓ qualifiedObstacle K raw z :=
      le_inf (inf_le_left.trans hcMark) (le_inf inf_le_right (inf_le_left.trans hcRaw))
    exact hh.trans (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp hAvoidRaw))
  have hs : c ≤ ⨆ x : ℕ → B, ⨆ y : ℕ → B, (raw x ⊓ raw y) ⊓ colorValue K x y := by
    simpa only [independenceTest,compl_iInf,compl_sup,compl_compl] using hcNonInd
  obtain ⟨x,b,hb,hbc,hbx⟩ := exists_nonzero_below_choice_r135 c hc
    (fun x => ⨆ y : ℕ → B, (raw x ⊓ raw y) ⊓ colorValue K x y) hs
  obtain ⟨y,d,hd,hdb,hdy⟩ := exists_nonzero_below_choice_r135 b hb
    (fun y => (raw x ⊓ raw y) ⊓ colorValue K x y) hbx
  have hReverse (j : ℕ) (l : Fin n) :
      (G j).weight ⊓ colorValue K (P l) ((G j).stem l) ≤
        colorValue K ((G j).stem l) (P l) := by
    rcases hG j with hz | ⟨k,hk⟩
    · rw [hz,bot_inf_eq]
      exact bot_le
    · rw [hk]
      apply le_trans _ (hSym _ _)
      have ht : w k ⊓ colorValue K (P l) ((F k).stem l) ≤ mark :=
        inf_le_left.trans (hw k).2
      exact le_inf (le_inf ht (le_inf (ht.trans (hY (a i l.castSucc)))
        (ht.trans (hY (a k l.castSucc))))) inf_le_right
  obtain ⟨j,k,q,hq,_,hqj,hqk,hMat,hTip⟩ := samples_of_clusterEdge_r150 K G P x y d hd
    (hdy.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
    (hdy.trans (inf_le_left.trans (inf_le_right.trans inf_le_right)))
    (hdy.trans inf_le_right) hReverse
  have hLift (k : ℕ) (h : q ≤ (G k).weight) : ∃ i, G k = F i := by
    rcases hG k with hz | hSome
    · exact False.elim (hq (le_bot_iff.mp (h.trans_eq hz)))
    · exact hSome
  obtain ⟨u,hu⟩ := hLift j hqj
  obtain ⟨v,hv⟩ := hLift k hqk
  rw [hu] at hqj
  rw [hv] at hqk
  rw [hu,hv] at hMat hTip
  have hUV : u ≠ v := by
    intro he
    subst v
    have hMark : q ≤ mark := hqj.trans (hw u).2
    have hn : q ≤ (colorValue K (F u).tip (F u).tip)ᶜ :=
      (le_inf hMark (hMark.trans (hY (a u (Fin.last n))))).trans (hIrr (F u).tip)
    exact hq (le_bot_iff.mp ((le_inf hTip hn).trans_eq (inf_compl_eq_bot')))
  refine ⟨u,v,hUV,q,hq,hqj,hqk,fun r t => ?_⟩
  by_cases h : r = t
  · subst t
    refine Fin.lastCases hTip (fun l => hMat.trans (iInf_le _ l)) r
  · exact (le_inf hqj hqk).trans (hRect u v r t h)

end CantorCodes
end JSP000933
