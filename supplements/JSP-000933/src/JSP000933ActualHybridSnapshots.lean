import JSP000933ActualGroundCutMasks

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def namedCutBandWeight (G : ℕ → ℕ → B) (j m : ℕ) : B :=
  actualRecursiveCutLE G j m⊓(actualRecursiveCutLE G (j+1) m)ᶜ

theorem namedCutBandWeight_mask_r337 (G : ℕ → ℕ → B) (hG : ∀ j, Monotone (G j))
    (g : ℕ → ℕ) (N : ℕ) {p : B} (hChoice : ∀ j<N, p≤firstNatWeight (G j) (g j))
    (j m : ℕ) (hJ : j+1≤N) :
    p⊓namedCutBandWeight G j m=p⊓crispTruth B
      (hybridBand (actualGroundHybridCut g) (actualGroundHybridCut_strict_r336 g) m=j) := by
  let c := actualGroundHybridCut g
  have hF := actualRecursiveCutLE_mask_ground_r336 G hG g N hChoice
  have hm := mask_inf_congr_r126 (hF j ((Nat.le_succ j).trans hJ) m)
    (mask_compl_congr_r126 (hF (j+1) hJ m))
  have he : (c j≤ m ∧ ¬c (j+1)≤ m) ↔ hybridBand c (actualGroundHybridCut_strict_r336 g) m=j := by
    rw [hybridBand_eq_iff c (actualGroundHybridCut_strict_r336 g) (actualGroundHybridCut_zero_r336 g)]
    exact and_congr_right (fun _ => not_le)
  refine hm.trans (congrArg (fun b : B => p⊓b) ?_)
  rw [← crisp_not_r197,← crisp_and_r190]
  exact crispTruth_propext_r188 he

theorem actualHybridBit_mask_snapshot_r337 (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B)
    (g : ℕ → ℕ) (N : ℕ) {p : B}
    (hChoice : ∀ j<N, p≤firstNatWeight (actualDyadicGapTail f x j) (g j)) (m : ℕ) (hm : m<N) :
    p⊓actualHybridBit f x m=p⊓
      f (hybridBand (actualGroundHybridCut g) (actualGroundHybridCut_strict_r336 g) m) x m := by
  let c := actualGroundHybridCut g
  let b := hybridBand c (actualGroundHybridCut_strict_r336 g) m
  let G := actualDyadicGapTail f x
  have hb : b≤ m := (actualGroundHybridCut_le_self_of_index_r336 g b).trans
    (hybridBand_spec c (actualGroundHybridCut_strict_r336 g) (actualGroundHybridCut_zero_r336 g) m).1
  have hB (j : ℕ) (hj : j≤ m) :
      p⊓namedCutBandWeight G j m=p⊓crispTruth B (b=j) :=
    namedCutBandWeight_mask_r337 G (fun j => actualDyadicGapTail_mono_r335 f x j)
      g N hChoice j m (Nat.succ_le_of_lt (hj.trans_lt hm))
  change p⊓(⨆ j : ℕ, namedCutBandWeight G j m⊓f j x m)=p⊓f b x m
  apply le_antisymm
  · rw [inf_iSup_eq]
    apply iSup_le
    intro j
    by_cases hj : j≤ m
    · have he := mask_inf_congr_r126 (hB j hj) (show p⊓f j x m=p⊓f j x m from rfl)
      by_cases hBJ : b=j
      · subst j
        exact he.le.trans (by simp [crispTruth])
      · exact he.le.trans (by simp [crispTruth,hBJ])
    · have h0 : namedCutBandWeight G j m=⊥ := by
        unfold namedCutBandWeight
        rw [actualRecursiveCutLE_bot_r335 G j m (Nat.lt_of_not_ge hj),bot_inf_eq]
      rw [h0,bot_inf_eq,inf_bot_eq]
      exact bot_le
  · apply le_inf inf_le_left
    apply le_iSup_of_le b
    have hW : p≤namedCutBandWeight G b m :=
      ((show p=p⊓namedCutBandWeight G b m by
          simpa [crispTruth] using (hB b hb).symm).le).trans inf_le_right
    exact le_inf (inf_le_left.trans hW) inf_le_right

theorem exists_actualHybrid_snapshot_r337 {p q : B}
    (f : ℕ → (ℕ → B) → ℕ → B) (R : (ℕ → B) → ℕ → B)
    (hF : ∀ j x, p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x))
    (x : ℕ → B) (N : ℕ) (hq : q≠⊥) (hqp : q≤p) :
    ∃ (g : ℕ → ℕ) (r : B), r≠⊥ ∧ r≤q ∧
      (∀ j<N, r≤firstNatWeight (actualDyadicGapTail f x j) (g j)) ∧
      ∀ m<N, r⊓actualHybridBit f x m=r⊓
        f (hybridBand (actualGroundHybridCut g) (actualGroundHybridCut_strict_r336 g) m) x m := by
  have hN : q≤⨅ j : Fin N, ⨆ n : ℕ, firstNatWeight (actualDyadicGapTail f x j.val) n :=
    le_iInf (fun j => (hqp.trans (actualDyadicGapTail_exists_r335 f R hF x j.val)).trans_eq
      (firstNatWeight_covers_r317 (actualDyadicGapTail f x j.val)).symm)
  obtain ⟨w,r,hr,hrq,hR⟩ := exists_nonzero_finiteChoices_fin_r135 N
    (fun j : Fin N => firstNatWeight (actualDyadicGapTail f x j.val)) q hq hN
  let g (j : ℕ) := if hj : j<N then w ⟨j,hj⟩ else 0
  have hChoice (j : ℕ) (hj : j<N) : r≤firstNatWeight (actualDyadicGapTail f x j) (g j) := by
    simpa only [g,dite_eq_left hj] using hR ⟨j,hj⟩
  exact ⟨g,r,hr,hrq,hChoice,fun m hm => actualHybridBit_mask_snapshot_r337 f x g N hChoice m hm⟩

end SetLanguage
end JSP000933
