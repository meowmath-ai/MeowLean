import JSP000933ActualHybridSnapshots

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def namedBandOutput (G : ℕ → ℕ → B) (a : ℕ → ℕ → B) (m : ℕ) : B :=
  ⨆ j, namedCutBandWeight G j m⊓a j m

theorem namedBandOutput_mask_snapshot_r338 (G : ℕ → ℕ → B) (hG : ∀ j, Monotone (G j))
    (a : ℕ → ℕ → B) (g : ℕ → ℕ) (N : ℕ) {p : B}
    (hChoice : ∀ j<N, p≤firstNatWeight (G j) (g j)) (m : ℕ) (hm : m<N) :
    p⊓namedBandOutput G a m=p⊓
      a (hybridBand (actualGroundHybridCut g) (actualGroundHybridCut_strict_r336 g) m) m := by
  let c := actualGroundHybridCut g
  let b := hybridBand c (actualGroundHybridCut_strict_r336 g) m
  have hb : b≤ m := (actualGroundHybridCut_le_self_of_index_r336 g b).trans
    (hybridBand_spec c (actualGroundHybridCut_strict_r336 g) (actualGroundHybridCut_zero_r336 g) m).1
  have hB (j : ℕ) (hj : j≤ m) :
      p⊓namedCutBandWeight G j m=p⊓crispTruth B (b=j) :=
    namedCutBandWeight_mask_r337 G hG g N hChoice j m (Nat.succ_le_of_lt (hj.trans_lt hm))
  change p⊓(⨆ j : ℕ, namedCutBandWeight G j m⊓a j m)=p⊓a b m
  apply le_antisymm
  · rw [inf_iSup_eq]
    apply iSup_le
    intro j
    by_cases hj : j≤ m
    · have he := mask_inf_congr_r126 (hB j hj) (show p⊓a j m=p⊓a j m from rfl)
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

noncomputable def actualTruncatedHybrid (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B) (J : ℕ) : ℕ → B :=
  namedBandOutput (actualDyadicGapTail f x) (fun j => f (max J j) x)

theorem actualRecursiveCutLE_antitone_r338 (G : ℕ → ℕ → B) (hG : ∀ j, Monotone (G j)) (m : ℕ) :
    Antitone (fun j => actualRecursiveCutLE G j m) := by
  intro i j h
  induction j with
  | zero =>
    have he : i=0 := Nat.eq_zero_of_le_zero h
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i=j+1
    · subst i
      exact le_rfl
    · have hIJ : i≤j := by omega
      exact (actualRecursiveCutLE_step_r335 G hG j m).trans (ih hIJ)

theorem actualHybrid_agrees_trunc_late_r338 (f : ℕ → (ℕ → B) → ℕ → B) (x : ℕ → B) (J M : ℕ)
    {p : B} (hC : p≤actualRecursiveCutLE (actualDyadicGapTail f x) J M) :
    ∀ m≥M, p⊓actualHybridBit f x m=p⊓actualTruncatedHybrid f x J m := by
  intro m hm
  let G := actualDyadicGapTail f x
  have hG : ∀ j, Monotone (G j) := fun j => actualDyadicGapTail_mono_r335 f x j
  have hM : p≤actualRecursiveCutLE G J m :=
    hC.trans (actualRecursiveCutLE_mono_r335 G hG J hm)
  change p⊓(⨆ j : ℕ, namedCutBandWeight G j m⊓f j x m)=
    p⊓(⨆ j : ℕ, namedCutBandWeight G j m⊓f (max J j) x m)
  simp only [inf_iSup_eq]
  apply congrArg iSup
  funext j
  by_cases hj : J≤j
  · rw [max_eq_right hj]
  · have hJ : j+1≤J := Nat.lt_of_not_ge hj
    have hU : p≤actualRecursiveCutLE G (j+1) m :=
      hM.trans (actualRecursiveCutLE_antitone_r338 G hG m hJ)
    have h0 : p⊓namedCutBandWeight G j m=⊥ :=
      le_bot_iff.mp ((le_inf (inf_le_left.trans hU) (inf_le_right.trans inf_le_right)).trans_eq inf_compl_eq_bot')
    simp only [← inf_assoc,h0,bot_inf_eq]

theorem actualRecursiveCutLE_eventually_r338 {p : B} (f : ℕ → (ℕ → B) → ℕ → B) (R : (ℕ → B) → ℕ → B)
    (hF : ∀ j x, p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x))
    (x : ℕ → B) (J : ℕ) : p≤⨆ M, actualRecursiveCutLE (actualDyadicGapTail f x) J M := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨g,r,hr,hrq,hChoice,_⟩ := exists_actualHybrid_snapshot_r337 f R hF x J hq hqp
  let M := actualGroundHybridCut g J
  have he := actualRecursiveCutLE_mask_ground_r336 _ (fun j => actualDyadicGapTail_mono_r335 f x j)
    g J hChoice J le_rfl M
  have hIn : r≤actualRecursiveCutLE (actualDyadicGapTail f x) J M :=
    ((show r=r⊓actualRecursiveCutLE (actualDyadicGapTail f x) J M by
        simpa [M,crispTruth] using he.symm).le).trans inf_le_right
  exact ⟨r,hr,hrq,le_iSup_of_le M hIn⟩

end SetLanguage
end JSP000933
