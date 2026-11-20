import JSP000933ActualHarmonicLateEquality

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem exists_finitePalette_prefix_r342 (a : ℕ → ℕ → B) (L n : ℕ) (p : B) (hp : p≠⊥) :
    ∃ (S : ℕ → Set ℕ) (q : B), q≠⊥ ∧ q≤p ∧
      ∀ j<L, ∀ m<n, q⊓a j m=q⊓crispTruth B (m∈S j) := by
  let W := {w : Word // w.length=n}
  have hC (j : Fin L) : p≤⨆ w : W, cylinderValue (a j.val) w.val := by
    apply le_of_dense_named_refinements_r219
    intro r hr hrp
    obtain ⟨w,hw,s,hs,hsr,hS⟩ := exists_decided_initialWord_r136 (a j.val) n r hr
    exact ⟨s,hs,hsr,le_iSup_of_le (⟨w,hw⟩ : W) hS⟩
  obtain ⟨w,q,hq,hqp,hQ⟩ := exists_nonzero_finiteChoices_fin_r135 L
    (fun j (w : W) => cylinderValue (a j.val) w.val) p hp (le_iInf hC)
  let S (j : ℕ) := if hj : j<L then subsetFromWord (w ⟨j,hj⟩).val else ∅
  refine ⟨S,q,hq,hqp,?_⟩
  intro j hj m hm
  let v := w ⟨j,hj⟩
  have hM : m<v.val.length := v.property.symm ▸ hm
  have he := cylinder_fixes_paddedBits_r258 (hQ ⟨j,hj⟩) m hM
  refine he.trans (congrArg (fun b : B => q⊓b) ?_)
  simp only [paddedWordBits,S,dite_eq_left hj,subsetFromWord,Set.mem_ofPred_eq]
  change truthBit (wordBit v.val m)=crispTruth B (wordBit v.val m=true)
  cases wordBit v.val m <;> simp [truthBit,crispTruth]

def groundTruncatedHybrid (S : ℕ → Set ℕ) (g : ℕ → ℕ) (J : ℕ) : Set ℕ :=
  {m | m∈S (max J (hybridBand (actualGroundHybridCut g) (actualGroundHybridCut_strict_r336 g) m))}

theorem exists_truncatedHybrid_groundPrefix_r342 {p q : B}
    (f : ℕ → (ℕ → B) → ℕ → B) (R : (ℕ → B) → ℕ → B)
    (hF : ∀ j x, p≤eventuallySmallError true (dyadicApproxDen j) (f j x) (R x))
    (x : ℕ → B) (J n : ℕ) (hq : q≠⊥) (hqp : q≤p) :
    ∃ (g : ℕ → ℕ) (S : ℕ → Set ℕ) (s : B), s≠⊥ ∧ s≤q ∧
      (∀ j ≤ max J n, ∀ m<n, s⊓f j x m=s⊓crispTruth B (m∈S j)) ∧
      (∀ m<n, s⊓actualTruncatedHybrid f x J m=s⊓crispTruth B (m∈groundTruncatedHybrid S g J)) ∧
      ∀ j, actualGroundHybridCut g (j+1)≤n →
        GroundBudgetHolds true (xorSet (S j) (S (j+1))) ∅ (dyadicGapDen j) n := by
  obtain ⟨g,r,hr,hrq,hChoice,_⟩ := exists_actualHybrid_snapshot_r337 f R hF x n hq hqp
  obtain ⟨S,s,hs,hsr,hPal⟩ := exists_finitePalette_prefix_r342 (fun j => f j x) (max J n+1) n r hr
  have hC (j : ℕ) (hj : j<n) : s≤firstNatWeight (actualDyadicGapTail f x j) (g j) :=
    hsr.trans (hChoice j hj)
  refine ⟨g,S,s,hs,hsr.trans hrq,fun j hj => hPal j (Nat.lt_succ_of_le hj),?_,?_⟩
  · intro m hm
    let c := actualGroundHybridCut g
    let b := hybridBand c (actualGroundHybridCut_strict_r336 g) m
    have hB : b≤ m := (actualGroundHybridCut_le_self_of_index_r336 g b).trans
      (hybridBand_spec c (actualGroundHybridCut_strict_r336 g) (actualGroundHybridCut_zero_r336 g) m).1
    have hJ : max J b ≤ max J n := max_le_max le_rfl (hB.trans hm.le)
    change s⊓namedBandOutput (actualDyadicGapTail f x) (fun j => f (max J j) x) m=
      s⊓crispTruth B (m∈S (max J b))
    rw [namedBandOutput_mask_snapshot_r338 _ (fun j => actualDyadicGapTail_mono_r335 f x j)
      _ g n hC m hm]
    exact hPal (max J b) (Nat.lt_succ_of_le hJ) m hm
  · intro j hj
    have hJ : j+1≤n := (actualGroundHybridCut_le_self_of_index_r336 g (j+1)).trans hj
    have hM : g j≤n := (show g j≤actualGroundHybridCut g (j+1) from le_max_right _ _).trans hj
    have hG := (hC j (Nat.lt_of_succ_le hJ)).trans inf_le_left
    have hE : s≤nameErrorBudget true (dyadicGapDen j) n (f j x) (f (j+1) x) :=
      hG.trans (budgetTail_apply_r229 _ _ _ n hM)
    exact nameErrorBudget_crispPrefix_sound_r340 true (dyadicGapDen j) n hs
      (hPal j (Nat.lt_succ_of_le ((Nat.le_succ j).trans (hJ.trans (le_max_right J n)))))
      (hPal (j+1) (Nat.lt_succ_of_le (hJ.trans (le_max_right J n)))) hE

end SetLanguage
end JSP000933
