import JSP000933ActualDyadicGapCuts
import JSP000933Hybrid

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem firstNatWeight_decides_monotone_r336 {p : B} (V : ℕ → B) (hV : Monotone V) (n m : ℕ)
    (h : p≤firstNatWeight V n) : p⊓V m=p⊓crispTruth B (n≤ m) := by
  by_cases hm : n≤ m
  · have hp : p≤V m := h.trans (inf_le_left.trans (hV hm))
    rw [crispTruth,ite_eq_left hm,inf_top_eq,inf_eq_left.mpr hp]
  · have hp : p≤(V m)ᶜ := h.trans (inf_le_right.trans (iInf_le _ (⟨m,Nat.lt_of_not_ge hm⟩ : Fin n)))
    have h0 : p⊓V m=⊥ := le_bot_iff.mp
      ((le_inf inf_le_right (inf_le_left.trans hp)).trans_eq inf_compl_eq_bot')
    rw [crispTruth,ite_eq_right hm,inf_bot_eq,h0]

def actualGroundHybridCut (g : ℕ → ℕ) : ℕ → ℕ :=
  Nat.rec 0 (fun j r => max (r+1) (g j))

theorem actualGroundHybridCut_zero_r336 (g : ℕ → ℕ) : actualGroundHybridCut g 0=0 := rfl

theorem actualGroundHybridCut_succ_r336 (g : ℕ → ℕ) (j : ℕ) :
    actualGroundHybridCut g (j+1)=max (actualGroundHybridCut g j+1) (g j) := rfl

theorem actualGroundHybridCut_strict_r336 (g : ℕ → ℕ) : StrictMono (actualGroundHybridCut g) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [actualGroundHybridCut_succ_r336]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem actualGroundHybridCut_le_self_of_index_r336 (g : ℕ → ℕ) (j : ℕ) : j≤actualGroundHybridCut g j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [actualGroundHybridCut_succ_r336]
    exact (Nat.succ_le_succ ih).trans (le_max_left _ _)

theorem actualRecursiveCutLE_mask_ground_r336 (G : ℕ → ℕ → B) (hG : ∀ j, Monotone (G j))
    (g : ℕ → ℕ) (N : ℕ) {p : B} (hChoice : ∀ j<N, p≤firstNatWeight (G j) (g j)) :
    ∀ j≤N, ∀ m, p⊓actualRecursiveCutLE G j m=p⊓crispTruth B (actualGroundHybridCut g j≤ m) := by
  intro j
  induction j with
  | zero =>
    intro _ m
    simp [actualRecursiveCutLE,actualGroundHybridCut_zero_r336,crispTruth]
  | succ j ih =>
    intro hJ m
    have hj : j<N := Nat.lt_of_succ_le hJ
    cases m with
    | zero =>
      have hn : ¬actualGroundHybridCut g (j+1)≤0 :=
        Nat.not_le_of_gt ((Nat.zero_lt_succ (actualGroundHybridCut g j)).trans_le
          (show actualGroundHybridCut g j+1≤actualGroundHybridCut g (j+1) from le_max_left _ _))
      simp [actualRecursiveCutLE,crispTruth,hn]
    | succ m =>
      change p⊓(actualRecursiveCutLE G j m⊓G j (m+1))=
        p⊓crispTruth B (actualGroundHybridCut g (j+1)≤ m+1)
      have hh := mask_inf_congr_r126 (ih hj.le m)
        (firstNatWeight_decides_monotone_r336 (G j) (hG j) (g j) (m+1) (hChoice j hj))
      have he : (actualGroundHybridCut g j≤ m ∧ g j≤ m+1) ↔ actualGroundHybridCut g (j+1)≤ m+1 := by
        rw [actualGroundHybridCut_succ_r336]
        exact ⟨fun h => max_le (Nat.succ_le_succ h.1) h.2,
          fun h => ⟨Nat.le_of_succ_le_succ ((le_max_left _ _).trans h),(le_max_right _ _).trans h⟩⟩
      exact hh.trans (congrArg (fun b : B => p⊓b)
        ((crisp_and_r190 _ _).symm.trans (crispTruth_propext_r188 he)))

end SetLanguage
end JSP000933
