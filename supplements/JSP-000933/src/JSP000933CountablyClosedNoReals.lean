import JSP000933BooleanDecisions
import JSP000933BooleanRealEquality

namespace JSP000933
namespace BooleanCompletion

open CantorCodes

variable {P : Type} [Preorder P]

def IsCountablyClosed (P : Type*) [Preorder P] : Prop :=
  ∀ s : ℕ → P, Antitone s → ∃ q : P, ∀ n, q ≤ s n

theorem exists_decides_all_r185 (hp : IsCountablyClosed P)
    (bits : ℕ → RO P) (p : P) :
    ∃ q : P, q ≤ p ∧ ∀ n, Decides q (bits n) := by
  classical
  let s : ℕ → P := Nat.rec p (fun n r => Classical.choose (exists_stronger_decides_r51 r (bits n)))
  have hstep (n : ℕ) : s (n+1) ≤ s n ∧ Decides (s (n+1)) (bits n) :=
    Classical.choose_spec (exists_stronger_decides_r51 (s n) (bits n))
  obtain ⟨q,hq⟩ := hp s (antitone_nat_of_succ_le (fun n => (hstep n).1))
  exact ⟨q,hq 0,fun n => (hstep n).2.of_stronger_r51 (hq (n+1))⟩

theorem exists_groundBitName_below_r185 (hp : IsCountablyClosed P)
    (bits : ℕ → RO P) (p : P) :
    ∃ q : P, q ≤ p ∧ ∃ x : ℕ → Bool,
      imageCondition q ≤ realEqValue bits (fun n => truthBit (x n)) := by
  classical
  obtain ⟨q,hqp,hq⟩ := exists_decides_all_r185 hp bits p
  let x (n : ℕ) := decide (imageCondition q ≤ bits n)
  refine ⟨q,hqp,x,(le_realEqValue_iff_r126 _ _ _).mpr (fun n => ?_)⟩
  by_cases h : imageCondition q ≤ bits n
  · have hx : x n = true := by simp [x,h]
    rw [hx]
    simpa [truthBit] using (inf_eq_left.mpr h)
  · have hx : x n = false := by simp [x,h]
    rw [hx]
    have hc : imageCondition q ≤ (bits n)ᶜ := (hq n).resolve_left h
    have hh := le_bot_iff.mp (disjoint_iff_inf_le.mp (le_compl_iff_disjoint_right.mp hc))
    simpa [truthBit] using hh

theorem groundBitNames_join_top_r185 (hp : IsCountablyClosed P) (bits : ℕ → RO P) :
    (⨆ x : ℕ → Bool, realEqValue bits (fun n => truthBit (x n))) = ⊤ := by
  classical
  let a := ⨆ x : ℕ → Bool, realEqValue bits (fun n => truthBit (x n))
  apply top_unique
  change ⊤ ≤ a
  by_contra hn
  have hc : aᶜ ≠ ⊥ := by
    intro he
    exact hn (by rw [← compl_compl a,he,compl_bot])
  obtain ⟨p,hpA⟩ := imageCondition_dense_r50 aᶜ hc
  obtain ⟨q,hqp,x,hqx⟩ := exists_groundBitName_below_r185 hp bits p
  have hqA : imageCondition q ≤ a := hqx.trans (le_iSup (fun y : ℕ → Bool => realEqValue bits (fun n => truthBit (y n))) x)
  exact imageCondition_ne_bot_r50 q (le_bot_iff.mp
    ((le_inf hqA ((imageCondition_mono_r50 hqp).trans hpA)).trans_eq (inf_compl_eq_bot' (x := a))))

end BooleanCompletion
end JSP000933
