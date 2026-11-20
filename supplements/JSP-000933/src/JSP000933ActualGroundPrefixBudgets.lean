import JSP000933HarmonicBudgetMassBridge

open scoped Flypitch

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nameBudgetValue_crispPrefix_mask_r340 (h : Bool) (k n : ℕ) {p : B}
    {a b : ℕ → B} {A C : Set ℕ}
    (ha : ∀ m<n, p⊓a m=p⊓crispTruth B (m∈A))
    (hb : ∀ m<n, p⊓b m=p⊓crispTruth B (m∈C)) :
    p⊓nameBudgetValue h (realBitsName a) (realBitsName b) k n=
      p⊓crispTruth B (GroundBudgetHolds h A C k n) := by
  have hA (m : ℕ) (hm : m<n) : p⊓membershipBits (realBitsName a) m=
      p⊓membershipBits (groundSubsetName B A) m := by
    rw [membershipBits_realBitsName_r128]
    change p⊓a m=p⊓((bSet.of_nat m : bSet B) ∈ᴮ groundSubsetName B A)
    rw [checkedNat_ground_mem_r197]
    exact ha m hm
  have hB (m : ℕ) (hm : m<n) : p⊓membershipBits (realBitsName b) m=
      p⊓membershipBits (groundSubsetName B C) m := by
    rw [membershipBits_realBitsName_r128]
    change p⊓b m=p⊓((bSet.of_nat m : bSet B) ∈ᴮ groundSubsetName B C)
    rw [checkedNat_ground_mem_r197]
    exact hb m hm
  rw [nameBudgetValue_mask_r226 hA hB h k,nameBudgetValue_ground_r226]

theorem crispXorSet_r340 (A C : Set ℕ) (m : ℕ) :
    (crispTruth B (m∈A)⊓(crispTruth B (m∈C))ᶜ)⊔((crispTruth B (m∈A))ᶜ⊓crispTruth B (m∈C))=
      crispTruth B (m∈xorSet A C) := by
  classical
  by_cases hA : m∈A <;> by_cases hC : m∈C <;>
    simp [xorSet,Set.mem_union,Set.mem_sdiff,hA,hC,crispTruth]

theorem nameErrorBudget_crispPrefix_mask_r340 (h : Bool) (k n : ℕ) {p : B}
    {a b : ℕ → B} {A C : Set ℕ}
    (ha : ∀ m<n, p⊓a m=p⊓crispTruth B (m∈A))
    (hb : ∀ m<n, p⊓b m=p⊓crispTruth B (m∈C)) :
    p⊓nameErrorBudget h k n a b=p⊓crispTruth B (GroundBudgetHolds h (xorSet A C) ∅ k n) := by
  unfold nameErrorBudget
  apply nameBudgetValue_crispPrefix_mask_r340
  · intro m hm
    exact (mask_xor_congr_r257 (ha m hm) (hb m hm)).trans
      (congrArg (fun b : B => p⊓b) (crispXorSet_r340 A C m))
  · intro m hm
    simp [crispTruth]

theorem nameErrorBudget_crispPrefix_sound_r340 (h : Bool) (k n : ℕ) {p : B} (hp : p≠⊥)
    {a b : ℕ → B} {A C : Set ℕ}
    (ha : ∀ m<n, p⊓a m=p⊓crispTruth B (m∈A))
    (hb : ∀ m<n, p⊓b m=p⊓crispTruth B (m∈C))
    (hB : p≤nameErrorBudget h k n a b) : GroundBudgetHolds h (xorSet A C) ∅ k n :=
  prop_of_le_crisp_nonzero_r190 hp
    (((le_inf le_rfl hB).trans_eq (nameErrorBudget_crispPrefix_mask_r340 h k n ha hb)).trans inf_le_right)

theorem nameErrorBudget_crispPrefix_complete_r340 (h : Bool) (k n : ℕ) {p : B}
    {a b : ℕ → B} {A C : Set ℕ}
    (ha : ∀ m<n, p⊓a m=p⊓crispTruth B (m∈A))
    (hb : ∀ m<n, p⊓b m=p⊓crispTruth B (m∈C))
    (hB : GroundBudgetHolds h (xorSet A C) ∅ k n) : p≤nameErrorBudget h k n a b := by
  have hG : p≤crispTruth B (GroundBudgetHolds h (xorSet A C) ∅ k n) := by
    simpa only [crispTruth,ite_eq_left hB] using (le_top : p≤⊤)
  exact ((le_inf le_rfl hG).trans_eq (nameErrorBudget_crispPrefix_mask_r340 h k n ha hb).symm).trans inf_le_right

end SetLanguage
end JSP000933
