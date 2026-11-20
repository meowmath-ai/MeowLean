import JSP000933MultiProfileBudgetTriangle

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem GroundBudgetHolds.refl_r228 (h : Bool) (A : Set ℕ) (k n : ℕ) :
    GroundBudgetHolds h A A k n := by
  classical
  cases h <;> simp [GroundBudgetHolds,groundCount,groundScaledHarmonic]

theorem GroundBudgetHolds.triangle_r228 (h : Bool) (A M C : Set ℕ) (k n : ℕ)
    (h₁ : GroundBudgetHolds h A M (2*k) n) (h₂ : GroundBudgetHolds h M C (2*k) n) :
    GroundBudgetHolds h A C k n := by
  cases h
  · change (2*k)*groundCount A M n ≤ n at h₁
    change (2*k)*groundCount M C n ≤ n at h₂
    change k*groundCount A C n ≤ n
    apply (Nat.mul_le_mul_left _ (groundCount_triangle_r227 A M C n)).trans
    rw [Nat.mul_add]
    rw [Nat.mul_assoc] at h₁ h₂
    omega
  · let d := groundScaledHarmonic true A C n n
    let a := groundScaledHarmonic false A M n n
    let b := groundScaledHarmonic false M C n n
    let c := groundScaledHarmonic false A C n n
    change (2*k)*a ≤ groundScaledHarmonic true A M n n at h₁
    change (2*k)*b ≤ groundScaledHarmonic true M C n n at h₂
    rw [groundScaledHarmonic_all_independent_r227 A M A C n n] at h₁
    rw [groundScaledHarmonic_all_independent_r227 M C A C n n] at h₂
    change k*c ≤ d
    apply (Nat.mul_le_mul_left k (groundScaledHarmonic_triangle_r227 A M C n)).trans
    change k*(a+b) ≤ d
    change (2*k)*a ≤ d at h₁
    change (2*k)*b ≤ d at h₂
    rw [Nat.mul_add]
    rw [Nat.mul_assoc] at h₁ h₂
    omega

theorem nameBudgetValue_refl_r228 (h : Bool) (A : bSet B) (k n : ℕ) :
    (⊤ : B) ≤ nameBudgetValue h A A k n := by
  apply le_of_dense_named_refinements_r219
  intro p hp _
  obtain ⟨a,q,hq,hqp,hA⟩ := exists_joint_finiteGroundProfiles_r227 (fun _ : Unit => A) n p hp
  have hh := nameBudgetValue_locallyCrisp_r226 (hA ()) (hA ()) h k
  have hTop : crispTruth B (GroundBudgetHolds h (a ()) (a ()) k n) = (⊤ : B) := by
    simp [crispTruth,GroundBudgetHolds.refl_r228]
  exact ⟨q,hq,hqp,((le_inf le_rfl (le_top.trans_eq hTop.symm)).trans_eq hh.symm).trans inf_le_right⟩

theorem nameBudgetValue_triangle_r228 (h : Bool) (A M C : bSet B) (k n : ℕ) :
    nameBudgetValue h A M (2*k) n ⊓ nameBudgetValue h M C (2*k) n ≤ nameBudgetValue h A C k n := by
  apply le_of_dense_named_refinements_r219
  intro p hp hP
  let f (i : Fin 3) := if i=0 then A else if i=1 then M else C
  obtain ⟨a,q,hq,hqp,hProfile⟩ := exists_joint_finiteGroundProfiles_r227 f n p hp
  have hA (i : ℕ) (hi : i<n) : q ⊓ membershipBits A i =
      q ⊓ membershipBits (groundSubsetName B (a 0)) i := by simpa [f] using hProfile 0 i hi
  have hM (i : ℕ) (hi : i<n) : q ⊓ membershipBits M i =
      q ⊓ membershipBits (groundSubsetName B (a 1)) i := by simpa [f] using hProfile 1 i hi
  have hC (i : ℕ) (hi : i<n) : q ⊓ membershipBits C i =
      q ⊓ membershipBits (groundSubsetName B (a 2)) i := by simpa [f] using hProfile 2 i hi
  have h₁ := nameBudgetValue_locallyCrisp_r226 hA hM h (2*k)
  have h₂ := nameBudgetValue_locallyCrisp_r226 hM hC h (2*k)
  have hAB : GroundBudgetHolds h (a 0) (a 1) (2*k) n :=
    prop_of_le_crisp_nonzero_r190 hq
      (((le_inf le_rfl (hqp.trans (hP.trans inf_le_left))).trans_eq h₁).trans inf_le_right)
  have hBC : GroundBudgetHolds h (a 1) (a 2) (2*k) n :=
    prop_of_le_crisp_nonzero_r190 hq
      (((le_inf le_rfl (hqp.trans (hP.trans inf_le_right))).trans_eq h₂).trans inf_le_right)
  have ht := GroundBudgetHolds.triangle_r228 h (a 0) (a 1) (a 2) k n hAB hBC
  have hTop : crispTruth B (GroundBudgetHolds h (a 0) (a 2) k n) = (⊤ : B) := by
    simp [crispTruth,ht]
  have hEq := nameBudgetValue_locallyCrisp_r226 hA hC h k
  exact ⟨q,hq,hqp,((le_inf le_rfl (le_top.trans_eq hTop.symm)).trans_eq hEq.symm).trans inf_le_right⟩

end SetLanguage
end JSP000933
