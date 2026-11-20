import JSP000933AnchorCrossErrorBudget

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem commonCylinder_maskBit_r250 {q : B} (x y : ℕ → B) (u : Word)
    (hx : q≤cylinderValue x u) (hy : q≤cylinderValue y u) (i : ℕ) (hi : i<u.length) :
    q ⊓ x i = q ⊓ y i := by
  let b : B := truthBit (u[i]'hi)
  have hX : q ≤ bitEq (x i) b := by
    rw [show b = truthBit (u[i]'hi) from rfl,bitEq_truthBit_r175]
    exact hx.trans (iInf_le _ (⟨i,hi⟩ : Fin u.length))
  have hY : q ≤ bitEq (y i) b := by
    rw [show b = truthBit (u[i]'hi) from rfl,bitEq_truthBit_r175]
    exact hy.trans (iInf_le _ (⟨i,hi⟩ : Fin u.length))
  exact ((le_bitEq_iff_r126 q _ _).mp hX).trans ((le_bitEq_iff_r126 q _ _).mp hY).symm

theorem mask_symmDiff_zero_r250 {q x y : B} (h : q ⊓ x = q ⊓ y) :
    q ⊓ ((x ⊓ yᶜ) ⊔ (xᶜ ⊓ y)) = q ⊓ ⊥ := by
  have h1 : q ⊓ (x ⊓ yᶜ) = q ⊓ (x ⊓ xᶜ) :=
    mask_inf_congr_r126 rfl (mask_compl_congr_r126 h.symm)
  have h2 : q ⊓ (xᶜ ⊓ y) = q ⊓ (yᶜ ⊓ y) :=
    mask_inf_congr_r126 (mask_compl_congr_r126 h) rfl
  have hz : yᶜ ⊓ y = ⊥ := by rw [inf_comm,inf_compl_eq_bot']
  simpa only [inf_compl_eq_bot',hz,sup_idem] using mask_sup_congr_r211 h1 h2

theorem anchor_crossError_early_r250 {q : B} (h : Bool) (a b c d : ℕ → B) (k n : ℕ)
    (hCap : ∀ i<n, q ⊓ a i = q ⊓ c i)
    (hPay : ∀ i<n, q ⊓ b i = q ⊓ d i) :
    q ≤ nameBudgetValue h (realBitsName (bitsSymmDiff (bitsMeet a d) (bitsMeet c b)))
      (realBitsName (fun _ => ⊥)) k n := by
  let D := bitsSymmDiff (bitsMeet a d) (bitsMeet c b)
  let z : ℕ → B := fun _ => ⊥
  have hD (i : ℕ) (hi : i<n) : q ⊓ D i = q ⊓ z i :=
    mask_symmDiff_zero_r250 (mask_inf_congr_r126 (hCap i hi) (hPay i hi).symm)
  have hMask (i : ℕ) (hi : i<n) :
      q ⊓ membershipBits (realBitsName D) i = q ⊓ membershipBits (realBitsName z) i := by
    simpa only [membershipBits_realBitsName_r128] using hD i hi
  have hEq := nameBudgetValue_mask_r226 (C := realBitsName z) (C' := realBitsName z) hMask
    (fun _ _ => rfl) h k
  exact ((le_inf le_rfl (le_top.trans (nameBudgetValue_refl_r228 h (realBitsName z) k n))).trans_eq
    hEq.symm).trans inf_le_right

theorem anchor_crossError_smallAll_r250 {q : B} (h : Bool) (H a b c d : ℕ → B) (k : ℕ)
    (u v : Word) (hv : v.length=u.length)
    (ha : q≤cylinderValue a u) (hc : q≤cylinderValue c u)
    (hb : q≤cylinderValue b v) (hd : q≤cylinderValue d v)
    (hA : q ≤ smallTailPrefixes h (2*k) u.length (bitsSymmDiff (bitsMeet H a) b))
    (hC : q ≤ smallTailPrefixes h (2*k) u.length (bitsSymmDiff (bitsMeet H c) d)) :
    q ≤ smallAllPrefixes h k (bitsSymmDiff (bitsMeet a d) (bitsMeet c b)) := by
  apply le_iInf
  intro n
  by_cases hn : u.length≤n
  · exact (le_inf (hA.trans (budgetTail_apply_r229 _ _ _ n hn))
      (hC.trans (budgetTail_apply_r229 _ _ _ n hn))).trans
        (anchor_crossError_budget_r249 h H a b c d k n)
  · have hn' := lt_of_not_ge hn
    exact anchor_crossError_early_r250 h a b c d k n
      (fun i hi => commonCylinder_maskBit_r250 a c u ha hc i (hi.trans hn'))
      (fun i hi => commonCylinder_maskBit_r250 b d v hb hd i (hv.symm ▸ (hi.trans hn')))

end SetLanguage
end JSP000933
