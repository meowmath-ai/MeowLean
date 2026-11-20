import JSP000933ActualFiniteBoundaryDecisions

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure NamedRegularOn (p : B) (f : (ℕ → B) → ℕ → B) where
  code : ℕ → Word → B
  dense : ∀ n, DenseOpenNaming p (code n)
  localAt : ∀ (x : ℕ → B) (N : ℕ) (q : B), q≠⊥ → q≤p →
    q≤(⨅ n : ℕ, openValue (code n) x) →
    ∃ (r : B) (u : Word), r≠⊥ ∧ r≤q ∧ r≤cylinderValue x u ∧
      ∀ (y : ℕ → B) (s : B), s≤r → s≤cylinderValue y u → ∀ m<N, s⊓f x m=s⊓f y m

theorem firstNamedIndexOutput_regular_r319 (p : B) (V : (ℕ → B) → ℕ → B)
    (K : ℕ → Word → B) (f : ℕ → (ℕ → B) → ℕ → B)
    (hK : ∀ x i, p⊓openValue (K i) x=p⊓(V x i)ᶜ)
    (hC : ∀ i, NamedContinuousOn p (f i))
    (hCov : ∀ x, p≤⨆ i, V x i) : Nonempty (NamedRegularOn p (firstNamedIndexOutput V f)) := by
  let R (n : ℕ) : Word → B := closedBoundaryRegularCode (K n)
  refine ⟨⟨R,fun n => (closedBoundaryRegular_dense_r280 (K n)).restrict_r293 le_top,?_⟩⟩
  intro x N q hq hqp hReg
  have hW : q≤⨆ i, firstNatWeight (V x) i :=
    (hqp.trans (hCov x)).trans_eq (firstNatWeight_covers_r317 (V x)).symm
  obtain ⟨i,r,hr,hrq,hI⟩ := exists_nonzero_below_choice_r135 q hq (firstNatWeight (V x)) hW
  obtain ⟨t,u,ht,htr,hU,hDec⟩ := finiteClosedBoundary_sameCylinder_r318 K x (i+1) r hr
    (fun j _ => hrq.trans (hReg.trans (iInf_le _ j)))
  have htp : t≤p := htr.trans (hrq.trans hqp)
  obtain ⟨v,w,hv,hvt,hV,hF⟩ := hC i x N t ht htp
  have hFinish (y : ℕ → B) (s : B) (hsv : s≤v)
      (hYU : s≤cylinderValue y u) (hYV : s≤cylinderValue y w) (m : ℕ) (hm : m<N) :
      s⊓firstNamedIndexOutput V f x m=s⊓firstNamedIndexOutput V f y m := by
    have hst : s≤t := hsv.trans hvt
    have hsp : s≤p := hst.trans htp
    have hW' : s≤firstNatWeight (V x) i := hst.trans (htr.trans hI)
    have hEq (j : ℕ) (hj : j≤ i) : s⊓V x j=s⊓V y j :=
      (closedCode_closedMask_r318 hsp (K j) (fun z => V z j) x (hK x j)).symm.trans
        (((hDec j (Nat.lt_succ_of_le hj)).mask_eq_r286 hst (hst.trans hU) hYU).trans
          (closedCode_closedMask_r318 hsp (K j) (fun z => V z j) y (hK y j)))
    have hY : s≤firstNatWeight (V y) i :=
      ((le_inf le_rfl hW').trans_eq (firstNatWeight_mask_r318 i hEq)).trans inf_le_right
    have hOX := (le_realEqValue_iff_r126 _ _ _).mp
      (hW'.trans (firstNamedIndexOutput_mask_r317 V f x i)) m
    have hOY := (le_realEqValue_iff_r126 _ _ _).mp
      (hY.trans (firstNamedIndexOutput_mask_r317 V f y i)) m
    exact hOX.trans ((hF y s hsv hYV m hm).trans hOY.symm)
  have hVU : v≤cylinderValue x u := hvt.trans hU
  rcases le_total u.length w.length with hl | hl
  · have he := extendsWord_of_compatible_r173 x hv hl hVU hV
    exact ⟨v,w,hv,hvt.trans (htr.trans hrq),hV,
      fun y s hs hY => hFinish y s hs (hY.trans (cylinderWord_mono_r173 y he)) hY⟩
  · have he := extendsWord_of_compatible_r173 x hv hl hV hVU
    exact ⟨v,u,hv,hvt.trans (htr.trans hrq),hVU,
      fun y s hs hY => hFinish y s hs hY (hY.trans (cylinderWord_mono_r173 y he))⟩

end SetLanguage
end JSP000933
