import JSP000933ActualCodedContinuousFunctions

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem namedBitTable_negative_mask_r312 (C : NamedBitTable B) {p : B}
    (h : p≤namedBitTableValid C) (x : ℕ → B) (m : ℕ) :
    p⊓openValue (C m false) x=p⊓(namedTableOutput C x m)ᶜ :=
  (le_bitEq_iff_r126 _ _ _).mp (h.trans ((iInf_le _ x).trans (iInf_le _ m)))

theorem namedBitTable_covers_r312 (C : NamedBitTable B) {p : B}
    (h : p≤namedBitTableValid C) (x : ℕ → B) (m : ℕ) :
    p≤namedTableOutput C x m⊔openValue (C m false) x := by
  let A := namedTableOutput C x m
  let D := openValue (C m false) x
  calc
    p=p⊓(A⊔Aᶜ) := by rw [sup_compl_eq_top,inf_top_eq]
    _=(p⊓A)⊔(p⊓Aᶜ) := inf_sup_left _ _ _
    _=(p⊓A)⊔(p⊓D) := congrArg (fun a : B => (p⊓A)⊔a) (namedBitTable_negative_mask_r312 C h x m).symm
    _≤A⊔D := sup_le_sup inf_le_right inf_le_right

theorem namedBitTable_oneDigit_local_r312 (C : NamedBitTable B) {p q : B}
    (h : p≤namedBitTableValid C) (x : ℕ → B) (m : ℕ) (hq : q≠⊥) (hqp : q≤p) :
    ∃ (r : B) (u : Word), r≠⊥ ∧ r≤q ∧ r≤cylinderValue x u ∧
      DecidesOnCylinder r u (fun y => namedTableOutput C y m) := by
  let A := namedTableOutput C x m
  let D := openValue (C m false) x
  have hCov : q≤A⊔D := hqp.trans (namedBitTable_covers_r312 C h x m)
  by_cases hA : q⊓A=⊥
  · have hD : q≤D := calc
      q=q⊓(A⊔D) := le_antisymm (le_inf le_rfl hCov) inf_le_left
      _=(q⊓A)⊔(q⊓D) := inf_sup_left _ _ _
      _=q⊓D := by rw [hA,bot_sup_eq]
      _≤D := inf_le_right
    obtain ⟨u,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 q hq
      (fun u : Word => C m false u⊓cylinderValue x u) hD
    refine ⟨r,u,hr,hrq,hR.trans inf_le_right,Or.inr ?_⟩
    intro y t htr hY
    have ht : t≤openValue (C m false) y :=
      le_iSup_of_le u (le_inf (htr.trans (hR.trans inf_le_left)) hY)
    have he := mask_under_r302 (htr.trans (hrq.trans hqp)) (namedBitTable_negative_mask_r312 C h y m)
    exact ((le_inf le_rfl ht).trans_eq he).trans inf_le_right
  · let qA := q⊓A
    obtain ⟨u,r,hr,hrq,hR⟩ := exists_nonzero_below_choice_r135 qA hA
      (fun u : Word => C m true u⊓cylinderValue x u) inf_le_right
    refine ⟨r,u,hr,hrq.trans inf_le_left,hR.trans inf_le_right,Or.inl ?_⟩
    intro y t htr hY
    exact le_iSup_of_le u (le_inf (htr.trans (hR.trans inf_le_left)) hY)

theorem namedBitTable_continuous_r312 (C : NamedBitTable B) {p : B} (h : p≤namedBitTableValid C) :
    NamedContinuousOn p (namedTableOutput C) := by
  intro x N
  induction N with
  | zero =>
    intro q hq _
    obtain ⟨u,_,r,hr,hrq,hR⟩ := exists_decided_initialWord_r136 x 0 q hq
    exact ⟨r,u,hr,hrq,hR,fun _ _ _ _ _ hm => (Nat.not_lt_zero _ hm).elim⟩
  | succ N ih =>
    intro q hq hqp
    obtain ⟨r,u,hr,hrq,hR,hSame⟩ := ih q hq hqp
    obtain ⟨t,v,ht,htr,hV,hDec⟩ := namedBitTable_oneDigit_local_r312 C h x N hr (hrq.trans hqp)
    have hRU : t≤cylinderValue x u := htr.trans hR
    rcases le_total u.length v.length with hL | hL
    · have he := extendsWord_of_compatible_r173 x ht hL hRU hV
      refine ⟨t,v,ht,htr.trans hrq,hV,?_⟩
      intro y s hst hY m hm
      by_cases hm' : m<N
      · exact hSame y s (hst.trans htr) (hY.trans (cylinderWord_mono_r173 y he)) m hm'
      · have heM : m=N := by omega
        subst m
        exact hDec.mask_eq_r286 hst (hst.trans hV) hY
    · have he := extendsWord_of_compatible_r173 x ht hL hV hRU
      refine ⟨t,u,ht,htr.trans hrq,hRU,?_⟩
      intro y s hst hY m hm
      by_cases hm' : m<N
      · exact hSame y s (hst.trans htr) hY m hm'
      · have heM : m=N := by omega
        subst m
        exact hDec.mask_eq_r286 hst (hst.trans hV) (hY.trans (cylinderWord_mono_r173 y he))

end SetLanguage
end JSP000933
