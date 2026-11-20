import JSP000933ActualFirstGoodIndex

open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem finiteClosedBoundary_sameCylinder_r318 (K : ℕ → Word → B) (x : ℕ → B) :
    ∀ (N : ℕ) (p : B), p≠⊥ →
      (∀ i<N, p≤openValue (closedBoundaryRegularCode (K i)) x) →
      ∃ (q : B) (u : Word), q≠⊥ ∧ q≤p ∧ q≤cylinderValue x u ∧
        ∀ i<N, DecidesOnCylinder q u (fun y => (openValue (K i) y)ᶜ) := by
  intro N
  induction N with
  | zero =>
    intro p hp hP
    obtain ⟨u,_,q,hq,hqp,hU⟩ := exists_decided_initialWord_r136 x 0 p hp
    exact ⟨q,u,hq,hqp,hU,fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | succ N ih =>
    intro p hp hP
    obtain ⟨q,u,hq,hqp,hU,hOld⟩ := ih p hp
      (fun i hi => hP i (hi.trans (Nat.lt_succ_self N)))
    obtain ⟨t,v,ht,htq,hV,hNew⟩ := boundaryRegular_local_decision_r280 (K N) x hq
      (hqp.trans (hP N (Nat.lt_succ_self N)))
    have hU' := htq.trans hU
    rcases le_total u.length v.length with hL | hL
    · have he := extendsWord_of_compatible_r173 x ht hL hU' hV
      refine ⟨t,v,ht,htq.trans hqp,hV,?_⟩
      intro i hi
      by_cases hii : i<N
      · exact (hOld i hii).restrict_r285 htq he
      · have hi' : i=N := by omega
        subst i
        exact hNew
    · have he := extendsWord_of_compatible_r173 x ht hL hV hU'
      refine ⟨t,u,ht,htq.trans hqp,hU',?_⟩
      intro i hi
      by_cases hii : i<N
      · exact (hOld i hii).restrict_r285 htq (extendsWord_refl_r216 u)
      · have hi' : i=N := by omega
        subst i
        exact hNew.restrict_r285 le_rfl he

theorem firstNatWeight_mask_r318 {p : B} {V W : ℕ → B} (n : ℕ)
    (h : ∀ i≤n, p⊓V i=p⊓W i) : p⊓firstNatWeight V n=p⊓firstNatWeight W n :=
  mask_inf_congr_r126 (h n le_rfl)
    (mask_iInf_congr_r126 (fun i => mask_compl_congr_r126 (h i.val i.isLt.le)))

theorem closedCode_closedMask_r318 {p q : B} (hqp : q≤p) (K : Word → B) (V : (ℕ → B) → B)
    (x : ℕ → B) (h : p⊓openValue K x=p⊓(V x)ᶜ) :
    q⊓(openValue K x)ᶜ=q⊓V x := by
  have he := mask_compl_congr_r126 (mask_under_r302 hqp h)
  rw [compl_compl] at he
  exact he

end SetLanguage
end JSP000933
