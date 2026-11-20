import JSP000933BooleanDenseCliqueSamples

namespace JSP000933
namespace CantorCodes

variable {B W : Type} [CompleteBooleanAlgebra B]

theorem exists_nonzero_below_choice_r135 (p : B) (hN : p ≠ ⊥) (f : W → B) (h : p ≤ ⨆ w, f w) :
    ∃ w : W, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ q ≤ f w := by
  classical
  by_contra hn
  apply hN
  apply le_bot_iff.mp
  have hp : p ≤ p ⊓ (⨆ w, f w) := le_inf le_rfl h
  apply hp.trans
  rw [inf_iSup_eq]
  apply iSup_le
  intro w
  by_contra hw
  exact hn ⟨w,p ⊓ f w,fun he => hw he.le,inf_le_left,inf_le_right⟩

theorem exists_nonzero_finiteChoices_fin_r135 :
    ∀ n : ℕ, ∀ (f : Fin n → W → B) (p : B), p ≠ ⊥ →
      (p ≤ ⨅ i, ⨆ w, f i w) →
      ∃ g : Fin n → W, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ ∀ i, q ≤ f i (g i) := by
  intro n
  induction n with
  | zero =>
    intro f p hN h
    exact ⟨Fin.elim0,p,hN,le_rfl,fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro f p hN h
    obtain ⟨old,q,hQ,hQP,hq⟩ := ih (fun i => f i.castSucc) p hN
      (le_iInf (fun i => h.trans (iInf_le (fun j => ⨆ w, f j w) i.castSucc)))
    obtain ⟨w,r,hRN,hRQ,hr⟩ := exists_nonzero_below_choice_r135 q hQ (f (Fin.last n))
      ((hQP.trans h).trans (iInf_le (fun j => ⨆ w, f j w) (Fin.last n)))
    let g : Fin (n+1) → W := Fin.lastCases w old
    refine ⟨g,r,hRN,hRQ.trans hQP,fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [g] using hr
    · simpa [g] using hRQ.trans (hq j)

theorem exists_nonzero_finiteChoices_r135 {I : Type} [Fintype I]
    (f : I → W → B) (p : B) (hN : p ≠ ⊥)
    (h : p ≤ ⨅ i, ⨆ w, f i w) :
    ∃ g : I → W, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧ ∀ i, q ≤ f i (g i) := by
  classical
  let e := Fintype.equivFin I
  obtain ⟨g,q,hq,hqp,hG⟩ := exists_nonzero_finiteChoices_fin_r135 (Fintype.card I)
    (fun i => f (e.symm i)) p hN (le_iInf (fun i => h.trans (iInf_le _ (e.symm i))))
  refine ⟨fun i => g (e i),q,hq,hqp,fun i => ?_⟩
  simpa only [Equiv.symm_apply_apply] using hG (e i)

end CantorCodes
end JSP000933
