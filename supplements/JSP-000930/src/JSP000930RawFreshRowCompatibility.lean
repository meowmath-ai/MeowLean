import JSP000930OldWitnessPinGuard

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing

variable {B J : Type} [NontrivialCompleteBooleanAlgebra B]

set_option maxHeartbeats 700000 in
theorem raw_fresh_row_common_of_actual_bounds
    (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (A : J → Prop) (p : SymbolicTrace J) (i : PinNumber p) (c : ℚ × ℚ)
    (R : ℕ) (e cap ε : ℚ) (he : 0 < e) (hR : p.radius ≤ R)
    (hε : 0 < ε) (heCap : ε ≤ e) (hCap : 3*e ≤ cap)
    (d : PolyTrace B J) (m : B) (hm : m ≠ ⊥)
    (hSupport : ∀ j ∈ d.pins,A j) (hNew : ¬ A (pinAt p i).1)
    (hOld : m ≤ (polynomialQ site H).refines (some d)
      (some (oldCenteredTrace site H p i c R e he)))
    (hSite : ∀ j,(site j).CutOn m)
    (hH : ∀ j ∈ p.pins.map Prod.fst,∀ n,(H j n).CutOn m)
    (hApart : ∀ j ∈ p.pins.map Prod.fst,∀ k ∈ p.pins.map Prod.fst,j ≠ k →
      m ≤ ((site j).name =ᴮ (site k).name)ᶜ)
    (hSep : ∀ j ∈ d.pins,m ≤ ((site (pinAt p i).1).name =ᴮ (site j).name)ᶜ)
    (G : IncomingGeometry p site m) (D : OldTracePinGuard d site (pinAt p i).1 m)
    (hFit : (ε+ε)*((d.radius : ℚ)+D.L)^(oldSiteAtoms d).length ≤
      (d.budget-d.budget/2)*D.r)
    (hBudget : e+cap/G.r*(G.L+G.L)^p.pins.length ≤ p.budget)
    (hTarget : m ≤ distanceLe (H (pinAt p i).1 (pinAt p i).2)
      (d.eval (site (pinAt p i).1)) (ε+ε))
    (hClose : m ≤ distanceLe (H (pinAt p i).1 (pinAt p i).2)
      (ComplexBits.checked (gaussianRat c)) (ε+(ε+e))) :
    ∃ q : PolyTrace B J,(∀ j ∈ q.pins,A j ∨ j=(pinAt p i).1) ∧
      m ≤ (polynomialQ site H).refines (some q) (some d) ∧
      m ≤ (polynomialQ site H).refines (some q) (some (decodeSymbolicTrace site H p)) := by
  classical
  let z := (pinAt p i).1
  let n := (pinAt p i).2
  have hz : z ∉ d.pins := fun h => hNew (hSupport _ h)
  have hD : m ≤ polyValid site H d := hOld.trans (inf_le_left.trans inf_le_left)
  have hB : 0 < d.budget/2 := by linarith [d.budget_pos]
  have hB' : d.budget/2 ≤ d.budget := by linarith [d.budget_pos]
  have hY : (H z n).CutOn m := hH z (pinAt_mem_symbolicSite p i) n
  obtain ⟨q,hPins,_,_,hPin,hRef⟩ := exists_refining_polynomial_pin_with_value site H d m
    z n hz hD hSite hY hSep D.L (ε+ε) D.r (d.budget/2) D.L_nonneg (by linarith) D.r_pos
    hB hB' hFit D.old_norm hTarget D.d D.d_sq (D.denominator_target (H z n))
  have hCent := (le_inf hRef hOld).trans ((polynomialQ site H).trans _ _ _)
  have hη : 0 ≤ ε+(ε+e) := by linarith
  have hCap' : ε+(ε+e) ≤ cap := by linarith
  have hFit' := earlier_center_retarget_allowance p G.L G.r cap e (ε+(ε+e)) G.one_le
    G.positive hCap' hBudget
  have hzq : z ∈ q.pins := by rw [hPins]; exact Finset.mem_insert_self _ _
  have hIn := retargeted_refines_incoming site H p i c R e he hR q m hm hCent hzq hPin
    (fun j _ => hSite j) hH hApart G.L (ε+(ε+e)) G.r G.one_le G.positive hη
    G.rad_le G.norms hClose (G.margin_any p site m H) hFit'
  refine ⟨q,?_,hRef,hIn⟩
  intro j hj
  rw [hPins] at hj
  exact (Finset.mem_insert.mp hj).elim Or.inr (fun h => Or.inl (hSupport j h))

end JSP000930.Negative
