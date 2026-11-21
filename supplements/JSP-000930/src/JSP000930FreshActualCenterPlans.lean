import JSP000930AnalyticProductRealLabels

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Dyadic JSP000930.Positive.Cohen
open JSP000930.Negative.Cohen JSP000933.MarkedForcing

variable {B J X : Type} [NontrivialCompleteBooleanAlgebra B]

structure FreshCenterPlan (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace J) (i : PinNumber p) (A : J → Prop)
    (t : CohenTotal B (X × ℕ)) (route : Bool → X) (interval : Bool → Interval) (m : B) where
  c : ℚ × ℚ
  K : ℕ
  R : ℕ
  e : ℚ
  cap : ℚ
  geometry : IncomingGeometry p site m
  pos_budget : 0 < e
  strict_cap : 3*e ≤ cap
  incoming_radius : p.radius ≤ R
  radius_cover : m ≤ halfRadiusBound (site (pinAt p i).1) K
  strict_radius : (K : ℝ)/2 < (R : ℝ)
  allowance : e + cap/geometry.r*(geometry.L+geometry.L)^p.pins.length ≤ p.budget
  clearBox : ∀ j, ((interval j).follow (completeRowWord t.trace (route j))).left <
      centerComponent c j - 2*e ∧ centerComponent c j + 2*e <
      ((interval j).follow (completeRowWord t.trace (route j))).right
  center_valid : m ≤ polyValid site H (oldCenteredTrace site H p i c R e pos_budget)
  center_support : ∀ z ∈ (oldCenteredTrace site H p i c R e pos_budget).pins,A z
  center_at_pin : m ≤ ((oldCenteredTrace site H p i c R e pos_budget).eval
      (site (pinAt p i).1)).name =ᴮ (ComplexBits.checked (gaussianRat c)).name

def FreshCenterPlan.mono {site : J → ComplexBits B} {H : J → ℕ → ComplexBits B}
    {p : SymbolicTrace J} {i : PinNumber p} {A : J → Prop}
    {t : CohenTotal B (X × ℕ)} {route : Bool → X} {interval : Bool → Interval}
    {m b : B} (G : FreshCenterPlan site H p i A t route interval m) (h : b ≤ m) :
    FreshCenterPlan site H p i A t route interval b :=
  ⟨G.c,G.K,G.R,G.e,G.cap,IncomingGeometry.mono p site G.geometry h,G.pos_budget,G.strict_cap,
    G.incoming_radius,h.trans G.radius_cover,G.strict_radius,G.allowance,G.clearBox,
    h.trans G.center_valid,G.center_support,h.trans G.center_at_pin⟩

set_option maxHeartbeats 600000 in
theorem exists_fresh_center_plan (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
    (p : SymbolicTrace J) (i : PinNumber p) (A : J → Prop)
    (t : CohenTotal B (X × ℕ)) (route : Bool → X) (interval : Bool → Interval)
    (m : B) (hm : m ≠ ⊥)
    (hSite : ∀ j ∈ p.pins.map Prod.fst,(site j).CutOn m)
    (hH : ∀ j ∈ p.pins.map Prod.fst,j ≠ (pinAt p i).1 → ∀ n,(H j n).CutOn m)
    (hOld : ∀ j ∈ p.pins.map Prod.fst,j ≠ (pinAt p i).1 → A j)
    (hApart : ∀ j ∈ p.pins.map Prod.fst,∀ k ∈ p.pins.map Prod.fst,j ≠ k →
      m ≤ ((site j).name =ᴮ (site k).name)ᶜ) :
    ∃ (s : B),s ≠ ⊥ ∧ s ≤ m ∧ Nonempty (FreshCenterPlan site H p i A t route interval s) := by
  classical
  let box (j : Bool) := (interval j).follow (completeRowWord t.trace (route j))
  let c : ℚ × ℚ := ((box false).mid,(box true).mid)
  have hmid (j : Bool) : centerComponent c j = (box j).mid := by cases j <;> rfl
  have h1 (j : Bool) : 0 < (box j).mid-(box j).left := by
    unfold Interval.mid
    linarith [(box j).positive]
  have h2 (j : Bool) : 0 < (box j).right-(box j).mid := by
    unfold Interval.mid
    linarith [(box j).positive]
  let W := min (min ((box false).mid-(box false).left) ((box false).right-(box false).mid))
    (min ((box true).mid-(box true).left) ((box true).right-(box true).mid))
  have hW : 0 < W := lt_min (lt_min (h1 false) (h2 false)) (lt_min (h1 true) (h2 true))
  have hWT (j : Bool) : W ≤ min ((box j).mid-(box j).left) ((box j).right-(box j).mid) := by
    cases j
    · exact min_le_left _ _
    · exact min_le_right _ _
  obtain ⟨s,K,R,hs,hsM,hR,hStrict,hCover,⟨G⟩⟩ :=
    exists_center_window_geometry p i site m hm hSite hApart
  obtain ⟨b,e,hb,he,hCap,hWidth,hBud⟩ := exists_earlier_center_budgets p G.L G.r W G.one_le G.positive hW
  obtain ⟨hV,hAt⟩ := oldCenteredTrace_valid_exact site H p i c R e he s
    (fun j hj => cutOn_mono930 (hSite j hj) hsM)
    (fun j hj hn n => cutOn_mono930 (hH j hj hn n) hsM)
    (fun j hj k hk hn => hsM.trans (hApart j hj k hk hn))
  refine ⟨s,hs,hsM,⟨⟨c,K,R,e,b,G,he,hCap,hR,hCover,hStrict,hBud,?_,hV,?_,hAt⟩⟩⟩
  · intro j
    rw [hmid]
    change (box j).left < (box j).mid - 2*e ∧ (box j).mid+2*e < (box j).right
    have ha := (hWT j).trans (min_le_left _ _)
    have hb := (hWT j).trans (min_le_right _ _)
    exact ⟨by linarith,by linarith⟩
  · intro j hj
    change j ∈ (p.pins.map Prod.fst).toFinset.erase (pinAt p i).1 at hj
    exact hOld j (List.mem_toFinset.mp (Finset.mem_of_mem_erase hj)) (Finset.ne_of_mem_erase hj)

end JSP000930.Negative
