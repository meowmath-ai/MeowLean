import JSP000930RawFreshRowCompatibility

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000930.Negative.Cohen JSP000933.MarkedForcing

variable {B I J X : Type} [NontrivialCompleteBooleanAlgebra B] [Fintype I]

variable {site : J → ComplexBits B} {H : I → J → ℕ → ComplexBits B}
variable {p : I → SymbolicTrace J} {A : J → Prop} {z : J}
variable {t : CohenTotal B (X × ℕ)}
variable {route : FreshRows p z × Bool → X} {interval : FreshRows p z × Bool → Interval}
variable {a b : B}

structure FreshTargetBatch
    (S : FreshCenterBatch site H p A z t route interval a) (d : I → PolyTrace B J) (m : B) where
  guard : ∀ k : FreshRows p z,OldTracePinGuard (d k.1) site z m
  ε : FreshRows p z → ℚ
  pos : ∀ k,0 < ε k
  cap : ∀ k,ε k ≤ (S.fresh k).e
  fit : ∀ k,(ε k+ε k)*(((d k.1).radius : ℚ)+(guard k).L)^(oldSiteAtoms (d k.1)).length ≤
    ((d k.1).budget-(d k.1).budget/2)*(guard k).r
  query_valid : ∀ k : FreshRows p z,((d k.1).eval (site z)).CutOn m
  query_near : ∀ k : FreshRows p z,m ≤ distanceLe ((d k.1).eval (site z))
    (ComplexBits.checked (gaussianRat (S.fresh k).c)) (S.fresh k).e
  inside : ∀ k j,
    ((interval (k,j)).follow (completeRowWord t.trace (route (k,j)))).left <
      centerComponent (S.fresh k).c j - ((S.fresh k).e+ε k) ∧
    centerComponent (S.fresh k).c j + ((S.fresh k).e+ε k) <
      ((interval (k,j)).follow (completeRowWord t.trace (route (k,j)))).right

set_option maxHeartbeats 600000 in
theorem exists_old_target_batch (S : FreshCenterBatch site H p A z t route interval a)
    (d : I → PolyTrace B J) (hb : b ≠ ⊥) (hbA : b ≤ a)
    (hSite : ∀ j,(site j).CutOn (⊤ : B))
    (hSep : ∀ i,∀ j ∈ (d i).pins,(⊤ : B) ≤ ((site z).name =ᴮ (site j).name)ᶜ)
    (hOld : ∀ i,b ≤ (polynomialQ site (H i)).refines (some (d i)) (some (S.center i))) :
    ∃ s : B,s ≠ ⊥ ∧ s ≤ b ∧ Nonempty (FreshTargetBatch S d s) := by
  classical
  let P (k : FreshRows p z) (m : B) := Nonempty (OldTracePinGuard (d k.1) site z m)
  obtain ⟨s,hs,hsB,hS⟩ := exists_finitely_refined_marks P
    (by
      intro k a b hab hB
      obtain ⟨G⟩ := hB
      exact ⟨G.mono hab⟩) b hb (by
      intro k m hm hmB
      have hCoe : m ≤ coeffValue (d k.1).coeff :=
        hmB.trans ((hOld k.1).trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
      exact exists_oldTracePinGuard (d k.1) site z m hm hCoe
        (fun j => cutOn_mono930 (hSite j) le_top) (fun j hj => le_top.trans (hSep k.1 j hj)))
  let D (k : FreshRows p z) := Classical.choice (hS k)
  have hE (k : FreshRows p z) := (D k).tolerance (S.fresh k).e (S.fresh k).pos_budget
  choose ε hε hCap hFit using hE
  refine ⟨s,hs,hsB,⟨⟨D,ε,hε,hCap,hFit,?_ ,?_ ,?_⟩⟩⟩
  · intro k
    have hc : s ≤ coeffValue (d k.1).coeff :=
      hsB.trans ((hOld k.1).trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
    exact eval_cutOn_of_coeff hc (cutOn_mono930 (hSite z) le_top)
  · intro k
    let G := S.fresh k
    have hR := hsB.trans (hOld k.1)
    rw [S.center_of_fresh k] at hR
    have hz := newPinNumber_site (p k.1) z k.2
    have hNear := old_witness_eval_near_center site (H k.1) (d k.1) _ s hs hR
      (site (pinAt (p k.1) (newPinNumber (p k.1) z k.2)).1)
      (cutOn_mono930 (hSite _) le_top) (gaussianRat G.c)
      ((hsB.trans hbA).trans G.center_at_pin) G.K ((hsB.trans hbA).trans G.radius_cover) G.strict_radius
    simpa only [hz,oldCenteredTrace] using hNear
  · intro k j
    have hh := (S.fresh k).clearBox j
    exact ⟨by linarith [hh.1,hCap k],by linarith [hh.2,hCap k]⟩

end JSP000930.Negative
