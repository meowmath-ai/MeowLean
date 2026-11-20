import JSP000933HarmonicPrefixValue

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem bTruth_ordinaryBudget_checked_r200 {n : ℕ} (v : DVec (V B) n)
    (a b k p : STerm n) (A C : Set ℕ) (K P : ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C)
    (hk : bTerm v k = bSet.of_nat K) (hp : bTerm v p = bSet.of_nat P) :
    bTruth v (ordinaryBudget_f a b k p) = crispTruth B (K * groundCount A C P ≤ P) := by
  let y : STerm (n+1) := bd_var ⟨0,by omega⟩
  let z : STerm (n+2) := bd_var ⟨0,by omega⟩
  let w (u t : ℕ) := DVec.cons (bSet.of_nat t) (DVec.cons (bSet.of_nat u) v)
  have hy (u t : ℕ) : bTerm (w u t) (up y) = bSet.of_nat u :=
    (bTerm_up_r181 _ _ y).trans (bTerm_current_r181 _ _)
  have hz (u t : ℕ) : bTerm (w u t) z = bSet.of_nat t := bTerm_current_r181 _ _
  have hc (u t : ℕ) :
      bTruth (w u t) (ordinaryPrefixCount_f (up2 a) (up2 b) (up2 p) (up y)) =
        crispTruth B (u=groundCount A C P) :=
    bTruth_ordinaryPrefix_checked_r197 _ _ _ _ _ A C P u ((bTerm_up2_r181 v _ _ a).trans ha)
      ((bTerm_up2_r181 v _ _ b).trans hb) ((bTerm_up2_r181 v _ _ p).trans hp) (hy u t)
  have hm (u t : ℕ) :
      bTruth (w u t) (multiplication_f (up2 k) (up y) z) = crispTruth B (t=K*u) :=
    bTruth_multiplication_checked_r196 _ _ _ _ K u t ((bTerm_up2_r181 v _ _ k).trans hk) (hy u t) (hz u t)
  have hle (u t : ℕ) :
      bTruth (w u t) (natLE_f z (up2 p)) = crispTruth B (t≤P) :=
    bTruth_natLE_checked_r192 _ _ _ t P (hz u t) ((bTerm_up2_r181 v _ _ p).trans hp)
  simp only [ordinaryBudget_f,bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ u : ℕ, ⨆ t : ℕ, bTruth (w u t) (ordinaryPrefixCount_f (up2 a) (up2 b) (up2 p) (up y)) ⊓
    (bTruth (w u t) (multiplication_f (up2 k) (up y) z) ⊓ bTruth (w u t) (natLE_f z (up2 p)))) = _
  simp only [hc,hm,hle,← crisp_and_r190,iSup_crisp_r192]
  apply crispTruth_propext_r188
  constructor
  · rintro ⟨u,t,rfl,rfl,h⟩
    exact h
  · intro h
    exact ⟨_,_,rfl,rfl,h⟩

theorem bTruth_harmonicBudget_checked_r200 {n : ℕ} (v : DVec (V B) n)
    (a b k p : STerm n) (A C : Set ℕ) (K P : ℕ)
    (ha : bTerm v a = groundSubsetName B A) (hb : bTerm v b = groundSubsetName B C)
    (hk : bTerm v k = bSet.of_nat K) (hp : bTerm v p = bSet.of_nat P) :
    bTruth v (harmonicBudget_f a b k p) =
      crispTruth B (K * groundScaledHarmonic false A C P P ≤ groundScaledHarmonic true A C P P) := by
  let s : STerm (n+1) := bd_var ⟨0,by omega⟩
  let t : STerm (n+2) := bd_var ⟨0,by omega⟩
  let r : STerm (n+3) := bd_var ⟨0,by omega⟩
  let w (x y z : ℕ) :=
    DVec.cons (bSet.of_nat z) (DVec.cons (bSet.of_nat y) (DVec.cons (bSet.of_nat x) v))
  have hx (x y z : ℕ) : bTerm (w x y z) (up2 s) = bSet.of_nat x :=
    (bTerm_up2_r181 _ _ _ s).trans (bTerm_current_r181 _ _)
  have hy (x y z : ℕ) : bTerm (w x y z) (up t) = bSet.of_nat y :=
    (bTerm_up_r181 _ _ t).trans (bTerm_current_r181 _ _)
  have hz (x y z : ℕ) : bTerm (w x y z) r = bSet.of_nat z := bTerm_current_r181 _ _
  have hNum (x y z : ℕ) :
      bTruth (w x y z) (harmonicPrefixMass_f false (up3 a) (up3 b) (up3 p) (up2 s)) =
        crispTruth B (x=groundScaledHarmonic false A C P P) :=
    bTruth_harmonicPrefix_checked_r199 _ false _ _ _ _ A C P x
      ((bTerm_up3_r181 v _ _ _ a).trans ha) ((bTerm_up3_r181 v _ _ _ b).trans hb)
      ((bTerm_up3_r181 v _ _ _ p).trans hp) (hx x y z)
  have hDen (x y z : ℕ) :
      bTruth (w x y z) (harmonicPrefixMass_f true (up3 a) (up3 b) (up3 p) (up t)) =
        crispTruth B (y=groundScaledHarmonic true A C P P) :=
    bTruth_harmonicPrefix_checked_r199 _ true _ _ _ _ A C P y
      ((bTerm_up3_r181 v _ _ _ a).trans ha) ((bTerm_up3_r181 v _ _ _ b).trans hb)
      ((bTerm_up3_r181 v _ _ _ p).trans hp) (hy x y z)
  have hMul (x y z : ℕ) :
      bTruth (w x y z) (multiplication_f (up3 k) (up2 s) r) = crispTruth B (z=K*x) :=
    bTruth_multiplication_checked_r196 _ _ _ _ K x z ((bTerm_up3_r181 v _ _ _ k).trans hk)
      (hx x y z) (hz x y z)
  have hLE (x y z : ℕ) : bTruth (w x y z) (natLE_f r (up t)) = crispTruth B (z≤y) :=
    bTruth_natLE_checked_r192 _ _ _ z y (hz x y z) (hy x y z)
  simp only [harmonicBudget_f,bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ x : ℕ, ⨆ y : ℕ, ⨆ z : ℕ,
    bTruth (w x y z) (harmonicPrefixMass_f false (up3 a) (up3 b) (up3 p) (up2 s)) ⊓
    (bTruth (w x y z) (harmonicPrefixMass_f true (up3 a) (up3 b) (up3 p) (up t)) ⊓
      (bTruth (w x y z) (multiplication_f (up3 k) (up2 s) r) ⊓ bTruth (w x y z) (natLE_f r (up t))))) = _
  simp only [hNum,hDen,hMul,hLE,← crisp_and_r190,iSup_crisp_r192]
  apply crispTruth_propext_r188
  constructor
  · rintro ⟨x,y,z,rfl,rfl,rfl,h⟩
    exact h
  · intro h
    exact ⟨_,_,_,rfl,rfl,rfl,h⟩

end SetLanguage
end JSP000933
