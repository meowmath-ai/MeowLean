import JSP000933MixedFinitePrefixLocality

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def mixedOrdinaryPrefixValue (A C : bSet B) (n r : ℕ) : B :=
  recurrenceOfTables B n 0 r (mixedOrdinaryStep A C)

noncomputable def mixedHarmonicPrefixValue (allBits : Bool) (A C : bSet B) (n r : ℕ) : B :=
  recurrenceOfTables B n 0 r (mixedHarmonicStep allBits A C (Nat.factorial n))

noncomputable def mixedOrdinaryBudgetValue (A C : bSet B) (k n : ℕ) : B :=
  ⨆ r : ℕ, mixedOrdinaryPrefixValue A C n r ⊓ crispTruth B (k*r ≤ n)

noncomputable def mixedHarmonicBudgetValue (A C : bSet B) (k n : ℕ) : B :=
  ⨆ r : ℕ, ⨆ s : ℕ,
    mixedHarmonicPrefixValue false A C n r ⊓
      (mixedHarmonicPrefixValue true A C n s ⊓ crispTruth B (k*r ≤ s))

theorem bTruth_mixedOrdinaryBudget_r212 {n : ℕ} (v : DVec (V B) n) (a b k p : STerm n)
    (K P : ℕ) (hk : bTerm v k = bSet.of_nat K) (hp : bTerm v p = bSet.of_nat P) :
    bTruth v (ordinaryBudget_f a b k p) = mixedOrdinaryBudgetValue (bTerm v a) (bTerm v b) K P := by
  let y : STerm (n+1) := bd_var ⟨0,by omega⟩
  let z : STerm (n+2) := bd_var ⟨0,by omega⟩
  let w (u t : ℕ) : DVec (V B) (n+2) := DVec.cons (bSet.of_nat t) (DVec.cons (bSet.of_nat u) v)
  have hy (u t : ℕ) : bTerm (w u t) (up y) = bSet.of_nat u :=
    (bTerm_up_r181 _ _ y).trans (bTerm_current_r181 _ _)
  have hz (u t : ℕ) : bTerm (w u t) z = bSet.of_nat t := bTerm_current_r181 _ _
  have hc (u t : ℕ) :
      bTruth (w u t) (ordinaryPrefixCount_f (up2 a) (up2 b) (up2 p) (up y)) =
        mixedOrdinaryPrefixValue (bTerm v a) (bTerm v b) P u := by
    have hP : bTerm (w u t) (up2 p) = bSet.of_nat P := (bTerm_up2_r181 v _ _ p).trans hp
    rw [bTruth_mixedOrdinaryPrefix_r210 (w u t) _ _ _ _ P u hP (hy u t)]
    unfold mixedOrdinaryPrefixValue
    rw [show bTerm (w u t) (up2 a) = bTerm v a from bTerm_up2_r181 v _ _ a,
      show bTerm (w u t) (up2 b) = bTerm v b from bTerm_up2_r181 v _ _ b]
  have hm (u t : ℕ) :
      bTruth (w u t) (multiplication_f (up2 k) (up y) z) = crispTruth B (t=K*u) :=
    bTruth_multiplication_checked_r196 _ _ _ _ K u t ((bTerm_up2_r181 v _ _ k).trans hk) (hy u t) (hz u t)
  have hle (u t : ℕ) :
      bTruth (w u t) (natLE_f z (up2 p)) = crispTruth B (t≤P) :=
    bTruth_natLE_checked_r192 _ _ _ t P (hz u t) ((bTerm_up2_r181 v _ _ p).trans hp)
  simp only [ordinaryBudget_f,bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ u : ℕ, ⨆ t : ℕ, bTruth (w u t) (ordinaryPrefixCount_f (up2 a) (up2 b) (up2 p) (up y)) ⊓
    (bTruth (w u t) (multiplication_f (up2 k) (up y) z) ⊓ bTruth (w u t) (natLE_f z (up2 p)))) = _
  simp only [hc,hm,hle,← inf_iSup_eq,iSup_crispEquality_select_r193,mixedOrdinaryBudgetValue]

theorem bTruth_mixedHarmonicBudget_r212 {n : ℕ} (v : DVec (V B) n) (a b k p : STerm n)
    (K P : ℕ) (hk : bTerm v k = bSet.of_nat K) (hp : bTerm v p = bSet.of_nat P) :
    bTruth v (harmonicBudget_f a b k p) = mixedHarmonicBudgetValue (bTerm v a) (bTerm v b) K P := by
  let s : STerm (n+1) := bd_var ⟨0,by omega⟩
  let t : STerm (n+2) := bd_var ⟨0,by omega⟩
  let r : STerm (n+3) := bd_var ⟨0,by omega⟩
  let w (x y z : ℕ) : DVec (V B) (n+3) :=
    DVec.cons (bSet.of_nat z) (DVec.cons (bSet.of_nat y) (DVec.cons (bSet.of_nat x) v))
  have hx (x y z : ℕ) : bTerm (w x y z) (up2 s) = bSet.of_nat x :=
    (bTerm_up2_r181 _ _ _ s).trans (bTerm_current_r181 _ _)
  have hy (x y z : ℕ) : bTerm (w x y z) (up t) = bSet.of_nat y :=
    (bTerm_up_r181 _ _ t).trans (bTerm_current_r181 _ _)
  have hz (x y z : ℕ) : bTerm (w x y z) r = bSet.of_nat z := bTerm_current_r181 _ _
  have hNum (x y z : ℕ) :
      bTruth (w x y z) (harmonicPrefixMass_f false (up3 a) (up3 b) (up3 p) (up2 s)) =
        mixedHarmonicPrefixValue false (bTerm v a) (bTerm v b) P x := by
    have hP : bTerm (w x y z) (up3 p) = bSet.of_nat P := (bTerm_up3_r181 v _ _ _ p).trans hp
    rw [bTruth_mixedHarmonicPrefix_r210 (w x y z) false _ _ _ _ P x hP (hx x y z)]
    unfold mixedHarmonicPrefixValue
    rw [show bTerm (w x y z) (up3 a) = bTerm v a from bTerm_up3_r181 v _ _ _ a,
      show bTerm (w x y z) (up3 b) = bTerm v b from bTerm_up3_r181 v _ _ _ b]
  have hDen (x y z : ℕ) :
      bTruth (w x y z) (harmonicPrefixMass_f true (up3 a) (up3 b) (up3 p) (up t)) =
        mixedHarmonicPrefixValue true (bTerm v a) (bTerm v b) P y := by
    have hP : bTerm (w x y z) (up3 p) = bSet.of_nat P := (bTerm_up3_r181 v _ _ _ p).trans hp
    rw [bTruth_mixedHarmonicPrefix_r210 (w x y z) true _ _ _ _ P y hP (hy x y z)]
    unfold mixedHarmonicPrefixValue
    rw [show bTerm (w x y z) (up3 a) = bTerm v a from bTerm_up3_r181 v _ _ _ a,
      show bTerm (w x y z) (up3 b) = bTerm v b from bTerm_up3_r181 v _ _ _ b]
  have hMul (x y z : ℕ) :
      bTruth (w x y z) (multiplication_f (up3 k) (up2 s) r) = crispTruth B (z=K*x) :=
    bTruth_multiplication_checked_r196 _ _ _ _ K x z ((bTerm_up3_r181 v _ _ _ k).trans hk)
      (hx x y z) (hz x y z)
  have hLE (x y z : ℕ) :
      bTruth (w x y z) (natLE_f r (up t)) = crispTruth B (z≤y) :=
    bTruth_natLE_checked_r192 _ _ _ z y (hz x y z) (hy x y z)
  simp only [harmonicBudget_f,bTruth_exOmega_r192,boolean_realize_bounded_formula_and]
  change (⨆ x : ℕ, ⨆ y : ℕ, ⨆ z : ℕ,
    bTruth (w x y z) (harmonicPrefixMass_f false (up3 a) (up3 b) (up3 p) (up2 s)) ⊓
    (bTruth (w x y z) (harmonicPrefixMass_f true (up3 a) (up3 b) (up3 p) (up t)) ⊓
      (bTruth (w x y z) (multiplication_f (up3 k) (up2 s) r) ⊓ bTruth (w x y z) (natLE_f r (up t))))) = _
  simp only [hNum,hDen,hMul,hLE,← inf_iSup_eq,iSup_crispEquality_select_r193,mixedHarmonicBudgetValue]

end SetLanguage
end JSP000933
