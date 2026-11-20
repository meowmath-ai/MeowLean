import JSP000933NamedIsoSelection

open Fol Lattice
open scoped Flypitch

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def groundFourEnv (a b : Set ℕ) (k n : ℕ) : DVec (V B) 4 :=
  DVec.cons (bSet.of_nat n) (DVec.cons (bSet.of_nat k)
    (DVec.cons (groundSubsetName B b) (DVec.cons (groundSubsetName B a) DVec.nil)))

def GroundBudgetHolds (h : Bool) (a b : Set ℕ) (k n : ℕ) : Prop :=
  if h then k * groundScaledHarmonic false a b n n ≤ groundScaledHarmonic true a b n n
  else k * groundCount a b n ≤ n

noncomputable def nameBudgetValue (h : Bool) (A C : bSet B) (k n : ℕ) : B :=
  if h then mixedHarmonicBudgetValue A C k n else mixedOrdinaryBudgetValue A C k n

theorem nameBudgetValue_ground_r226 (h : Bool) (a b : Set ℕ) (k n : ℕ) :
    nameBudgetValue h (groundSubsetName B a) (groundSubsetName B b) k n =
      crispTruth B (GroundBudgetHolds h a b k n) := by
  let v : DVec (V B) 4 := groundFourEnv a b k n
  let at' := up3 (x0 0)
  let bt := up2 (x0 1)
  let kt := up (x0 2)
  let nt := x0 3
  have ha : bTerm v at' = groundSubsetName B a := by
    rfl
  have hb : bTerm v bt = groundSubsetName B b := by
    rfl
  have hk : bTerm v kt = bSet.of_nat k := by
    rfl
  have hn : bTerm v nt = bSet.of_nat n := by
    rfl
  cases h
  · have hh := bTruth_mixedOrdinaryBudget_r212 v at' bt kt nt k n hk hn
    rw [ha,hb] at hh
    exact hh.symm.trans (bTruth_ordinaryBudget_checked_r200 v at' bt kt nt a b k n ha hb hk hn)
  · have hh := bTruth_mixedHarmonicBudget_r212 v at' bt kt nt k n hk hn
    rw [ha,hb] at hh
    exact hh.symm.trans (bTruth_harmonicBudget_checked_r200 v at' bt kt nt a b k n ha hb hk hn)

theorem nameBudgetValue_mask_r226 {q : B} {A A' C C' : bSet B} {n : ℕ}
    (hA : ∀ i < n, q ⊓ membershipBits A i = q ⊓ membershipBits A' i)
    (hC : ∀ i < n, q ⊓ membershipBits C i = q ⊓ membershipBits C' i)
    (h : Bool) (k : ℕ) :
    q ⊓ nameBudgetValue h A C k n = q ⊓ nameBudgetValue h A' C' k n := by
  obtain ⟨hO,hH⟩ := mixed_prefix_values_mask_r211 hA hC
  cases h
  · change q ⊓ mixedOrdinaryBudgetValue A C k n = q ⊓ mixedOrdinaryBudgetValue A' C' k n
    unfold mixedOrdinaryBudgetValue
    apply mask_iSup_congr_r126
    intro r
    exact mask_inf_congr_r126 (hO r) rfl
  · change q ⊓ mixedHarmonicBudgetValue A C k n = q ⊓ mixedHarmonicBudgetValue A' C' k n
    unfold mixedHarmonicBudgetValue
    apply mask_iSup_congr_r126
    intro r
    apply mask_iSup_congr_r126
    intro s
    exact mask_inf_congr_r126 (hH false r) (mask_inf_congr_r126 (hH true s) rfl)

theorem nameBudgetValue_locallyCrisp_r226 {q : B} {A C : bSet B} {a b : Set ℕ} {n : ℕ}
    (hA : ∀ i < n, q ⊓ membershipBits A i = q ⊓ membershipBits (groundSubsetName B a) i)
    (hC : ∀ i < n, q ⊓ membershipBits C i = q ⊓ membershipBits (groundSubsetName B b) i)
    (h : Bool) (k : ℕ) :
    q ⊓ nameBudgetValue h A C k n = q ⊓ crispTruth B (GroundBudgetHolds h a b k n) := by
  rw [nameBudgetValue_mask_r226 hA hC h k,nameBudgetValue_ground_r226]

end SetLanguage
end JSP000933
