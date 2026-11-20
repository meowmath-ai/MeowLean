import JSP000933MixedPrefixValues
import JSP000933FiniteWordNames
import JSP000933FiniteOpenRectangleWitnesses

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem mask_sup_congr_r211 {p x y z w : B}
    (h₁ : p ⊓ x = p ⊓ y) (h₂ : p ⊓ z = p ⊓ w) :
    p ⊓ (x ⊔ z) = p ⊓ (y ⊔ w) := by
  rw [inf_sup_left,inf_sup_left,h₁,h₂]

theorem mask_imp_ante_congr_r211 {p x y z : B} (h : p ⊓ x = p ⊓ y) :
    p ⊓ imp x z = p ⊓ imp y z :=
  mask_sup_congr_r211 (mask_compl_congr_r126 h) rfl

theorem mixedOrdinaryStep_mask_r211 {p : B} {A A' C C' : bSet B} {i : ℕ}
    (hA : p ⊓ membershipBits A i = p ⊓ membershipBits A' i)
    (hC : p ⊓ membershipBits C i = p ⊓ membershipBits C' i) (y z : ℕ) :
    p ⊓ mixedOrdinaryStep A C i y z = p ⊓ mixedOrdinaryStep A' C' i y z := by
  have h : p ⊓ mixedDiffBit A C i = p ⊓ mixedDiffBit A' C' i :=
    mask_inf_congr_r126 hA (mask_compl_congr_r126 hC)
  exact mask_inf_congr_r126 (mask_imp_ante_congr_r211 h)
    (mask_imp_ante_congr_r211 (mask_compl_congr_r126 h))

theorem mixedHarmonicStep_mask_r211 {p : B} {A A' C C' : bSet B} {i : ℕ}
    (hA : p ⊓ membershipBits A i = p ⊓ membershipBits A' i)
    (hC : p ⊓ membershipBits C i = p ⊓ membershipBits C' i) (b : Bool) (F y z : ℕ) :
    p ⊓ mixedHarmonicStep b A C F i y z = p ⊓ mixedHarmonicStep b A' C' F i y z := by
  have h : p ⊓ mixedHarmonicBit b A C i = p ⊓ mixedHarmonicBit b A' C' i := by
    cases b
    · exact mask_inf_congr_r126 hA (mask_compl_congr_r126 hC)
    · rfl
  exact mask_inf_congr_r126 (mask_imp_ante_congr_r211 h)
    (mask_imp_ante_congr_r211 (mask_compl_congr_r126 h))

def subsetFromWord (w : Word) : Set ℕ := {i | wordBit w i = true}

theorem cylinder_fixes_ground_membership_r211 (A : bSet B) (w : Word) {q : B}
    (h : q ≤ cylinderValue (membershipBits A) w) :
    ∀ i < w.length, q ⊓ membershipBits A i =
      q ⊓ membershipBits (groundSubsetName B (subsetFromWord w)) i := by
  intro i hi
  apply (le_bitEq_iff_r126 q _ _).mp
  change q ≤ bitEq (membershipBits A i) ((bSet.of_nat i : bSet B) ∈ᴮ groundSubsetName B (subsetFromWord w))
  rw [checkedNat_ground_mem_r197]
  have he : crispTruth B (i ∈ subsetFromWord w) = truthBit (w[i]'hi) := by
    classical
    cases hw : w[i]'hi <;> simp [subsetFromWord,wordBit,hi,hw,crispTruth,truthBit]
  rw [he,bitEq_truthBit_r175]
  exact h.trans (iInf_le _ (⟨i,hi⟩ : Fin w.length))

theorem exists_joint_ground_prefix_r211 (A C : bSet B) (n : ℕ) (p : B) (hp : p ≠ ⊥) :
    ∃ a c : Set ℕ, ∃ q : B, q ≠ ⊥ ∧ q ≤ p ∧
      (∀ i < n, q ⊓ membershipBits A i = q ⊓ membershipBits (groundSubsetName B a) i) ∧
      (∀ i < n, q ⊓ membershipBits C i = q ⊓ membershipBits (groundSubsetName B c) i) := by
  obtain ⟨u,hu,q,hq,hqp,hA⟩ := exists_decided_initialWord_r136 (membershipBits A) n p hp
  obtain ⟨v,hv,r,hr,hrq,hC⟩ := exists_decided_initialWord_r136 (membershipBits C) n q hq
  refine ⟨subsetFromWord u,subsetFromWord v,r,hr,hrq.trans hqp,?_,?_⟩
  · exact fun i hi => cylinder_fixes_ground_membership_r211 A u (hrq.trans hA) i (hu.symm ▸ hi)
  · exact fun i hi => cylinder_fixes_ground_membership_r211 C v hC i (hv.symm ▸ hi)

theorem mixed_prefix_values_mask_r211 {p : B} {A A' C C' : bSet B} {n : ℕ}
    (hA : ∀ i < n, p ⊓ membershipBits A i = p ⊓ membershipBits A' i)
    (hC : ∀ i < n, p ⊓ membershipBits C i = p ⊓ membershipBits C' i) :
    (∀ r, p ⊓ recurrenceOfTables B n 0 r (mixedOrdinaryStep A C) =
      p ⊓ recurrenceOfTables B n 0 r (mixedOrdinaryStep A' C')) ∧
    (∀ b r, p ⊓ recurrenceOfTables B n 0 r (mixedHarmonicStep b A C (Nat.factorial n)) =
      p ⊓ recurrenceOfTables B n 0 r (mixedHarmonicStep b A' C' (Nat.factorial n))) := by
  constructor
  · intro r
    exact recurrenceOfTables_maskCongr_r208 n 0 r
      (fun i hi y z => mixedOrdinaryStep_mask_r211 (hA i hi) (hC i hi) y z)
  · intro b r
    exact recurrenceOfTables_maskCongr_r208 n 0 r
      (fun i hi y z => mixedHarmonicStep_mask_r211 (hA i hi) (hC i hi) b _ y z)

end SetLanguage
end JSP000933
