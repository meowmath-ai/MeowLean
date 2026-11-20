import JSP000933BooleanAntichain
import JSP000933BooleanNamedCliqueStage

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open BooleanTwoStep OpenGraphForcing

universe u
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
variable {carrier ord : bSet B}
variable {hrefl : ∀ q : bSet B, (q ∈ᴮ carrier) ≤ bSet.pair q q ∈ᴮ ord}
variable {htrans : ∀ q r s : bSet B, (bSet.pair q r ∈ᴮ ord) ⊓ (bSet.pair r s ∈ᴮ ord)
  ≤ bSet.pair q s ∈ᴮ ord}

local notation "S" => bSetStage carrier ord hrefl htrans

noncomputable def maskedAntichainEnum_r80 (a : OmegaOneIndex → bSet B) (g : OmegaOneIndex → B)
    (ha : ∀ i, g i ≤ (S).admitted (a i))
    (hanti : ∀ i j, i ≠ j → Disjoint (g i ⊓ g j) ((S).compVal (a i) (a j)))
    (p : B) (f : bSet B) (hf : p ≤ bSet.is_func f) : EnumerationMatrix OmegaOneIndex B := by
  refine ⟨fun n i => (p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f),?_⟩
  intro n i j hij
  apply disjoint_iff_inf_le.mpr
  let c := ((p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f)) ⊓
    ((p ⊓ g j) ⊓ (bSet.pair (bSet.of_nat n) (a j) ∈ᴮ f))
  have hEq : c ≤ a i =ᴮ a j := bSet.eq_of_is_func_of_eq
    (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hf)))
    bSet.bv_refl (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hG : c ≤ g i ⊓ g j := le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
  have hComp : c ≤ (S).compVal (a i) (a j) :=
    compVal_of_admitted_eq_r79 (hrefl := hrefl) (htrans := htrans)
      (hG.trans (inf_le_left.trans (ha i))) hEq
  exact (le_inf hG hComp).trans (disjoint_iff_inf_le.mp (hanti i j hij))

theorem hasOmegaEnumeration_indexedAntichain_le_r80 (a : OmegaOneIndex → bSet B)
    (g : OmegaOneIndex → B) (ha : ∀ i, g i ≤ (S).admitted (a i))
    (hanti : ∀ i j, i ≠ j → Disjoint (g i ⊓ g j) ((S).compVal (a i) (a j))) :
    hasOmegaEnumeration (indexedFamilyName a g) ≤ countableCoverageValue g := by
  apply iSup_le
  intro f
  let p := bSet.is_func f ⊓ bSet.is_surj bSet.omega (indexedFamilyName a g) f
  let e := maskedAntichainEnum_r80 a g ha hanti p f inf_le_left
  refine (show p ≤ matrixCoverage g e from ?_).trans
    (le_iSup (fun e : EnumerationMatrix OmegaOneIndex B => matrixCoverage g e) e)
  apply le_iInf
  intro i
  change p ≤ imp (g i) (⨆ n : ℕ, (p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f))
  rw [← _root_.deduction]
  let c := p ⊓ g i
  have haMem : g i ≤ a i ∈ᴮ indexedFamilyName a g := by
    rw [mem_indexedFamilyName_r79]
    exact le_iSup_of_le i (by rw [bSet.bv_eq_refl,inf_top_eq])
  have hSurj : c ≤ imp (a i ∈ᴮ indexedFamilyName a g)
      (⨆ w : bSet B, (w ∈ᴮ bSet.omega) ⊓ (bSet.pair w (a i) ∈ᴮ f)) :=
    inf_le_left.trans (inf_le_right.trans (iInf_le _ (a i)))
  have hVal := (_root_.context_imp_elim hSurj (inf_le_right.trans haMem)).trans_eq
    (omega_exists_pair_eq_r71 (a i) f)
  apply (le_inf le_rfl hVal).trans
  apply Lattice.bv_cases_right
  intro n
  exact le_iSup (fun n : ℕ => c ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f)) n

def InternalCCC (carrier : bSet B) (D : Stage B (bSet B)) : Prop :=
  ∀ w : bSet B, (w ⊆ᴮ carrier) ⊓ antichainValue D w ≤ hasOmegaEnumeration w

theorem booleanAntichainCCC_of_internalCCC_r80 (h : InternalCCC carrier S) :
    (S).BooleanAntichainCCC := by
  intro a g ha hn
  let w := indexedFamilyName a g
  have hTop : (w ⊆ᴮ carrier) ⊓ antichainValue S w = ⊤ := by
    rw [indexedFamilyName_subset_r79 (hrefl := hrefl) (htrans := htrans) a g ha,
      indexedFamilyName_antichain_r79 a g hn,top_inf_eq]
  exact top_unique ((hTop.symm.le.trans (h w)).trans (hasOmegaEnumeration_indexedAntichain_le_r80 a g ha hn))

theorem countableAntichains_bSet_twoStep_r80 (hB : BooleanCCC B) (h : InternalCCC carrier S) :
    HasCountableAntichains (Condition S) :=
  countableAntichains_twoStep_r78 hB (booleanAntichainCCC_of_internalCCC_r80 h)

end BooleanNames
end JSP000933
