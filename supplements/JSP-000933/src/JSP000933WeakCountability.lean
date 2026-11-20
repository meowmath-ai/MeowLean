import JSP000933MaskedCliqueName
import JSP000933MaskNativeClique
import JSP000933CodedNamedClique

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open OpenGraphForcing CantorCodes FiniteSupport

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def weakUniqueValue (C f : bSet B) : B :=
  ⨅ n : bSet B, ⨅ y : bSet B, ⨅ z : bSet B,
    imp ((n ∈ᴮ bSet.omega) ⊓ ((y ∈ᴮ C) ⊓ ((z ∈ᴮ C) ⊓
      ((bSet.pair n y ∈ᴮ f) ⊓ (bSet.pair n z ∈ᴮ f))))) (y =ᴮ z)

noncomputable def weakCountabilityValue (C : bSet B) : B :=
  ⨆ f : bSet B, weakUniqueValue C f ⊓ bSet.is_surj bSet.omega C f

theorem restricted_unique_r172 (C f : bSet B) {p : B} (n y z : bSet B)
    (hu : p ≤ weakUniqueValue C f) (hn : p ≤ n ∈ᴮ bSet.omega)
    (hy : p ≤ y ∈ᴮ C) (hz : p ≤ z ∈ᴮ C)
    (hny : p ≤ bSet.pair n y ∈ᴮ f) (hnz : p ≤ bSet.pair n z ∈ᴮ f) :
    p ≤ y =ᴮ z := by
  have h : p ≤ imp ((n ∈ᴮ bSet.omega) ⊓ ((y ∈ᴮ C) ⊓ ((z ∈ᴮ C) ⊓
      ((bSet.pair n y ∈ᴮ f) ⊓ (bSet.pair n z ∈ᴮ f))))) (y =ᴮ z) :=
    hu.trans ((iInf_le _ n).trans ((iInf_le _ y).trans (iInf_le _ z)))
  exact _root_.context_imp_elim h (le_inf hn (le_inf hy (le_inf hz (le_inf hny hnz))))

noncomputable def weakEnumerationMatrix (a : I → bSet B) (g : I → B)
    (sep : ∀ i j, i ≠ j → Disjoint (g i ⊓ g j) (a i =ᴮ a j))
    (p : B) (f : bSet B) (hf : p ≤ weakUniqueValue (familyName a g) f) :
    EnumerationMatrix I B := by
  refine ⟨fun n i => (p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f),?_⟩
  intro n i j hij
  apply disjoint_iff_inf_le.mpr
  let c := ((p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f)) ⊓
    ((p ⊓ g j) ⊓ (bSet.pair (bSet.of_nat n) (a j) ∈ᴮ f))
  have hi : c ≤ g i := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have hj : c ≤ g j := inf_le_right.trans (inf_le_left.trans inf_le_right)
  have heq : c ≤ a i =ᴮ a j := restricted_unique_r172 _ _ (bSet.of_nat n) (a i) (a j)
    (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hf))) bSet.omega_definite
    (hi.trans (bSet.mem_mk a g i)) (hj.trans (bSet.mem_mk a g j))
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  exact (le_inf (le_inf hi hj) heq).trans (disjoint_iff_inf_le.mp (sep i j hij))

theorem locallyDistinct_weakCountability_le_r172 (a : I → bSet B) (g : I → B)
    (sep : ∀ i j, i ≠ j → Disjoint (g i ⊓ g j) (a i =ᴮ a j)) :
    weakCountabilityValue (familyName a g) ≤ countableCoverageValue g := by
  unfold weakCountabilityValue
  apply iSup_le
  intro f
  let p := weakUniqueValue (familyName a g) f ⊓ bSet.is_surj bSet.omega (familyName a g) f
  let e := weakEnumerationMatrix a g sep p f inf_le_left
  refine (show p ≤ matrixCoverage g e from ?_).trans
    (le_iSup (fun e : EnumerationMatrix I B => matrixCoverage g e) e)
  apply le_iInf
  intro i
  change p ≤ imp (g i) (⨆ n : ℕ, (p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f))
  rw [← _root_.deduction]
  let c := p ⊓ g i
  have ha : g i ≤ a i ∈ᴮ familyName a g := bSet.mem_mk a g i
  have hS : c ≤ imp (a i ∈ᴮ familyName a g)
    (⨆ w : bSet B, (w ∈ᴮ bSet.omega) ⊓ (bSet.pair w (a i) ∈ᴮ f)) :=
    inf_le_left.trans (inf_le_right.trans (iInf_le _ (a i)))
  have hv := (_root_.context_imp_elim hS (inf_le_right.trans ha)).trans_eq
    (omega_exists_pair_eq_r71 (a i) f)
  apply (le_inf le_rfl hv).trans
  apply Lattice.bv_cases_right
  intro n
  exact le_iSup (fun n : ℕ => c ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f)) n

theorem realize_weightedClique_r172 (X : bSet B) (K : Word × Word → B)
    (x : OmegaOneIndex → ℕ → B) (g : OmegaOneIndex → B) (p : B)
    (h : p ≤ weightedCliqueValue (fun r => realBitsName r ∈ᴮ X) K x g) :
    ∃ C : bSet B, (⊤ : B) ≤ C ⊆ᴮ X ∧
      namedOpenClique K C = ⊤ ∧ p ≤ (weakCountabilityValue C)ᶜ := by
  obtain ⟨hX,hEdge,hUnc⟩ :=
    weightedClique_masked_r171 (fun r => realBitsName r ∈ᴮ X) K x g p h
  let a (i : OmegaOneIndex) := realBitsName (x i)
  let w (i : OmegaOneIndex) := p ⊓ g i
  refine ⟨familyName a w, familyName_subset_of_memberships_r129 a w X hX,
    familyName_namedOpenClique_r129 K x w (fun i j hij => (hEdge i j hij).trans inf_le_left),
    hUnc.trans (compl_le_compl ?_)⟩
  apply locallyDistinct_weakCountability_le_r172
  intro i j hij
  apply le_compl_iff_disjoint_right.mp
  change w i ⊓ w j ≤ (realBitsName (x i) =ᴮ realBitsName (x j))ᶜ
  rw [realBitsName_eq_r128]
  exact (hEdge i j hij).trans inf_le_right

end BooleanNames
end JSP000933
