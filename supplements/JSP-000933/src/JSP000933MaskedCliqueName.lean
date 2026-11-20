import JSP000933SuccessorCliqueBelowMark
import JSP000933InternalRealEnumeration

open scoped Flypitch
open Lattice

open scoped bSet

namespace JSP000933
namespace BooleanNames

open OpenGraphForcing

variable {B I : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def enumerationFromLocallyDistinct (a : I → bSet B) (g : I → B)
    (sep : ∀ i j, i ≠ j → Disjoint (g i ⊓ g j) (a i =ᴮ a j))
    (p : B) (f : bSet B) (hf : p ≤ bSet.is_func f) : EnumerationMatrix I B := by
  refine ⟨fun n i => (p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f),?_⟩
  intro n i j hij
  apply disjoint_iff_inf_le.mpr
  let c := ((p ⊓ g i) ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f)) ⊓
    ((p ⊓ g j) ⊓ (bSet.pair (bSet.of_nat n) (a j) ∈ᴮ f))
  have heq : c ≤ a i =ᴮ a j := bSet.eq_of_is_func_of_eq
    (inf_le_left.trans (inf_le_left.trans (inf_le_left.trans hf)))
    bSet.bv_refl (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have hG : c ≤ g i ⊓ g j := le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
    (inf_le_right.trans (inf_le_left.trans inf_le_right))
  exact (le_inf hG heq).trans (disjoint_iff_inf_le.mp (sep i j hij))

theorem locDistinctName_countability_le_r125 (a : I → bSet B) (g : I → B)
    (sep : ∀ i j, i ≠ j → Disjoint (g i ⊓ g j) (a i =ᴮ a j)) :
    hasOmegaEnumeration (familyName a g) ≤ countableCoverageValue g := by
  unfold hasOmegaEnumeration
  apply iSup_le
  intro f
  let p := bSet.is_func f ⊓ bSet.is_surj bSet.omega (familyName a g) f
  let e := enumerationFromLocallyDistinct a g sep p f inf_le_left
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

theorem locDistinctName_forced_uncountable_r125 (a : I → bSet B) (g : I → B) (mark : B)
    (activated : ∀ i, g i ≤ mark)
    (sep : ∀ i j, i ≠ j → Disjoint mark (a i =ᴮ a j))
    {p : B} (hp : p ≤ (countableCoverageValue g)ᶜ) :
    p ≤ (hasOmegaEnumeration (familyName a g))ᶜ := by
  apply hp.trans
  apply compl_le_compl
  apply locDistinctName_countability_le_r125 a g
  intro i j hne
  apply disjoint_iff_inf_le.mpr
  have h : g i ⊓ g j ≤ mark := inf_le_left.trans (activated i)
  exact (inf_le_inf_right (a i =ᴮ a j) h).trans (disjoint_iff_inf_le.mp (sep i j hne))

end BooleanNames
end JSP000933
