import JSP000933BooleanNames
import JSP000933BooleanUncountability

open scoped Flypitch bSet
open Lattice

namespace JSP000933
namespace BooleanNames

open OpenGraphForcing

universe u
variable {B : Type u} [NontrivialCompleteBooleanAlgebra B]
variable {I : Type u}

theorem omega_exists_pair_eq_r71 (x f : bSet B) :
    (⨆ w : bSet B, (w ∈ᴮ (bSet.omega : bSet B)) ⊓ (bSet.pair w x ∈ᴮ f)) =
      ⨆ n : ℕ, bSet.pair (bSet.of_nat n) x ∈ᴮ f := by
  calc
    _ = ⨆ k : ULift.{u} ℕ, bSet.pair (bSet.of_nat k.down) x ∈ᴮ f := by
      rw [← @bSet.bounded_exists B _ (bSet.omega : bSet B)
        (fun w => bSet.pair w x ∈ᴮ f) (h_congr := bSet.B_ext_pair_mem_left)]
      change (⨆ k : ULift.{u} ℕ, ⊤ ⊓ (bSet.pair (bSet.of_nat k.down) x ∈ᴮ f)) = _
      simp only [top_inf_eq]
    _ = _ := le_antisymm
      (iSup_le (fun k => le_iSup (fun n => bSet.pair (bSet.of_nat n) x ∈ᴮ f) k.down))
      (iSup_le (fun n => le_iSup
        (fun k : ULift.{u} ℕ => bSet.pair (bSet.of_nat k.down) x ∈ᴮ f) ⟨n⟩))

noncomputable def enumFromName (a : I → bSet B)
    (ha : ∀ i j, i ≠ j → (a i =ᴮ a j) = ⊥)
    (p : B) (f : bSet B) (hf : p ≤ bSet.is_func f) : EnumerationMatrix I B := by
  refine ⟨fun n i => p ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f),?_⟩
  intro n i j hij
  apply disjoint_iff_inf_le.mpr
  let c := (p ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f)) ⊓
    (p ⊓ (bSet.pair (bSet.of_nat n) (a j) ∈ᴮ f))
  have hEq : c ≤ a i =ᴮ a j := bSet.eq_of_is_func_of_eq
    (inf_le_left.trans (inf_le_left.trans hf)) bSet.bv_refl
    (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  exact hEq.trans_eq (ha i j hij)

theorem partialEnumeration_le_countableCoverage_r71 (a : I → bSet B)
    (ha : ∀ i j, i ≠ j → (a i =ᴮ a j) = ⊥) (g : I → B) (f : bSet B) :
    bSet.is_func f ⊓ bSet.is_surj bSet.omega (familyName a g) f ≤ countableCoverageValue g := by
  let p := bSet.is_func f ⊓ bSet.is_surj bSet.omega (familyName a g) f
  let e := enumFromName a ha p f inf_le_left
  refine (show p ≤ matrixCoverage g e from ?_).trans
    (le_iSup (fun e : EnumerationMatrix I B => matrixCoverage g e) e)
  apply le_iInf
  intro i
  change p ≤ (g i)ᶜ ⊔ (⨆ n, p ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f))
  change p ≤ imp (g i) _
  rw [← _root_.deduction]
  let c := p ⊓ g i
  have hd : c ≤ a i ∈ᴮ familyName a g :=
    inf_le_right.trans_eq (mem_familyName_self_r70 a ha g i).symm
  have hs : c ≤ imp (a i ∈ᴮ familyName a g)
      (⨆ w : bSet B, (w ∈ᴮ (bSet.omega : bSet B)) ⊓ (bSet.pair w (a i) ∈ᴮ f)) :=
    inf_le_left.trans (inf_le_right.trans (iInf_le _ (a i)))
  have hh := (_root_.context_imp_elim hs hd).trans_eq (omega_exists_pair_eq_r71 (a i) f)
  have he : c ≤ p ⊓ (⨆ n : ℕ, bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f) :=
    le_inf inf_le_left hh
  apply he.trans
  apply Lattice.bv_cases_right
  intro n
  exact le_iSup (fun n : ℕ => p ⊓ (bSet.pair (bSet.of_nat n) (a i) ∈ᴮ f)) n

theorem bSet_countableValue_le_matrixValue_r71 (a : I → bSet B)
    (ha : ∀ i j, i ≠ j → (a i =ᴮ a j) = ⊥) (g : I → B) :
    (⨆ f : bSet B, bSet.is_func f ⊓ bSet.is_surj bSet.omega (familyName a g) f) ≤
      countableCoverageValue g :=
  iSup_le (partialEnumeration_le_countableCoverage_r71 a ha g)

end BooleanNames
end JSP000933
