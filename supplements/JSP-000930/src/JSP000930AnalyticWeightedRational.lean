import JSP000933CheckedAddMulFactorial

open Lattice
open scoped Flypitch bSet

namespace JSP000930.BooleanAnalysis

open JSP000933.PositiveForcing JSP000933.BooleanNames

structure RatPresentation where
  pos : ℕ
  neg : ℕ
  den : ℕ
  den_pos : 0 < den
  deriving DecidableEq

def RatPresentation.value (q : RatPresentation) : ℚ :=
  ((q.pos : ℚ) - (q.neg : ℚ)) / (q.den : ℚ)

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def ratName (q : RatPresentation) : bSet B :=
  bSet.pair (bSet.of_nat q.pos)
    (bSet.pair (bSet.of_nat q.neg) (bSet.of_nat q.den))

theorem ratName_eq_crisp (q r : RatPresentation) :
    (ratName (B := B) q =ᴮ ratName r) = crispTruth B (q = r) := by
  by_cases h : q = r
  · subst r
    simp [crispTruth]
  · have hdiff : q.pos ≠ r.pos ∨ q.neg ≠ r.neg ∨ q.den ≠ r.den := by
      by_contra hnd
      push Not at hnd
      apply h
      cases q
      cases r
      simp_all
    rcases hdiff with hp | hm | hd
    · simp only [ratName, pair_eq_inf_r189, checkedNat_eq_crisp_r189, crispTruth, h, hp,
        ite_false, bot_inf_eq]
    · simp only [ratName, pair_eq_inf_r189, checkedNat_eq_crisp_r189, crispTruth, h, hm,
        ite_false, bot_inf_eq, inf_bot_eq]
    · simp only [ratName, pair_eq_inf_r189, checkedNat_eq_crisp_r189, crispTruth, h, hd,
        ite_false, inf_bot_eq]

def weightedRationalSet (β : RatPresentation → B) : bSet B :=
  familyName (ratName (B := B)) β

def ratUniverse : bSet B := weightedRationalSet (fun _ => ⊤)

theorem mem_weightedRationalSet (z : bSet B) (β : RatPresentation → B) :
    (z ∈ᴮ weightedRationalSet β) =
      ⨆ q : RatPresentation, β q ⊓ (z =ᴮ ratName q) := by
  unfold weightedRationalSet
  rw [mem_familyName_r70]

theorem ratUniverse_membership (z : bSet B) :
    (z ∈ᴮ (ratUniverse : bSet B)) = ⨆ q : RatPresentation, z =ᴮ ratName q := by
  simp only [ratUniverse, mem_weightedRationalSet, top_inf_eq]

theorem ratName_mem_weightedRationalSet (β : RatPresentation → B) (q : RatPresentation) :
    (ratName (B := B) q ∈ᴮ weightedRationalSet β) = β q := by
  rw [mem_weightedRationalSet]
  apply le_antisymm
  · apply iSup_le
    intro r
    by_cases h : q = r
    · subst r
      exact inf_le_left
    · simp [ratName_eq_crisp, crispTruth, h]
  · exact (by simpa using
      (le_iSup (fun r : RatPresentation => β r ⊓ (ratName q =ᴮ ratName r)) q))

noncomputable def extractRationalWeights (X : bSet B) (q : RatPresentation) : B :=
  ratName q ∈ᴮ X

theorem weightedRationalSet_recover (X : bSet B) (p : B)
    (hp : p ≤ X ⊆ᴮ (ratUniverse : bSet B)) :
    p ≤ X =ᴮ weightedRationalSet (extractRationalWeights X) := by
  exact familyName_represents_subset_r70 (ratName (B := B)) X p hp

theorem weightedRationalSet_subset (β γ : RatPresentation → B) :
    (weightedRationalSet β ⊆ᴮ weightedRationalSet γ) =
      ⨅ q : RatPresentation, imp (β q) (γ q) := by
  rw [bSet.subset_unfold]
  change (⨅ q : RatPresentation, imp (β q) (ratName q ∈ᴮ weightedRationalSet γ)) = _
  simp only [ratName_mem_weightedRationalSet]

theorem weightedRationalSet_eq (β γ : RatPresentation → B) :
    (weightedRationalSet β =ᴮ weightedRationalSet γ) =
      (⨅ q : RatPresentation, imp (β q) (γ q)) ⊓
      (⨅ q : RatPresentation, imp (γ q) (β q)) := by
  rw [bSet.eq_iff_subset_subset, weightedRationalSet_subset, weightedRationalSet_subset]

end JSP000930.BooleanAnalysis
