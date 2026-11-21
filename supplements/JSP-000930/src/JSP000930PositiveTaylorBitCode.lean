import JSP000930PositiveFamilyEvaluationKernel
import JSP000930AnalyticWeightedRational
import Mathlib.Data.Countable.Basic

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000933.BooleanNames JSP000933.CantorCodes
  JSP000930.BooleanAnalysis

abbrev TaylorSlot := ℕ × (Bool × RatPresentation)

instance : Countable RatPresentation := by
  let e : RatPresentation → ℕ × (ℕ × ℕ) := fun r => (r.pos,r.neg,r.den)
  have he : Function.Injective e := by
    intro q r h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg (fun x : ℕ × (ℕ × ℕ) => x.2.1) h
    have h₃ := congrArg (fun x : ℕ × (ℕ × ℕ) => x.2.2) h
    cases q
    cases r
    simp only [e] at h₁ h₂ h₃
    subst_vars
    rfl
  exact he.countable

noncomputable def taylorSlotEncodable : Encodable TaylorSlot :=
  Encodable.ofCountable TaylorSlot

noncomputable def encodeTaylorBits {B : Type} [Bot B] (V : TaylorSlot → B) : ℕ → B :=
  letI := taylorSlotEncodable
  fun n => (Encodable.decode (α := TaylorSlot) n).elim ⊥ V

noncomputable def decodeTaylorBits {B : Type} (x : ℕ → B) : TaylorSlot → B :=
  letI := taylorSlotEncodable
  fun s => x (Encodable.encode s)

theorem decode_encode_taylorBits {B : Type} [Bot B] (V : TaylorSlot → B) :
    decodeTaylorBits (encodeTaylorBits V) = V := by
  letI := taylorSlotEncodable
  funext s
  change (Encodable.decode (α := TaylorSlot) (Encodable.encode s)).elim ⊥ V = V s
  rw [Encodable.encodek] <;> rfl

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def coefficientName (V : TaylorSlot → B) (n : ℕ) : bSet B :=
  pair (weightedRationalSet (fun r => V (n,false,r)))
    (weightedRationalSet (fun r => V (n,true,r)))

def taylorCodeName (V : TaylorSlot → B) : bSet B :=
  functionalGraphName bSet.of_nat (coefficientName V)

theorem weightedCut_eq_of_mask {U V : RatPresentation → B} {p : B}
    (h : ∀ q,p ⊓ U q = p ⊓ V q) :
    p ≤ weightedRationalSet U =ᴮ weightedRationalSet V := by
  apply (le_inf ?_ ?_).trans (eq_of_subset_subset _ _)
  · rw [subset_unfold]
    change p ≤ ⨅ q : RatPresentation, imp (U q)
      (ratName q ∈ᴮ weightedRationalSet V)
    apply le_iInf
    intro q
    rw [← _root_.deduction,ratName_mem_weightedRationalSet,h q]
    exact inf_le_right
  · rw [subset_unfold]
    change p ≤ ⨅ q : RatPresentation, imp (V q)
      (ratName q ∈ᴮ weightedRationalSet U)
    apply le_iInf
    intro q
    rw [← _root_.deduction,ratName_mem_weightedRationalSet,← h q]
    exact inf_le_right

theorem taylorCodeName_eq_of_mask {U V : TaylorSlot → B} {p : B}
    (h : ∀ s,p ⊓ U s = p ⊓ V s) :
    p ≤ taylorCodeName U =ᴮ taylorCodeName V := by
  have hC (n : ℕ) : p ≤ coefficientName U n =ᴮ coefficientName V n :=
    pair_congr (weightedCut_eq_of_mask (fun q => h (n,false,q)))
      (weightedCut_eq_of_mask (fun q => h (n,true,q)))
  apply (le_inf ?_ ?_).trans (eq_of_subset_subset _ _)
  · rw [subset_unfold]
    change p ≤ ⨅ n : ℕ, imp (⊤ : B)
      (pair (bSet.of_nat n) (coefficientName U n) ∈ᴮ taylorCodeName V)
    apply le_iInf
    intro n
    rw [← _root_.deduction,inf_top_eq]
    exact subst_congr_mem_left' (pair_congr bv_refl (bv_symm (hC n)))
      (le_top.trans (pair_mem_functionalGraph_self_r102 bSet.of_nat (coefficientName V) n))
  · rw [subset_unfold]
    change p ≤ ⨅ n : ℕ, imp (⊤ : B)
      (pair (bSet.of_nat n) (coefficientName V n) ∈ᴮ taylorCodeName U)
    apply le_iInf
    intro n
    rw [← _root_.deduction,inf_top_eq]
    exact subst_congr_mem_left' (pair_congr bv_refl (hC n))
      (le_top.trans (pair_mem_functionalGraph_self_r102 bSet.of_nat (coefficientName U) n))

theorem taylorCode_decoded_eq_of_realEq {x y : ℕ → B} {p : B}
    (h : p ≤ realEqValue x y) :
    p ≤ taylorCodeName (decodeTaylorBits x) =ᴮ taylorCodeName (decodeTaylorBits y) := by
  letI := taylorSlotEncodable
  apply taylorCodeName_eq_of_mask
  intro s
  exact (le_realEqValue_iff_r126 p x y).mp h (Encodable.encode s)

end JSP000930.Positive
