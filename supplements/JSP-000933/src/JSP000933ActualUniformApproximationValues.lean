import JSP000933ActualValidityContinuity

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem nameErrorBudget_mask_r313 (h : Bool) (k n : ℕ) {p : B} {a a' b b' : ℕ → B}
    (ha : p≤realEqValue a a') (hb : p≤realEqValue b b') :
    p⊓nameErrorBudget h k n a b=p⊓nameErrorBudget h k n a' b' := by
  have hX := realEqValue_bitsSymmDiff_mask_r251 ha hb
  unfold nameErrorBudget
  apply nameBudgetValue_mask_r226
  · intro i hi
    simpa only [membershipBits_realBitsName_r128] using (le_realEqValue_iff_r126 _ _ _).mp hX i
  · exact fun _ _ => rfl

theorem eventuallySmallError_mask_r313 (h : Bool) (k : ℕ) {p : B} {a a' b b' : ℕ → B}
    (ha : p≤realEqValue a a') (hb : p≤realEqValue b b') :
    p⊓eventuallySmallError h k a b=p⊓eventuallySmallError h k a' b' := by
  unfold eventuallySmallError eventualBudgetAt budgetTail
  apply mask_iSup_congr_r126
  intro N
  apply mask_iInf_congr_r126
  intro i
  exact mask_sup_congr_r211 rfl (nameErrorBudget_mask_r313 h k i ha hb)

noncomputable def uniformTailErrorValue (F : (ℕ → B) → ℕ → B) (c : ℕ → B)
    (k : ℕ) (f : (ℕ → B) → ℕ → B) : B :=
  ⨅ x : ℕ → B, eventuallySmallError true k (f x) (F (bitsMeet c x))

noncomputable def namedUniformWitnessValue (F : (ℕ → B) → ℕ → B) (c : ℕ → B)
    (k : ℕ) (a : ℕ → B) : B :=
  namedBitTableValid (decodedBitTable a)⊓uniformTailErrorValue F c k (namedTableOutput (decodedBitTable a))

noncomputable def existsNamedUniformValue (F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ) : B :=
  ⨆ a : ℕ → B, namedUniformWitnessValue F c k a

theorem namedUniformWitnessValue_ext_r313 (F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ) :
    RealTestExt (namedUniformWitnessValue F c k) := by
  intro p a b h
  unfold namedUniformWitnessValue uniformTailErrorValue
  exact mask_inf_congr_r126 (decodedBitTable_valid_ext_r311 p a b h)
    (mask_iInf_congr_r126 (fun x => eventuallySmallError_mask_r313 true k
      (decodedBitTable_output_mask_r311 h x) (le_top.trans_eq (realEqValue_refl_r127 _).symm)))

theorem nameUniformWitnessValue_cap_mask_r313 (F : (ℕ → B) → ℕ → B) (hF : NameMapExt F)
    {q : B} {c c' : ℕ → B} (hc : q≤realEqValue c c') (k : ℕ) (a : ℕ → B) :
    q⊓namedUniformWitnessValue F c k a=q⊓namedUniformWitnessValue F c' k a := by
  unfold namedUniformWitnessValue uniformTailErrorValue
  apply mask_inf_congr_r126 rfl
  apply mask_iInf_congr_r126
  intro x
  exact eventuallySmallError_mask_r313 true k (le_top.trans_eq (realEqValue_refl_r127 _).symm)
    (hF q _ _ (realEqValue_bitsMeet_mask_r251 hc (le_top.trans_eq (realEqValue_refl_r127 x).symm)))

theorem existsNamedUniformValue_elim_r313 (F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ) {p : B}
    (h : p≤existsNamedUniformValue F c k) :
    ∃ f : (ℕ → B) → ℕ → B, NamedContinuousOn p f ∧ p≤uniformTailErrorValue F c k f := by
  obtain ⟨a,ha⟩ := exists_realName_maximum_r138 (namedUniformWitnessValue F c k)
    (namedUniformWitnessValue_ext_r313 F c k) p h
  exact ⟨namedTableOutput (decodedBitTable a),
    namedBitTable_continuous_r312 _ (ha.trans inf_le_left),ha.trans inf_le_right⟩

theorem existsNamedUniformValue_intro_r313 (F : (ℕ → B) → ℕ → B) (c : ℕ → B) (k : ℕ)
    {p : B} {f : (ℕ → B) → ℕ → B} (hC : NamedContinuousOn p f) (hU : p≤uniformTailErrorValue F c k f) :
    p≤existsNamedUniformValue F c k := by
  unfold existsNamedUniformValue
  apply le_iSup_of_le (encodedBitTable (actualFunctionBitTable f))
  unfold namedUniformWitnessValue
  rw [decoded_encodedBitTable_r311]
  apply le_inf hC.actualBitTable_valid_r311
  unfold uniformTailErrorValue
  apply le_iInf
  intro x
  have hx : p≤eventuallySmallError true k (f x) (F (bitsMeet c x)) := hU.trans (iInf_le _ x)
  have hM := eventuallySmallError_mask_r313 true k (hC.actualBitTable_mask_r311 x)
    (le_top.trans_eq (realEqValue_refl_r127 (F (bitsMeet c x))).symm)
  exact ((le_inf le_rfl hx).trans_eq hM.symm).trans inf_le_right

end SetLanguage
end JSP000933
