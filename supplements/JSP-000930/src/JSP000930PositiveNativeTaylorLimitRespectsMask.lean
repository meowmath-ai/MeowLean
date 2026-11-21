import JSP000930PositiveActualFreshRowSeparatesEarlierNativeTaylor

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def sameMaskedComplex (p : B) (x y : ComplexBits B) : Prop :=
  (∀ q,p ⊓ x.re q = p ⊓ y.re q) ∧ (∀ q,p ⊓ x.im q = p ⊓ y.im q)

theorem sameMaskedComplex_self (p : B) (x : ComplexBits B) :
    sameMaskedComplex p x x := ⟨fun _ => rfl,fun _ => rfl⟩

theorem sameMaskedComplex_add {p : B} {a a' b b' : ComplexBits B}
    (h₁ : sameMaskedComplex p a a') (h₂ : sameMaskedComplex p b b') :
    sameMaskedComplex p (a.add b) (a'.add b') :=
  ⟨masked_addCutBits_congr h₁.1 h₂.1,masked_addCutBits_congr h₁.2 h₂.2⟩

theorem masked_negCutBits_congr {p : B} {u v : RatPresentation → B}
    (h : ∀ q,p ⊓ u q = p ⊓ v q) (q : RatPresentation) :
    p ⊓ negCutBits u q = p ⊓ negCutBits v q := by
  unfold negCutBits
  exact masked_iSup_congr fun r => masked_iSup_congr fun _ => compl_eq_under_same_mask (h r)

theorem sameMaskedComplex_mul {p : B} {a a' b b' : ComplexBits B}
    (h₁ : sameMaskedComplex p a a') (h₂ : sameMaskedComplex p b b') :
    sameMaskedComplex p (a.mul b) (a'.mul b') :=
  ⟨masked_addCutBits_congr (masked_mulCutBits_congr h₁.1 h₂.1)
    (masked_negCutBits_congr (masked_mulCutBits_congr h₁.2 h₂.2)),
    masked_addCutBits_congr (masked_mulCutBits_congr h₁.1 h₂.2)
      (masked_mulCutBits_congr h₁.2 h₂.1)⟩

theorem sameMaskedComplex_power {p : B} {a b : ComplexBits B}
    (h : sameMaskedComplex p a b) (n : ℕ) :
    sameMaskedComplex p (a.power n) (b.power n) := by
  induction n with
  | zero => exact sameMaskedComplex_self _ _
  | succ n ih => exact sameMaskedComplex_mul ih h

theorem sameMaskedComplex_taylorPrefix {p : B} {A D : ℕ → ComplexBits B}
    (h : ∀ n,sameMaskedComplex p (A n) (D n)) {Z W : ComplexBits B}
    (hZ : sameMaskedComplex p Z W) (n : ℕ) :
    sameMaskedComplex p (taylorPrefixBits A Z n) (taylorPrefixBits D W n) := by
  induction n with
  | zero => exact sameMaskedComplex_self _ _
  | succ n ih =>
    exact sameMaskedComplex_add ih
      (sameMaskedComplex_mul (h n) (sameMaskedComplex_power hZ n))

theorem masked_roundedLiminf_congr {p : B} {u v : ℕ → RatPresentation → B}
    (h : ∀ n q,p ⊓ u n q = p ⊓ v n q) (q : RatPresentation) :
    p ⊓ roundedLiminfBits u q = p ⊓ roundedLiminfBits v q := by
  unfold roundedLiminfBits
  exact masked_iSup_congr fun r => masked_iSup_congr fun _ => masked_iSup_congr fun N =>
    masked_iInf_congr fun n => h n.val r

theorem sameMaskedComplex_taylorLimit {p : B} {A D : ℕ → ComplexBits B}
    (h : ∀ n,sameMaskedComplex p (A n) (D n)) {Z W : ComplexBits B}
    (hZ : sameMaskedComplex p Z W) :
    sameMaskedComplex p (taylorLimitBits A Z) (taylorLimitBits D W) :=
  ⟨masked_roundedLiminf_congr (fun n => (sameMaskedComplex_taylorPrefix h hZ n).1),
    masked_roundedLiminf_congr (fun n => (sameMaskedComplex_taylorPrefix h hZ n).2)⟩

theorem sameMaskedComplex_name {p : B} {a b : ComplexBits B} (h : sameMaskedComplex p a b) :
    p ≤ a.name =ᴮ b.name :=
  pair_congr (weightedCut_eq_of_mask h.1) (weightedCut_eq_of_mask h.2)

end JSP000930.Positive
