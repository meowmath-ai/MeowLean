import JSP000930PositiveNativeGrowthNaturality
import JSP000930PositiveMaskedProperCutTransfer

open bSet Lattice
open scoped Flypitch

namespace JSP000930.Positive

open JSP000930.BooleanAnalysis

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

theorem masked_inf_congr {p a b c d : B}
    (h₁ : p ⊓ a = p ⊓ b) (h₂ : p ⊓ c = p ⊓ d) :
    p ⊓ (a ⊓ c) = p ⊓ (b ⊓ d) := by
  calc
    p ⊓ (a ⊓ c) = (p ⊓ a) ⊓ (p ⊓ c) := by
      apply le_antisymm
      · exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
          (le_inf inf_le_left (inf_le_right.trans inf_le_right))
      · exact le_inf (inf_le_left.trans inf_le_left)
          (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
    _ = (p ⊓ b) ⊓ (p ⊓ d) := by rw [h₁,h₂]
    _ = p ⊓ (b ⊓ d) := by
      apply le_antisymm
      · exact le_inf (inf_le_left.trans inf_le_left)
          (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
      · exact le_inf (le_inf inf_le_left (inf_le_right.trans inf_le_left))
          (le_inf inf_le_left (inf_le_right.trans inf_le_right))

theorem masked_sup_congr {p a b c d : B}
    (h₁ : p ⊓ a = p ⊓ b) (h₂ : p ⊓ c = p ⊓ d) :
    p ⊓ (a ⊔ c) = p ⊓ (b ⊔ d) := by
  simp only [inf_sup_left,h₁,h₂]

theorem masked_iSup_congr {I : Sort*} {p : B} {U V : I → B}
    (h : ∀ i,p ⊓ U i = p ⊓ V i) : p ⊓ (⨆ i,U i) = p ⊓ (⨆ i,V i) := by
  simp only [inf_iSup_eq]
  exact iSup_congr h

theorem masked_iInf_congr {I : Sort*} {p : B} {U V : I → B}
    (h : ∀ i,p ⊓ U i = p ⊓ V i) : p ⊓ (⨅ i,U i) = p ⊓ (⨅ i,V i) := by
  have one (U V : I → B) (h' : ∀ i,p ⊓ U i = p ⊓ V i) :
      p ⊓ (⨅ i,U i) ≤ p ⊓ (⨅ i,V i) := by
    refine le_inf inf_le_left (le_iInf (fun i => ?_))
    exact (le_inf inf_le_left (inf_le_right.trans (iInf_le _ i))).trans
      ((h' i).le.trans inf_le_right)
  exact le_antisymm (one U V h) (one V U (fun i => (h i).symm))

theorem masked_addCutBits_congr {p : B} {u u' v v' : RatPresentation → B}
    (hu : ∀ q,p ⊓ u q = p ⊓ u' q) (hv : ∀ q,p ⊓ v q = p ⊓ v' q)
    (q : RatPresentation) : p ⊓ addCutBits u v q = p ⊓ addCutBits u' v' q := by
  unfold addCutBits
  exact masked_iSup_congr fun r => masked_iSup_congr fun s => masked_iSup_congr fun _ =>
    masked_inf_congr (hu r) (hv s)

theorem masked_intervalBits_congr {p : B} {u u' : RatPresentation → B}
    (hu : ∀ q,p ⊓ u q = p ⊓ u' q) (a b : RatPresentation) :
    p ⊓ intervalBits u a b = p ⊓ intervalBits u' a b := by
  unfold intervalBits
  exact masked_inf_congr (hu a) (masked_iSup_congr fun t =>
    masked_iSup_congr fun _ => compl_eq_under_same_mask (hu t))

theorem masked_mulCutBits_congr {p : B} {u u' v v' : RatPresentation → B}
    (hu : ∀ q,p ⊓ u q = p ⊓ u' q) (hv : ∀ q,p ⊓ v q = p ⊓ v' q)
    (q : RatPresentation) : p ⊓ mulCutBits u v q = p ⊓ mulCutBits u' v' q := by
  unfold mulCutBits
  exact masked_iSup_congr fun a => masked_iSup_congr fun b => masked_iSup_congr fun c =>
    masked_iSup_congr fun d => masked_iSup_congr fun _ =>
      masked_inf_congr (masked_intervalBits_congr hu a b) (masked_intervalBits_congr hv c d)

theorem masked_radiusBudgetBits_congr {p : B} {a a' : ComplexBits B}
    (hr : ∀ q,p ⊓ a.re q = p ⊓ a'.re q) (hi : ∀ q,p ⊓ a.im q = p ⊓ a'.im q)
    (R K n : ℕ) :
    p ⊓ radiusBudgetBits a R K n = p ⊓ radiusBudgetBits a' R K n := by
  have h₁ : ∀ q, p ⊓ a.normSq q = p ⊓ a'.normSq q :=
    masked_addCutBits_congr (masked_mulCutBits_congr hr hr) (masked_mulCutBits_congr hi hi)
  let crisp : RatPresentation → B := checkedRealBits (((R : ℝ)^n)^2)
  have h₂ := masked_mulCutBits_congr h₁ (v := crisp) (v' := crisp) (fun _ => rfl)
  unfold radiusBudgetBits
  rw [weightedRationalSet_subset,weightedRationalSet_subset]
  apply masked_iInf_congr
  intro q
  change p ⊓ imp (mulCutBits a.normSq crisp q) _ =
    p ⊓ imp (mulCutBits a'.normSq crisp q) _
  unfold imp
  exact masked_sup_congr (compl_eq_under_same_mask (h₂ q)) rfl

theorem masked_growthValue_congr {p : B} {U V : ℕ → ComplexBits B}
    (hr : ∀ n q,p ⊓ (U n).re q = p ⊓ (V n).re q)
    (hi : ∀ n q,p ⊓ (U n).im q = p ⊓ (V n).im q) :
    p ⊓ growthValue U = p ⊓ growthValue V := by
  unfold growthValue
  exact masked_iInf_congr fun R => masked_iInf_congr fun _ =>
    masked_iSup_congr fun K => masked_iInf_congr fun n =>
      masked_radiusBudgetBits_congr (hr n) (hi n) R K n

end JSP000930.Positive
