import JSP000930AnalyticRadiusCoefficient
import JSP000930PositiveLiteralSequenceGivesProperCoefficients

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.AnalyticSyntax

open JSP000933.SetLanguage JSP000933.PositiveForcing JSP000933.BooleanNames
open JSP000930.BooleanAnalysis JSP000930.Positive

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

noncomputable def sequenceBits (G : bSet B) (i : ℕ) : ComplexBits B :=
  ⟨fun q => graphTaylorBits G (i,false,q),fun q => graphTaylorBits G (i,true,q)⟩

theorem sequenceBits_actual {n : ℕ} (v : DVec (V B) n) (A : STerm n) (p : B)
    (hA : p ≤ bTruth v (sequence_f A)) :
    (p ≤ bSet.is_func (bTerm v A)) ∧
      (∀ i, (sequenceBits (bTerm v A) i).CutOn p) ∧
      (∀ i, p ≤ bSet.pair (bSet.of_nat i) (sequenceBits (bTerm v A) i).name ∈ᴮ bTerm v A) := by
  have hT := hA.trans (typedComplexFunction_le_native v A omega)
  have hShape : p ≤ graphTypedShape (bTerm v A) (bSet.omega : bSet B) := hT.trans inf_le_left
  have hTot : p ≤ graphTypedTotalUnique (bTerm v A) (bSet.omega : bSet B) := hT.trans inf_le_right
  have hF := typedGraph_func hShape hTot
  refine ⟨hF,fun i => ⟨sequence_graphTaylorBits_proper v A p hA i false,
    sequence_graphTaylorBits_proper v A p hA i true⟩,fun i => ?_⟩
  exact graphTaylorBits_named_coeff_mem (bTerm v A) p hF
    (fun j => typedGraph_good_total_omega hTot j) i

theorem bTruth_radiusBudget_weighted {n : ℕ} (v : DVec (V B) n)
    (A R K N : STerm n) (z : ComplexBits B) (r k i : ℕ) (p : B)
    (hR : bTerm v R = bSet.of_nat r) (hK : bTerm v K = bSet.of_nat k)
    (hN : bTerm v N = bSet.of_nat i) (hz : z.CutOn p)
    (hF : p ≤ bSet.is_func (bTerm v A))
    (hMember : p ≤ bSet.pair (bSet.of_nat i) z.name ∈ᴮ bTerm v A) :
    p ⊓ bTruth v (radiusBudget_f A R K N) = p ⊓ radiusBudgetBits z r k i := by
  let T : STerm (n+1) := bd_var ⟨0,Nat.succ_pos n⟩
  let W (x : bSet B) : DVec (V B) (n+1) := DVec.cons x v
  let φ := radiusCoefficient_f T (up R) (up K) (up N)
  have hRad : p ⊓ bTruth (W z.name) φ = p ⊓ radiusBudgetBits z r k i :=
    bTruth_radiusCoefficient_checked (W z.name) T (up R) (up K) (up N) z r k i p
      (bTerm_current_r181 v z.name) ((bTerm_up_r181 v z.name R).trans hR)
      ((bTerm_up_r181 v z.name K).trans hK) ((bTerm_up_r181 v z.name N).trans hN) hz
  have hValue (x : bSet B) : bTruth (W x) (value_f (up A) (up N) T) =
      (bSet.pair (bSet.of_nat i) x ∈ᴮ bTerm v A) := by
    rw [bTruth_value,(bTerm_up_r181 v x N).trans hN,bTerm_current_r181 v x,bTerm_up_r181 v x A]
  unfold radiusBudget_f
  rw [bTruth_sEx_r181]
  change p ⊓ (⨆ x : bSet B, bTruth (W x)
    (bd_and (complex_f T) (bd_and (value_f (up A) (up N) T) φ))) = _
  simp only [bTruth_and_eq,hValue]
  change (p ⊓ (⨆ x : bSet B, bTruth (W x) (complex_f T) ⊓
    ((bSet.pair (bSet.of_nat i) x ∈ᴮ bTerm v A) ⊓ bTruth (W x) φ))) = _
  rw [inf_iSup_eq]
  apply le_antisymm
  · refine iSup_le fun x => ?_
    let e := p ⊓ (bTruth (W x) (complex_f T) ⊓
      ((bSet.pair (bSet.of_nat i) x ∈ᴮ bTerm v A) ⊓ bTruth (W x) φ))
    have ep : e ≤ p := inf_le_left
    have h : e ≤ x =ᴮ z.name :=
      bSet.eq_of_is_func_of_eq (ep.trans hF) (le_top.trans bSet.bv_refl)
        (inf_le_right.trans (inf_le_right.trans inf_le_left)) (ep.trans hMember)
    have hφ := (le_inf le_rfl (inf_le_right.trans (inf_le_right.trans inf_le_right))).trans
      ((bTruth_oneMask v x z.name φ e h).le.trans inf_le_right)
    exact (le_inf ep hφ).trans hRad.le
  · apply le_iSup_of_le z.name
    refine le_inf inf_le_left (le_inf ?_ (le_inf ?_ ?_))
    · exact inf_le_left.trans (forces_complexBits_name (W z.name) T z p
        (bTerm_current_r181 v z.name) hz)
    · exact inf_le_left.trans hMember
    · exact hRad.symm.le.trans inf_le_right

end JSP000930.AnalyticSyntax
