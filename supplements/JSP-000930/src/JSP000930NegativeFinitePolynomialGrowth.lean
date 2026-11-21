import JSP000930NegativePolynomialDecision

open Fol Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.BooleanNames

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

def padCoeff {α : Type} (zero : α) : List α → ℕ → α
  | [], _ => zero
  | x :: _, 0 => x
  | _ :: s, n+1 => padCoeff zero s n

theorem padCoeff_eq_zero_after {α : Type} (zero : α) (f : List α)
    (i : ℕ) (hi : f.length ≤ i) : padCoeff zero f i = zero := by
  induction f generalizing i with
  | nil => rfl
  | cons x f ih =>
    cases i with
    | zero => simp at hi
    | succ i => exact ih i (by simpa using hi)

theorem padCoeff_mem_or_default {α : Type} (zero : α) (f : List α) (i : ℕ) :
    padCoeff zero f i ∈ f ∨ padCoeff zero f i = zero := by
  induction f generalizing i with
  | nil => exact Or.inr rfl
  | cons x f ih =>
    cases i with
    | zero => exact Or.inl List.mem_cons_self
    | succ i =>
      rcases ih i with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

noncomputable def zeroPaddedPoly (f : List (ComplexBits B)) : ℕ → ComplexBits B :=
  padCoeff (ComplexBits.ofNat 0) f

theorem zeroPaddedPoly_cutOn (f : List (ComplexBits B)) (m : B)
    (hf : ∀ c ∈ f,c.CutOn m) (i : ℕ) :
    (zeroPaddedPoly f i).CutOn m := by
  rcases padCoeff_mem_or_default (ComplexBits.ofNat 0) f i with h | h
  · exact hf _ h
  · change (padCoeff (ComplexBits.ofNat 0) f i).CutOn m
    rw [h]
    exact ComplexBits.ofNat_cutOn 0 m

theorem radiusBudget_zero_forces (m : B) (R K n : ℕ) :
    m ≤ radiusBudgetBits (ComplexBits.ofNat 0) R K n := by
  let z : ComplexBits B := ComplexBits.ofNat 0
  let c := ((R : ℝ)^n)^2
  let u := mulCutBits z.normSq (checkedRealBits c)
  let v := checkedRealBits (B := B) ((K : ℝ)^2)
  have hz : z.CutOn m := ComplexBits.ofNat_cutOn 0 m
  have hu := mulCutBits_properCut z.normSq (checkedRealBits c) m
    (ComplexBits.normSq_cutOn hz) (properCutOn_mono le_top (checkedRealBits_properCut c))
  change m ≤ weightedRationalSet u ⊆ᴮ weightedRationalSet v
  refine cutSubset_of_decision_law (fun _ : Unit => z) m (fun _ => hz) u v hu ?_
  intro p w hp hn hpm ht
  have h0 : ComplexDecisionTrace p z (0 : ℂ) := by
    simpa [z] using ComplexDecisionTrace.ofNat p 0
  have ht0 := (h0.normSq hp hpm hz).mul hp hpm (checkedRealBits_traces p c)
    (ComplexBits.normSq_cutOn hz) (properCutOn_mono le_top (checkedRealBits_properCut c))
  refine ⟨Complex.normSq (0 : ℂ)*c,(K : ℝ)^2,ht0,checkedRealBits_traces p _,?_⟩
  simp

theorem cut_boundedSqNat_cover {m : B} {u : RatPresentation → B} (hu : ProperCutOn m u) :
    m ≤ ⨆ K : ℕ, weightedRationalSet u ⊆ᴮ weightedRationalSet (checkedRealBits ((K : ℝ)^2)) := by
  apply (le_inf le_rfl hu.2.1).trans
  rw [inf_iSup_eq]
  refine iSup_le fun q => ?_
  let d : ℝ := |(q.value : ℝ)| + 1
  obtain ⟨K,hK⟩ := exists_nat_gt d
  have hD : (1 : ℝ) ≤ d := by dsimp [d]; linarith [abs_nonneg (q.value : ℝ)]
  have hk1 := hD.trans hK.le
  have hh : (K : ℝ) ≤ (K : ℝ)^2 := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hk1 (show 0 ≤ (K : ℝ) by positivity)
  have hq : (q.value : ℝ) ≤ (K : ℝ)^2 :=
    (le_abs_self _).trans (by dsimp [d] at hK; linarith only [hK,hh])
  exact (cut_le_checked_of_upper (properCutOn_mono inf_le_left hu) q _ hq inf_le_right).trans (le_iSup (fun n : ℕ => (weightedRationalSet u ⊆ᴮ weightedRationalSet (checkedRealBits ((n : ℝ)^2)))) K)

private theorem radiusBudget_mono (a : ComplexBits B) (R n : ℕ) :
    Monotone (fun K : ℕ => radiusBudgetBits a R K n) := by
  intro K L h
  have h' : (K : ℝ) ≤ (L : ℝ) := by exact_mod_cast h
  have hsq : (K : ℝ)^2 ≤ (L : ℝ)^2 := pow_le_pow_left₀ (by positivity) h' 2
  simp only [radiusBudgetBits,weightedRationalSet_subset]
  apply iInf_mono
  intro q
  unfold imp
  apply sup_le_sup_left
  by_cases hq : (q.value : ℝ) < (K : ℝ)^2
  · simp [checkedRealBits,JSP000933.PositiveForcing.crispTruth,hq,hq.trans_le hsq]
  · simp [checkedRealBits,JSP000933.PositiveForcing.crispTruth,hq]

private theorem finiteChoice_uniform {m : B} (F : ℕ → ℕ → B)
    (hMono : ∀ i,Monotone (F i)) (L : ℕ) (h : ∀ i < L,m ≤ ⨆ K : ℕ,F i K) :
    m ≤ ⨆ K : ℕ,⨅ i : Fin L,F i.val K := by
  induction L with
  | zero =>
    refine le_iSup_of_le 0 ?_
    exact le_iInf fun i => Fin.elim0 i
  | succ L ih =>
    have h₁ := ih (fun i hi => h i (hi.trans (Nat.lt_succ_self L)))
    have h₂ := h L (Nat.lt_succ_self L)
    apply (le_inf h₁ h₂).trans
    rw [iSup_inf_eq]
    refine iSup_le fun K => ?_
    rw [inf_iSup_eq]
    refine iSup_le fun M => ?_
    apply le_iSup_of_le (max K M)
    refine le_iInf fun i => ?_
    by_cases hi : i.val < L
    · exact (inf_le_left.trans (iInf_le _ (⟨i.val,hi⟩ : Fin L))).trans
        (hMono i.val (le_max_left _ _))
    · have he : i.val = L := by omega
      rw [he]
      exact inf_le_right.trans (hMono L (le_max_right _ _))

theorem zeroPaddedPoly_growth (f : List (ComplexBits B)) (m : B) (hf : ∀ c ∈ f,c.CutOn m) :
    GrowthOn m (zeroPaddedPoly f) := by
  intro R hR
  let F (n K : ℕ) := radiusBudgetBits (zeroPaddedPoly f n) R K n
  have hB (n : ℕ) : m ≤ ⨆ K : ℕ,F n K := by
    have hc := zeroPaddedPoly_cutOn f m hf n
    have hcut := mulCutBits_properCut (zeroPaddedPoly f n).normSq
      (checkedRealBits (((R : ℝ)^n)^2)) m (ComplexBits.normSq_cutOn hc)
      (properCutOn_mono le_top (checkedRealBits_properCut _))
    exact cut_boundedSqNat_cover hcut
  have hFin := finiteChoice_uniform F (fun i => radiusBudget_mono (zeroPaddedPoly f i) R i)
    f.length (fun i _ => hB i)
  apply (le_inf le_rfl hFin).trans
  rw [inf_iSup_eq]
  refine iSup_le fun K => le_iSup_of_le K (le_iInf fun n => ?_)
  by_cases hn : n < f.length
  · exact inf_le_right.trans (iInf_le _ (⟨n,hn⟩ : Fin f.length))
  · have hz : zeroPaddedPoly f n = ComplexBits.ofNat 0 :=
      padCoeff_eq_zero_after (ComplexBits.ofNat 0) f n (le_of_not_gt hn)
    unfold F
    rw [hz]
    exact inf_le_left.trans (radiusBudget_zero_forces m R K n)

end JSP000930.Negative
