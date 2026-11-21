import JSP000930ActualFreshAllocationPredensity
import JSP000930NegativeMixSiteCore
import JSP000930CoherentPreparedPalettes

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative.Cohen

open JSP000930.BooleanAnalysis JSP000930.Positive JSP000930.Positive.Cohen JSP000930.Positive.Dyadic
open JSP000930.MixedPalettes JSP000933.RelativeOCA JSP000933.OpenGraphForcing
open JSP000933.BooleanCompletion JSP000933.MarkedForcing JSP000933.ForcingTransport
open JSP000933.CantorCodes

variable {B I J : Type} [NontrivialCompleteBooleanAlgebra B]

abbrev StageCohenBA (B : Type) [NontrivialCompleteBooleanAlgebra B] :=
  CohenBA B (PaletteRow OmegaOneIndex × ℕ)

noncomputable def stageCohenMap (B : Type) [NontrivialCompleteBooleanAlgebra B] :
    CompleteValueMap B (StageCohenBA B) :=
  markedCompleteValueMap (valuedCohen B (PaletteRow OmegaOneIndex × ℕ))

noncomputable def actualMixedPalette (M : Label B) (n : ℕ) : ComplexBits (StageCohenBA B) :=
  mixSite (fun r => (stageCohenMap B).toFun (M.value r)) (fun r => paletteBits (B := B) r n)

theorem actualMixedPalette_weight_disjoint (M : Label B) :
    ∀ i j,i ≠ j → Disjoint ((stageCohenMap B).toFun (M.value i)) ((stageCohenMap B).toFun (M.value j)) := by
  intro i j hij
  apply disjoint_iff_inf_le.mpr
  rw [← (stageCohenMap B).map_inf,← (stageCohenMap B).map_bot]
  exact (stageCohenMap B).monotone (disjoint_iff_inf_le.mp (M.disjoint hij))

theorem actualMixedPalette_cutOn (M : Label B) (n : ℕ) :
    (actualMixedPalette M n).CutOn (⊤ : StageCohenBA B) := by
  have h := mixSite_proper (fun r => (stageCohenMap B).toFun (M.value r))
    (fun r => paletteBits (B := B) r n) (actualMixedPalette_weight_disjoint M)
    (fun r => paletteBits_cutOn r n _)
  rw [← (stageCohenMap B).map_iSup,M.covers,(stageCohenMap B).map_top] at h
  exact h

theorem actualMixedPalette_equal_on (M : Label B) (n : ℕ) (r : OmegaOneIndex) :
    (stageCohenMap B).toFun (M.value r) ≤
      (actualMixedPalette M n).name =ᴮ (paletteBits (B := B) r n).name :=
  bSet.bv_symm (sameMaskedComplex_name (mixSite_on
    (fun r => (stageCohenMap B).toFun (M.value r)) (fun r => paletteBits (B := B) r n)
    (actualMixedPalette_weight_disjoint M) r))

open scoped Classical in
noncomputable def extendActualPalette (H : I → J → ℕ → ComplexBits B)
    (M : I → Label B) (z : J) : I → J → ℕ → ComplexBits (StageCohenBA B) :=
  fun i j n => if j=z then actualMixedPalette (M i) n else (H i j n).map (stageCohenMap B)

theorem extendActualPalette_old (H : I → J → ℕ → ComplexBits B)
    (M : I → Label B) (z : J) (i : I) {j : J} (h : j≠z) (n : ℕ) :
    extendActualPalette H M z i j n = (H i j n).map (stageCohenMap B) := by
  classical
  simp only [extendActualPalette,ite_eq_right h]

theorem extendActualPalette_fresh (H : I → J → ℕ → ComplexBits B)
    (M : I → Label B) (z : J) (i : I) (n : ℕ) :
    extendActualPalette H M z i z n = actualMixedPalette (M i) n := by
  classical
  simp [extendActualPalette]

set_option maxHeartbeats 650000 in
theorem choose_actual_fresh_allocation [Fintype I]
    (H : I → J → ℕ → ComplexBits B) (M : I → Label B) (z : J)
    (b₀ : B) (hSep : ∀ i j,i≠j → b₀ ≤ (labelAgreement (M i) (M j))ᶜ)
    (p : I → SymbolicTrace J) (t : CohenTotal B (PaletteRow OmegaOneIndex × ℕ))
    (ht : t.mask ≤ b₀) :
    ∃ q : CohenTotal B (PaletteRow OmegaOneIndex × ℕ),q ≤ t ∧
      ∃ (route : FreshRows p z × Bool → PaletteRow OmegaOneIndex), Function.Injective route ∧
        ∃ (interval : FreshRows p z × Bool → Interval),
          ∀ k : FreshRows p z,
            imageCondition q ≤
              (extendActualPalette H M z k.1 z (pinAt (p k.1) (newPinNumber (p k.1) z k.2)).2).name =ᴮ
              (intervalPointBits B (route (k,false)) (route (k,true))
                (interval (k,false)) (interval (k,true))).name := by
  classical
  let T (k : FreshRows p z) (b : B) := ∃ r : OmegaOneIndex,b ≤ (M k.1).value r
  obtain ⟨a,ha,haT,hA⟩ := exists_finitely_refined_marks T
    (by
      intro k a b hab hB
      obtain ⟨r,hr⟩ := hB
      exact ⟨r,hab.trans hr⟩) t.mask t.nonzero (by
      intro k b hb hbT
      obtain ⟨r,s,hs,hsB,hsR⟩ := exists_nonzero_below_choice_r135 b hb (M k.1).value
        (le_top.trans (M k.1).covers.ge)
      exact ⟨s,hs,hsB,r,hsR⟩)
  choose r hr using hA
  have hR : Function.Injective r := by
    intro i j hij
    by_contra h
    have hne : i.1 ≠ j.1 := fun he => h (Subtype.ext he)
    have hAₛ : a ≤ labelAgreement (M i.1) (M j.1) := by
      unfold labelAgreement
      exact le_iSup_of_le (r i) (le_inf (hr i) (hij.symm ▸ hr j))
    exact ha (disjoint_compl_right.out _ hAₛ ((haT.trans ht).trans (hSep i.1 j.1 hne)))
  let n (k : FreshRows p z) := (pinAt (p k.1) (newPinNumber (p k.1) z k.2)).2
  let route (k : FreshRows p z × Bool) : PaletteRow OmegaOneIndex := (r k.1,n k.1,k.2)
  let interval (k : FreshRows p z × Bool) :=
    if k.2 then (rectangleSchedule (n k.1)).2 else (rectangleSchedule (n k.1)).1
  have hRoute : Function.Injective route := by
    intro x y h
    apply Prod.ext
    · exact hR (congrArg Prod.fst h)
    · exact congrArg (fun v : PaletteRow OmegaOneIndex => v.2.2) h
  let q : CohenTotal B (PaletteRow OmegaOneIndex × ℕ) := ⟨a,t.trace,ha,le_top⟩
  have hqRef : q ≤ t := (cohen_total_le_iff _ _).mpr ⟨haT,le_rfl⟩
  refine ⟨q,hqRef,route,hRoute,interval,?_⟩
  intro k
  have hm (j : FreshRows p z) : imageCondition q ≤ (stageCohenMap B).toFun ((M j.1).value (r j)) :=
    (baseEmbed_reflects_mask_r427 q _).mpr (hr j)
  rw [extendActualPalette_fresh]
  exact (hm k).trans (actualMixedPalette_equal_on (M k.1) (n k) (r k))

end JSP000930.Negative.Cohen
