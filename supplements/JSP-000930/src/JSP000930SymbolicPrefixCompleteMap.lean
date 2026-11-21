import JSP000930RegularOpenBasicCoherence

open Lattice
open scoped Flypitch bSet

namespace JSP000930.Negative

open JSP000930.BooleanAnalysis JSP000933.MarkedForcing JSP000933.BooleanCompletion

variable {B C J : Type} [NontrivialCompleteBooleanAlgebra B] [NontrivialCompleteBooleanAlgebra C]
variable {A A' : J → Prop}
variable (hAA : ∀ j,A j → A' j) (F : CompleteValueMap B C)
variable (site : J → ComplexBits B) (H : J → ℕ → ComplexBits B)
variable (site' : J → ComplexBits C) (H' : J → ℕ → ComplexBits C)
variable (hS : ∀ j,A j → (site j).map F = site' j)
variable (hH : ∀ j,A j → ∀ n,(H j n).map F = H' j n)
variable (hSite' : ∀ j,A j → (site' j).CutOn (⊤ : C))
variable (hH' : ∀ j,A j → ∀ n,(H' j n).CutOn (⊤ : C))
variable (hApart' : ∀ j,A j → ∀ i,A i → j ≠ i →
  (⊤ : C) ≤ ((site' j).name =ᴮ (site' i).name)ᶜ)
variable (hPred : PreservesPredensity (includeSupportedCondition hAA F site H site' H' hS hH))

noncomputable def supportedPrefixCompleteMap :
    CompleteValueMap (TotalBA (supportedSymbolicQ site H A)) (TotalBA (supportedSymbolicQ site' H' A')) :=
  completeMapFromPredensity (includeSupportedCondition hAA F site H site' H' hS hH) hPred
    (fun h => (includeSupportedCondition_compatible_iff hAA F site H site' H' hS hH
      hSite' hH' hApart' _ _).mp h)

theorem supportedPrefixCompleteMap_basic (p : TotalCondition (supportedSymbolicQ site H A)) :
    (supportedPrefixCompleteMap hAA F site H site' H' hS hH hSite' hH' hApart' hPred).toFun
      (imageCondition p) =
      imageCondition (includeSupportedCondition hAA F site H site' H' hS hH p) :=
  completeMapFromPredensity_image _ (fun _ _ h =>
    (includeSupportedCondition_le_iff hAA F site H site' H' hS hH _ _).mpr h) hPred
    (fun h => (includeSupportedCondition_compatible_iff hAA F site H site' H' hS hH
      hSite' hH' hApart' _ _).mp h) p

theorem supportedPrefixCompleteMap_base (b : B) :
    (supportedPrefixCompleteMap hAA F site H site' H' hS hH hSite' hH' hApart' hPred).toFun
      (baseEmbed (supportedSymbolicQ site H A) b) =
      baseEmbed (supportedSymbolicQ site' H' A') (F.toFun b) := by
  let Q := supportedSymbolicQ site H A
  let Q' := supportedSymbolicQ site' H' A'
  let M := supportedPrefixCompleteMap hAA F site H site' H' hS hH hSite' hH' hApart' hPred
  have hL (b : B) : M.toFun (baseEmbed Q b) ≤ baseEmbed Q' (F.toFun b) := by
    change basisImage (includeSupportedCondition hAA F site H site' H' hS hH)
      (baseEmbed Q b) ≤ baseEmbed Q' (F.toFun b)
    apply iSup_le
    intro p
    have hp := (baseEmbed_reflects_mask_r427 p.val b).mp ((JSP000933.ForcingTransport.image_le_iff_member p.val (baseEmbed Q b)).mpr p.2)
    apply (baseEmbed_reflects_mask_r427 _ _).mpr
    exact F.monotone hp
  apply le_antisymm (hL b)
  have hr := compl_le_compl (hL bᶜ)
  change (baseEmbed Q' (F.toFun bᶜ))ᶜ ≤ (M.toFun (baseEmbed Q bᶜ))ᶜ at hr
  rw [F.map_compl,baseEmbed_compl_r427,baseEmbed_compl_r427,M.map_compl,
    compl_compl,compl_compl] at hr
  exact hr

end JSP000930.Negative
