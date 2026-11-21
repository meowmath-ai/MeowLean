import JSP000930RelativeCCCLabelCharts
import JSP000933NativeSuccessorCCC

namespace JSP000930.Negative

open JSP000933.MarkedForcing JSP000933.RelativeOCA JSP000933.OpenGraphForcing
open JSP000933.BooleanCompletion JSP000933.ForcingTransport

variable {B N M : Type} [NontrivialCompleteBooleanAlgebra B]

theorem relativeCCC_of_base_dense (P : ValuedPoset B N) (Q : ValuedPoset B M)
    (D : DenseForcingMap (TotalCondition P) (TotalCondition Q))
    (hD : ∀ b,D.pullIso (baseEmbed Q b) = baseEmbed P b)
    (hQ : ForcesRelativeCCC Q) : ForcesRelativeCCC P := by
  let E := D.pullIso
  have hE (x : TotalBA P) : supportProjection P x = supportProjection Q (E.symm x) := by
    have hh (b : B) : supportProjection P x ≤ b ↔ supportProjection Q (E.symm x) ≤ b := by
      rw [supportProjection_le_iff_r428,supportProjection_le_iff_r428]
      constructor
      · intro hx
        apply E.symm.monotone at hx
        rw [← hD,E.symm_apply_apply] at hx
        exact hx
      · intro hx
        have hh := E.monotone hx
        rw [E.apply_symm_apply,hD] at hh
        exact hh
    exact le_antisymm ((hh _).mpr le_rfl) ((hh _).mp le_rfl)
  apply (relativeCCC_iff_projected P).mpr
  intro f hf
  simp only [hE]
  apply relativeCCC_projectedAntichain_bounded_r434 Q hQ
  intro i j hij
  apply disjoint_iff_inf_le.mpr
  rw [← E.symm.map_inf,← E.symm.map_bot]
  exact E.symm.monotone (disjoint_iff_inf_le.mp (hf i j hij))

theorem taggedDenseMap_base (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest)
    (put : N → M) (hPut : ∀ n,load (put n) = some n) (b : B) :
    (taggedDenseMap Q load zero hZero put hPut).pullIso (baseEmbed Q b) =
      baseEmbed (taggedValuedPoset Q load zero hZero) b := by
  let D := taggedDenseMap Q load zero hZero put hPut
  have ht (p : TotalCondition (taggedValuedPoset Q load zero hZero)) :
      imageCondition p ≤ D.pullIso (baseEmbed Q b) ↔
        imageCondition p ≤ baseEmbed (taggedValuedPoset Q load zero hZero) b := by
    rw [image_le_iff_member]
    change D.map p ∈ (baseEmbed Q b : LowerSet (TotalCondition Q)) ↔ _
    rw [← image_le_iff_member,baseEmbed_reflects_mask_r427,baseEmbed_reflects_mask_r427] <;> rfl
  exact le_antisymm (le_of_image_tests (fun p => (ht p).mp))
    (le_of_image_tests (fun p => (ht p).mpr))

theorem relativeCCC_tagged (Q : ValuedPoset B N) (load : M → Option N)
    (zero : M) (hZero : load zero = some Q.weakest)
    (put : N → M) (hPut : ∀ n,load (put n) = some n)
    (hQ : ForcesRelativeCCC Q) : ForcesRelativeCCC (taggedValuedPoset Q load zero hZero) :=
  relativeCCC_of_base_dense _ Q (taggedDenseMap Q load zero hZero put hPut)
    (taggedDenseMap_base Q load zero hZero put hPut) hQ

theorem relativeCCC_certified (Q : ValuedPoset B N) (hQ : ForcesRelativeCCC Q) :
    ForcesRelativeCCC (certifiedQ Q) :=
  relativeCCC_of_base_dense _ Q (certifiedHeadDenseMap Q) (certifiedHeadDenseMap_base Q) hQ

end JSP000930.Negative
