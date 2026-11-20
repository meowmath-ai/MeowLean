import JSP000933NativeGroundTailCarriers
import JSP000933CompleteDiagramLimit

namespace JSP000933
namespace ForcingTransport

open BooleanCompletion MarkedForcing FiniteSupport RelativeOCA OpenGraphForcing

variable {B P N : Type} [CompleteBooleanAlgebra B] [Preorder P] [Preorder N] [OrderTop N]

theorem DenseForcingMap.pull_imageMap {Q : Type} [Preorder Q] (F : DenseForcingMap P Q) (p : P) :
    F.pullIso (imageCondition (F.map p)) = imageCondition p := by
  apply le_antisymm
  · apply le_of_image_tests
    intro q hq
    have hq' : imageCondition (F.map q) ≤ imageCondition (F.map p) := by
      apply (image_le_iff_member _ _).mpr
      exact (F.mem_pull _ _).mp ((image_le_iff_member _ _).mp hq)
    apply CompleteDiagram.image_le_of_dense q
    intro r hr
    have hr' := (imageCondition_mono_r50 (F.monotone hr)).trans hq'
    have hc : Compatible (F.map r) (F.map p) := by
      apply (compatible_iff_not_disjoint_r50 _ _).mpr
      intro h
      exact imageCondition_ne_bot_r50 (F.map r) (h.out _ le_rfl hr')
    obtain ⟨s,hs,hsp⟩ := F.reflect_compatible hc
    exact ⟨s,hs,imageCondition_mono_r50 hsp⟩
  · exact (image_le_iff_member _ _).mpr (imageCondition_mem_r50 (F.map p))

namespace TailPresentation
variable {M : MaskRealization B P} (S : TailPresentation (N := N) M)

theorem project_quotient_coherent (x : TotalBA S.quotient) :
    M.project (S.denseMap.pullIso x) = supportProjection S.quotient x := by
  have hAdj (b : B) :
      M.project (S.denseMap.pullIso x)≤b ↔ supportProjection S.quotient x≤b := by
    rw [M.project_gc,supportProjection_le_iff_r428,← S.quotient_base_coherent]
    exact S.denseMap.pullIso.le_iff_le
  exact le_antisymm ((hAdj _).mpr le_rfl) ((hAdj _).mp le_rfl)

theorem quotient_relativeCCC (hCCC : ProjectedAntichainCCC M.project) :
    ForcesRelativeCCC S.quotient := by
  intro W hW hSep
  let Q := S.quotient
  let X (i : OmegaOneIndex) := ⨆ n, traceValue Q n ⊓ baseEmbed Q (W i n)
  have hX (i j : OmegaOneIndex) (hij : i<j) : Disjoint (X i) (X j) := by
    apply disjoint_iff_inf_le.mpr
    simp only [X,iSup_inf_iSup]
    apply iSup_le
    rintro ⟨n,k⟩
    have h0 : Disjoint (commonRefinementValue Q n k) (W i n⊓W j k) := by
      apply disjoint_iff_inf_le.mpr
      rw [inf_comm]
      exact (hSep i j hij n k).le
    have h1 := (mask_forces_incompatibility_iff_r430 Q n k (W i n⊓W j k)).mpr h0
    have h2 : (traceValue Q n⊓baseEmbed Q (W i n))⊓(traceValue Q k⊓baseEmbed Q (W j k)) =
        (traceValue Q n⊓traceValue Q k)⊓baseEmbed Q (W i n⊓W j k) := by
      rw [baseEmbed_meets_r429]
      ac_rfl
    exact (h2.trans h1).le
  have hRows (i : OmegaOneIndex) : supportProjection Q (X i) = ⨆ n,W i n := by
    unfold X
    rw [(supportProjection_gc_r428 Q).l_iSup]
    congr 1
    funext n
    rw [supportProjection_meet_base_r428,traceValue_support_r429,inf_eq_right.mpr (hW i n)]
  have hFinal := hCCC (fun i => S.denseMap.pullIso (X i)) (by
    intro i j hij
    apply disjoint_iff_inf_le.mpr
    let e := S.denseMap.pullIso
    change e (X i) ⊓ e (X j) ≤ ⊥
    rw [←e.map_inf,←e.map_bot]
    exact e.monotone (disjoint_iff_inf_le.mp (hX i j hij)))
  have hEq : (fun i => M.project (S.denseMap.pullIso (X i))) = fun i => ⨆ n, W i n := by
    funext i
    exact (S.project_quotient_coherent (X i)).trans (hRows i)
  rwa [hEq] at hFinal

theorem pull_tail_traceValue (n : N) :
    S.denseMap.pullIso (traceValue S.quotient n) =
      ⨆ p : {p : P // S.strip p=n},imageCondition p.val := by
  have hSup : traceValue S.quotient n =
      ⨆ p : {p : P // S.strip p=n},imageCondition (S.map p.val) := by
    have hBd : traceValue S.quotient n ≤ baseEmbed S.quotient (S.valid n) := by
      apply (supportProjection_le_iff_r428 _ _ _).mp
      rw [traceValue_support_r429]
      exact le_rfl
    calc
      traceValue S.quotient n = traceValue S.quotient n ⊓ baseEmbed S.quotient (S.valid n) :=
        (inf_eq_left.mpr hBd).symm
      _ = ⨆ p : {p : P // S.strip p=n},traceValue S.quotient n⊓baseEmbed S.quotient (M.mask p.val) := by
        rw [valid,baseEmbed_joins_r427,inf_iSup_eq]
      _ = _ := by
        congr 1
        funext p
        rw [inf_comm,image_eq_base_meet_trace_r429]
        change _ = baseEmbed S.quotient (M.mask p.val)⊓traceValue S.quotient (S.strip p.val)
        rw [p.property]
  rw [hSup,OrderIso.map_iSup]
  congr 1
  funext p
  exact S.denseMap.pull_imageMap p.val

end TailPresentation
end ForcingTransport
end JSP000933
