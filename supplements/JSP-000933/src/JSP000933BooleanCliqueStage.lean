import JSP000933BooleanUncountability

open scoped Cardinal

namespace JSP000933
namespace OpenGraphForcing

open BooleanCompletion

variable {X : Type} {K : Set (X × X)} {Y : OmegaOneIndex → X}

noncomputable def cliqueBit (K : Set (X × X)) (Y : OmegaOneIndex → X) (i : OmegaOneIndex) :
    RO (CliqueCondition K Y) :=
  ⨆ p : {p : CliqueCondition K Y // i ∈ p.1}, imageCondition p.1

theorem cliqueBit_nonzero_r69 (i : OmegaOneIndex) :
    cliqueBit K Y i ≠ ⊥ := by
  classical
  let p : CliqueCondition K Y := ⟨{i},fun x hx y hy hne => by
    have hxi : x = i := Finset.mem_singleton.mp hx
    have hyi : y = i := Finset.mem_singleton.mp hy
    exact False.elim (hne (hxi.trans hyi.symm))⟩
  have hi : i ∈ p.1 := Finset.mem_singleton.mpr rfl
  have hle : imageCondition p ≤ cliqueBit K Y i :=
    le_iSup (fun a : {a : CliqueCondition K Y // i ∈ a.1} => imageCondition a.1) ⟨p,hi⟩
  intro h
  exact imageCondition_ne_bot_r50 p (le_bot_iff.mp (hle.trans_eq h))

theorem cliqueBit_disjoint_of_forbidden_r69 (i j : OmegaOneIndex)
    (hne : i ≠ j) (hNo : (Y i,Y j) ∉ K) :
    Disjoint (cliqueBit K Y i) (cliqueBit K Y j) := by
  classical
  have hPQ (p q : CliqueCondition K Y) (hp : i ∈ p.1) (hq : j ∈ q.1) :
      Disjoint (imageCondition p) (imageCondition q) := by
    by_contra hh
    have hComp : Compatible p q := (compatible_iff_not_disjoint_r50 p q).mpr hh
    have hC := (cliqueCondition_compatible_iff_r66 p q).mp hComp
    exact hNo (hC i (Finset.mem_union.mpr (Or.inl hp)) j (Finset.mem_union.mpr (Or.inr hq)) hne)
  apply le_compl_iff_disjoint_right.mp
  apply iSup_le
  rintro ⟨p,hp⟩
  apply le_compl_iff_disjoint_left.mpr
  apply le_compl_iff_disjoint_right.mp
  apply iSup_le
  rintro ⟨q,hq⟩
  exact le_compl_iff_disjoint_right.mpr (hPQ p q hp hq).symm

theorem exists_forces_uncountableClique_r69
    (hCCC : HasCountableAntichains (CliqueCondition K Y)) :
    ∃ p : CliqueCondition K Y,
      imageCondition p ≤ (countableCoverageValue (cliqueBit K Y))ᶜ := by
  have hB := booleanCCC_of_conditionCCC_r66 hCCC
  have hC : countableCoverageValue (cliqueBit K Y) ≠ ⊤ :=
    countableCoverageValue_ne_top_r68 hB OmegaOneIndex_not_countable_r61 (cliqueBit K Y)
      (cliqueBit_nonzero_r69 (K := K) (Y := Y))
  have hN : (countableCoverageValue (cliqueBit K Y))ᶜ ≠ ⊥ := by
    intro h
    apply hC
    apply compl_injective
    simpa only [compl_top] using h
  exact imageCondition_dense_r50 _ hN

theorem exists_CH_BooleanClique_stage_r69 [TopologicalSpace X] [SecondCountableTopology X]
    (hK : IsOpen K) (hSym : ∀ x y, (x,y) ∈ K → (y,x) ∈ K)
    (hIrr : ∀ x, (x,x) ∉ K) (hChrom : UncountablyChromatic K)
    (embed : X → RealCode) (hEmbed : Function.Injective embed) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ Z : OmegaOneIndex → X, Function.Injective Z ∧
      BooleanCCC (RO (CliqueCondition K Z)) ∧
      (∀ i j, i ≠ j → (Z i,Z j) ∉ K → Disjoint (cliqueBit K Z i) (cliqueBit K Z j)) ∧
      ∃ p : CliqueCondition K Z, imageCondition p ≤ (countableCoverageValue (cliqueBit K Z))ᶜ := by
  obtain ⟨Z,hZ,hF⟩ := exists_indexed_ccc_clique_forcing_r65 hK hSym hIrr hChrom embed hEmbed CH
  have hCCC := cliqueCondition_countableAntichains_r66 hF
  exact ⟨Z,hZ,booleanCCC_of_conditionCCC_r66 hCCC,cliqueBit_disjoint_of_forbidden_r69,
    exists_forces_uncountableClique_r69 hCCC⟩

end OpenGraphForcing
end JSP000933
