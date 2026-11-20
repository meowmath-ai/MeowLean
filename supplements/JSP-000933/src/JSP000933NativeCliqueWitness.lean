import JSP000933ActivatedMatchingPolicy
import JSP000933CCCUncountabilityPersistence

open scoped Cardinal

namespace JSP000933
namespace CantorCodes

open FiniteSupport BooleanCompletion OpenGraphForcing

variable {B : Type} [CompleteBooleanAlgebra B]

noncomputable def weightedCliqueValue
    (D : (ℕ → B) → B) (K : Word × Word → B)
    (x : OmegaOneIndex → ℕ → B) (g : OmegaOneIndex → B) : B :=
  (⨅ i, (g i)ᶜ ⊔ D (x i)) ⊓
  ((⨅ ij : {ij : OmegaOneIndex × OmegaOneIndex // ij.1 ≠ ij.2},
      (g ij.1.1 ⊓ g ij.1.2)ᶜ ⊔
        (colorValue K (x ij.1.1) (x ij.1.2) ⊓ (realEqValue (x ij.1.1) (x ij.1.2))ᶜ)) ⊓
    (countableCoverageValue g)ᶜ)

theorem exists_omegaTwo_actualSuccessor_r169 (a : OmegaTwoIndex) :
    ∃ b : OmegaTwoIndex, ∀ i : OmegaTwoIndex, i < b ↔ i ≤ a := by
  let o := (Order.succ (ℵ₁ : Cardinal)).ord
  let t := Ordinal.ToType.mk (o := o)
  let α := (t.symm a).1
  have hReg : (Order.succ (ℵ₁ : Cardinal)).IsRegular :=
    Cardinal.isRegular_succ Cardinal.isRegular_aleph_one.1
  have hh : α + 1 < o := (Cardinal.isSuccLimit_ord hReg.1).add_one_lt (t.symm a).2
  refine ⟨t ⟨α+1,hh⟩,fun i => ?_⟩
  have hi : i < t ⟨α+1,hh⟩ ↔ (t.symm i).1 < α+1 := by
    constructor
    · intro h
      have hh' := t.symm.strictMono h
      rw [t.symm_apply_apply] at hh'
      exact hh'
    · intro h
      have hh' : t.symm i < (⟨α+1,hh⟩ : ↥(Set.Iio o)) := h
      have hp := t.strictMono hh'
      rw [t.apply_symm_apply i] at hp
      exact hp
  have hle : (t.symm i).1 ≤ α ↔ i ≤ a := by
    constructor
    · intro h
      have hh' : t.symm i ≤ t.symm a := h
      have hp := t.monotone hh'
      rw [t.apply_symm_apply i,t.apply_symm_apply a] at hp
      exact hp
    · exact fun h => t.symm.monotone h
  rw [hi,← hle]
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt h) (Order.add_one_le_iff.mpr (lt_of_not_ge hn))
  · intro h
    exact h.trans_lt (Order.add_one_le_iff.mp le_rfl)

theorem ocaTotal_stageMap_coherent_r169 (P : OCAParameters) {a b : OmegaTwoIndex} (hab : a ≤ b)
    (x : RO (GoodPrefix (ocaOld P a))) :
    (wholeReduction (R := ocaRules P) b).boolPullback
      ((typedStageMap (ocaStagePolicy P) hab).toFun x) = (ocaTotalMap P a).toFun x :=
  wholeReduction_coherent_r110 hab _

theorem exists_finalWeightedClique_from_activation_r169 (P : OCAParameters)
    (D : (ℕ → ocaB P) → ocaB P) (K : Word × Word → ocaB P) (p : ocaCondition P)
    (a : OmegaTwoIndex) (A : ActivatedAt P D K p a) :
    ∃ q : ocaCondition P, imageCondition q ≤ imageCondition p ∧
      ∃ x : OmegaOneIndex → ℕ → ocaB P, ∃ g : OmegaOneIndex → ocaB P,
        imageCondition q ≤ weightedCliqueValue D K x g := by
  obtain ⟨b,succ⟩ := exists_omegaTwo_actualSuccessor_r169 a
  let hab := ((succ a).mpr le_rfl).le
  let hMap := typedStageMap (ocaStagePolicy P) hab
  let G := (wholeReduction (R := ocaRules P) b).completeValueMap
  let F := ocaTotalMap P a
  let y := A.choice.points
  let k := historyGraphK P a (ocaOld P a) (ocaOldPersistent P a) (ocaOldCCC P a) A.choice.mark.color
  let d (i : OmegaOneIndex) := historySaturated P a (ocaOld P a)
    (ocaOldPersistent P a) (ocaOldCCC P a) (y i)
  let mark := imageCondition A.choice.mark.cond
  have hVal (s : OCALabel) : ocaStagePolicy P a (ocaOld P a) s =
      cliqueAdmitted mark d (fun i j => colorValue k (y i) (y j)) (OrderDual.ofDual s) :=
    congrFun A.admission s
  obtain ⟨r,hRMark,hRCount,hDom,hEdge⟩ := exists_successorClique_below_mark_r124
    (ocaStagePolicy P) succ hVal (ocaPrefixCCC_r164 P b) OmegaOneIndex_not_countable_r61
    (imageCondition_ne_bot_r50 _) A.choice.allPresent
  let q := r.1
  let oldBits := successorCliqueBit (ocaStagePolicy P) a b
  let g (i : OmegaOneIndex) := G.toFun (oldBits i)
  let x (i : OmegaOneIndex) (n : ℕ) := F.toFun (y i n)
  have hCo (u : RO (GoodPrefix (ocaOld P a))) : G.toFun (hMap.toFun u) = F.toFun u :=
    ocaTotal_stageMap_coherent_r169 P hab u
  have hq : G.toFun (imageCondition r) = imageCondition q := wholeReduction_basic_r100 b r
  have hqMark : imageCondition q ≤ F.toFun mark := by
    rw [← hq,← hCo]
    exact G.monotone hRMark
  refine ⟨q,hqMark.trans_eq A.condition_agrees,x,g,?_⟩
  have hD (i : OmegaOneIndex) : g i ≤ D (x i) :=
    ((G.monotone (hDom i)).trans_eq (hCo (d i))).trans (A.domain_included (y i))
  have hGMark (i : OmegaOneIndex) : g i ≤ F.toFun mark := by
    have h := successorCliqueBit_le_vertex_r123 (ocaStagePolicy P) hVal hab i
    exact (G.monotone (h.trans (hMap.monotone inf_le_left))).trans_eq (hCo mark)
  have hK : (fun w => F.toFun (k w)) = K := funext A.code_agrees
  have hE (i j : OmegaOneIndex) (hne : i ≠ j) : g i ⊓ g j ≤ colorValue K (x i) (x j) := by
    change G.toFun (oldBits i) ⊓ G.toFun (oldBits j) ≤ _
    rw [← G.map_inf]
    have h := (G.monotone (hEdge i j hne)).trans_eq (hCo (colorValue k (y i) (y j)))
    rw [map_colorValue_r105,hK] at h
    exact h
  have hSep (i j : OmegaOneIndex) (hne : i ≠ j) :
      g i ⊓ g j ≤ (realEqValue (x i) (x j))ᶜ := by
    apply (inf_le_left.trans (hGMark i)).trans
    apply le_compl_iff_disjoint_right.mpr
    apply disjoint_iff_inf_le.mpr
    change F.toFun mark ⊓ realEqValue (fun n => F.toFun (y i n)) (fun n => F.toFun (y j n)) ≤ ⊥
    rw [← map_realEqValue_r126,← F.map_inf]
    exact (F.monotone (disjoint_iff_inf_le.mp (A.choice.separated i j hne))).trans_eq F.map_bot
  have hCount : imageCondition q ≤ (countableCoverageValue g)ᶜ := by
    rw [← hq]
    exact map_forcing_uncountable_r95 G (booleanCCC_of_conditionCCC_r66 (ocaIterationCCC_r164 P)) oldBits hRCount
  refine le_inf ?_ (le_inf ?_ hCount)
  · exact le_iInf (fun i =>
      (le_materialImp_iff_r126 (imageCondition q) (g i) (D (x i))).mpr
        (inf_le_right.trans (hD i)))
  · apply le_iInf
    intro ij
    apply (le_materialImp_iff_r126 _ _ _).mpr
    exact inf_le_right.trans (le_inf (hE ij.1.1 ij.1.2 ij.2) (hSep ij.1.1 ij.1.2 ij.2))

end CantorCodes
end JSP000933
