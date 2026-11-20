import JSP000933CCCCodes
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular

open Cardinal Ordinal Order
open scoped Cardinal

namespace JSP000933
namespace OpenGraphForcing

def OmegaOneIndex : Type := (ℵ₁ : Cardinal).ord.ToType

noncomputable instance : LinearOrder OmegaOneIndex :=
  inferInstanceAs (LinearOrder ((ℵ₁ : Cardinal).ord.ToType))

instance : WellFoundedLT OmegaOneIndex :=
  inferInstanceAs (WellFoundedLT ((ℵ₁ : Cardinal).ord.ToType))

theorem mk_OmegaOneIndex_r61 : Cardinal.mk OmegaOneIndex = ℵ₁ := by
  simp [OmegaOneIndex,Cardinal.mk_toType,Cardinal.card_ord]

theorem OmegaOneIndex_not_countable_r61 : ¬ Countable OmegaOneIndex := by
  intro h
  have hh := Cardinal.mk_le_aleph0_iff.mpr h
  rw [mk_OmegaOneIndex_r61] at hh
  exact (not_lt_of_ge hh) (by
    rw [← Cardinal.succ_aleph0]
    exact Order.lt_succ _)

theorem OmegaOneIndex_initial_countable_r61 (j : OmegaOneIndex) : Countable (↥(Set.Iio j)) := by
  let t := Ordinal.ToType.mk (o := (ℵ₁ : Cardinal).ord)
  let x := t.symm j
  let e (i : ↥(Set.Iio j)) : x.1.ToType :=
    Ordinal.ToType.mk ⟨(t.symm i.1).1,t.symm.strictMono i.2⟩
  have he : Function.Injective e := by
    intro i k h
    apply Subtype.ext
    apply t.symm.injective
    apply Subtype.ext
    exact congrArg (fun y : Set.Iio x.1 => y.val) ((Ordinal.ToType.mk (o := x.1)).injective h)
  have hSm : Cardinal.mk x.1.ToType < ℵ₁ := by
    rw [Cardinal.mk_toType]
    exact Cardinal.lt_ord.mp x.2
  have h : Cardinal.mk (↥(Set.Iio j)) < ℵ₁ :=
    (Function.Embedding.cardinal_le (⟨e,he⟩ : ↥(Set.Iio j) ↪ x.1.ToType)).trans_lt hSm
  rw [← Cardinal.succ_aleph0] at h
  exact Cardinal.mk_le_aleph0_iff.mp (Order.lt_succ_iff.mp h)

theorem OmegaOneIndex_countable_bounded_r61 (S : Set OmegaOneIndex) (hS : S.Countable) :
    ∃ b : OmegaOneIndex, ∀ i ∈ S, i < b := by
  let t := Ordinal.ToType.mk (o := (ℵ₁ : Cardinal).ord)
  let f (i : S) : Ordinal := (t.symm i.1).1 + 1
  have hcof : Cardinal.mk S < (ℵ₁ : Cardinal).ord.cof := by
    rw [Cardinal.isRegular_aleph_one.cof_ord,← Cardinal.succ_aleph0]
    exact (Cardinal.mk_le_aleph0_iff.mpr hS.to_subtype).trans_lt (Order.lt_succ _)
  have hδ : (⨆ i, f i) < (ℵ₁ : Cardinal).ord :=
    Ordinal.iSup_lt_of_lt_cof hcof (fun i =>
      (isSuccLimit_ord Cardinal.isRegular_aleph_one.1).add_one_lt (t.symm i.1).2)
  refine ⟨t ⟨_,hδ⟩,fun i hi => ?_⟩
  have h' : (t.symm i).1 < ⨆ i, f i :=
    ((Order.add_one_le_iff).mp (le_rfl : f ⟨i,hi⟩ ≤ f ⟨i,hi⟩)).trans_le
      (Ordinal.le_iSup f ⟨i,hi⟩)
  have h'' : t.symm i < (⟨_,hδ⟩ : ↥(Set.Iio ((ℵ₁ : Cardinal).ord))) := h'
  have ht := t.strictMono h''
  rw [t.apply_symm_apply i] at ht
  exact ht

theorem mk_realCode_r61 : Cardinal.mk RealCode = 𝔠 := by
  change Cardinal.mk (ℕ → Bool) = 𝔠
  rw [Cardinal.mk_arrow, Cardinal.mk_nat, Cardinal.mk_bool, Cardinal.lift_id, Cardinal.lift_id, Cardinal.two_power_aleph0]

private theorem exists_enum_of_binary_code_r61 {T : Type} [Nonempty T]
    (g : T → RealCode) (hg : Function.Injective g) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ f : OmegaOneIndex → T, Function.Surjective f := by
  classical
  have hCard : Cardinal.mk T ≤ Cardinal.mk OmegaOneIndex := by
    calc
      Cardinal.mk T ≤ Cardinal.mk RealCode := (⟨g,hg⟩ : T ↪ RealCode).cardinal_le
      _ = 𝔠 := mk_realCode_r61
      _ = ℵ₁ := CH
      _ = Cardinal.mk OmegaOneIndex := mk_OmegaOneIndex_r61.symm
  obtain ⟨e⟩ := (Cardinal.le_def _ _).mp hCard
  let x₀ := Classical.choice (inferInstance : Nonempty T)
  let f (i : OmegaOneIndex) : T := if h : ∃ x, e x = i then Classical.choose h else x₀
  refine ⟨f,fun x => ⟨e x,?_⟩⟩
  have hx : ∃ y, e y = e x := ⟨x,rfl⟩
  unfold f
  rw [dite_eq_left hx]
  exact e.injective (Classical.choose_spec hx)

theorem exists_closed_set_binary_code_r61 {X : Type} [TopologicalSpace X] [SecondCountableTopology X] :
    ∃ g : {S : Set X // IsClosed S} → RealCode, Function.Injective g := by
  classical
  obtain ⟨B,hB⟩ := TopologicalSpace.exists_seq_basis X
  let g (S : {S : Set X // IsClosed S}) (n : ℕ) : Bool :=
    decide (B n ⊆ S.1ᶜ)
  refine ⟨g,fun S T he => ?_⟩
  have hSym (n : ℕ) : B n ⊆ S.1ᶜ ↔ B n ⊆ T.1ᶜ := by
    have hh := congrFun he n
    simp only [g] at hh
    constructor
    · intro hs
      apply of_decide_eq_true
      exact hh ▸ decide_eq_true hs
    · intro ht
      apply of_decide_eq_true
      exact hh.symm ▸ decide_eq_true ht
  apply Subtype.ext
  apply compl_injective
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨V,hV,hxV,hVS⟩ := hB.exists_subset_of_mem_open hx S.2.isOpen_compl
    obtain ⟨n,rfl⟩ := hV
    exact ((hSym n).mp hVS) hxV
  · intro x hx
    obtain ⟨V,hV,hxV,hVT⟩ := hB.exists_subset_of_mem_open hx T.2.isOpen_compl
    obtain ⟨n,rfl⟩ := hV
    exact ((hSym n).mpr hVT) hxV

theorem exists_exhaustive_avoidanceSchedule_r61 {X : Type} [TopologicalSpace X] [SecondCountableTopology X]
    (embed : X → RealCode) (hEmbed : Function.Injective embed) (CH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ S : AvoidanceSchedule X OmegaOneIndex,
      (∀ V : Set X, IsClosed V → ∃ e, S.closedCode e = V) ∧
      ∀ n : ℕ, ∀ G : Set (Sample X n), G.Countable → ∃ e, S.graphCode e = ⟨n,G⟩ := by
  letI : Nonempty {S : Set X // IsClosed S} := ⟨⟨∅,isClosed_empty⟩⟩
  letI : Nonempty (AllCountableSamples X) := ⟨⟨0,⟨∅,Set.countable_empty⟩⟩⟩
  obtain ⟨g,hg⟩ := exists_closed_set_binary_code_r61 (X := X)
  obtain ⟨C,hC⟩ := exists_enum_of_binary_code_r61 g hg CH
  obtain ⟨F,hF⟩ := exists_enum_of_binary_code_r61 (codeAllCountableSamples_r60 embed)
    (codeAllCountableSamples_injective_r60 hEmbed) CH
  let S : AvoidanceSchedule X OmegaOneIndex :=
    ⟨fun e => (C e).1,fun e => ⟨(F e).1,(F e).2.1⟩⟩
  refine ⟨S,fun V hV => ?_,fun n G hG => ?_⟩
  · obtain ⟨e,he⟩ := hC ⟨V,hV⟩
    exact ⟨e,congrArg Subtype.val he⟩
  · obtain ⟨e,he⟩ := hF ⟨n,⟨G,hG⟩⟩
    exact ⟨e,congrArg (fun q : AllCountableSamples X => (⟨q.1,q.2.1⟩ : Σ k, Set (Sample X k))) he⟩

end OpenGraphForcing
end JSP000933
