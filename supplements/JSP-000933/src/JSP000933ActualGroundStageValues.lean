import JSP000933ActualUniformFiniteModulus

open scoped Flypitch
open Lattice

namespace JSP000933
namespace SetLanguage

open PositiveForcing BooleanNames CantorCodes

local notation "Word" => CantorCodes.Word

variable {B : Type} [NontrivialCompleteBooleanAlgebra B]

structure ActualGroundStage where
  left : ℕ
  right : ℕ
  out : ℕ
  position : ℕ
  pad : Word

def ActualGroundStage.nextLeft (d : ActualGroundStage) : ℕ :=
  max (d.right+1) ((justSourceBlock d.position).sup id+1)

noncomputable def actualMiddleMatch (x : ℕ → B) (a b : ℕ) (w : Word) : B :=
  ⨅ m : {m : ℕ // a≤ m ∧ m<b}, bitEq (x m.val) (paddedWordBits w m.val)

theorem le_actualMiddleMatch_iff_r351 (s : B) (x : ℕ → B) (a b : ℕ) (w : Word) :
    s≤actualMiddleMatch x a b w ↔
      ∀ m, a≤ m → m<b → s⊓x m=s⊓paddedWordBits w m := by
  constructor
  · intro h m ha hb
    exact (le_bitEq_iff_r126 _ _ _).mp (h.trans (iInf_le (fun j : {j : ℕ // a ≤ j ∧ j < b} => bitEq (x j.val) (paddedWordBits w j.val)) ⟨m,ha,hb⟩))
  · intro h
    exact le_iInf (fun m => (le_bitEq_iff_r126 _ _ _).mpr (h m.val m.property.1 m.property.2))

noncomputable def actualStageGraftValue (L : (ℕ → B) → ℕ → B) (k : ℕ) (d : ActualGroundStage) : B :=
  ⨅ x : ℕ → B, ⨅ u : ℕ → B, ⨅ v : ℕ → B, ⨅ n : {n : ℕ // d.out≤n},
    imp (actualMiddleMatch x d.left d.right d.pad)
      (nameErrorBudget true (dyadicGapDen k) n.val
        (L (actualPrefixPatch d.left u x)) (L (actualPrefixPatch d.left v x)))

noncomputable def actualPrefixMatch (x y : ℕ → B) (b : ℕ) : B :=
  ⨅ m : Fin b, bitEq (x m.val) (y m.val)

theorem le_actualPrefixMatch_iff_r351 (s : B) (x y : ℕ → B) (b : ℕ) :
    s≤actualPrefixMatch x y b ↔ ∀ m<b, s⊓x m=s⊓y m := by
  constructor
  · intro h m hm
    exact (le_bitEq_iff_r126 _ _ _).mp (h.trans (iInf_le (fun j : Fin b => bitEq (x j.val) (y j.val)) ⟨m,hm⟩))
  · intro h
    exact le_iInf (fun m => (le_bitEq_iff_r126 _ _ _).mpr (h m.val m.isLt))

noncomputable def actualStagePrefixValue (L : (ℕ → B) → ℕ → B) (d : ActualGroundStage) : B :=
  ⨅ x : ℕ → B, ⨅ y : ℕ → B,
    imp (actualPrefixMatch x y d.right) (sameOutputPrefixValue L d.out x y)

def ActualGroundStage.admissible (k left out0 : ℕ) (d : ActualGroundStage) : Prop :=
  d.left=left ∧ d.left≤d.right ∧ out0≤d.out ∧ k≤d.position ∧
    ∀ m∈justSourceBlock d.position, d.right≤ m

noncomputable def actualStageValue (c : ℕ → B) (L : (ℕ → B) → ℕ → B) (k left out0 : ℕ)
    (d : ActualGroundStage) : B :=
  crispTruth B (d.admissible k left out0)⊓(actualIncludesBlock c d.position⊓
    (actualStageGraftValue L k d⊓actualStagePrefixValue L d))

theorem actualStageValue_covers_r351 {p : B} (F : CoherentSelectedIso B p)
    (c : ℕ → B) (L : (ℕ → B) → ℕ → B)
    (hC : NamedContinuousOn p L) (hL : ∀ x, LocalEq true p (L x) (F.toName (bitsMeet c x)))
    (hLarge : p≤actualLongBlockLarge c) (k a m₀ : ℕ) :
    p≤⨆ d : ActualGroundStage, actualStageValue c L k a m₀ d := by
  apply le_of_dense_named_refinements_r219
  intro q hq hqp
  obtain ⟨N,w,r,hr,hrq,hR⟩ := exists_actualPast_middle_refinement_r349 F c L hC hL a
    (dyadicGapDen k) (Nat.ne_of_gt (dyadicGapDen_pos_r335 k)) hq hqp
  let n := max N m₀
  obtain ⟨b₀,t,ht,htr,hT⟩ := exists_actualOutputPrefixBound_refinement_r350 hC n hr (hrq.trans hqp)
  let b := max b₀ (max a w.length)
  let M := max b k
  have hB : t≤⨆ i : {i : ℕ // M≤ i}, actualIncludesBlock c i.val :=
    (htr.trans (hrq.trans hqp)).trans (hLarge.trans (iInf_le _ M))
  obtain ⟨i,s,hs,hst,hS⟩ := exists_nonzero_below_choice_r135 t ht _ hB
  let d : ActualGroundStage := ⟨a,b,n,i.val,w⟩
  have hb : b≤justSourceStart i.val :=
    (le_max_left b k).trans (i.property.trans ((Nat.le_add_right i.val 2).trans (justSourceStart_growth i.val)))
  have hD : d.admissible k a m₀ := by
    refine ⟨rfl,(le_max_left _ _).trans (le_max_right _ _),le_max_right _ _,
      (le_max_right b k).trans i.property,?_⟩
    intro m hm
    have he : m∈Finset.Ico (justSourceStart i.val) (justSourceStart (i.val+1)) := hm
    exact hb.trans (Finset.mem_Ico.mp he).1
  have hG : s≤actualStageGraftValue L k d := by
    unfold actualStageGraftValue
    apply le_iInf
    intro x
    apply le_iInf
    intro u
    apply le_iInf
    intro v
    apply le_iInf
    intro j
    apply (le_materialImp_iff_r126 _ _ _).mpr
    let z := s⊓actualMiddleMatch x d.left d.right d.pad
    have hz : z≤r := (show z ≤ s from inf_le_left).trans (hst.trans htr)
    have hM := (le_actualMiddleMatch_iff_r351 z x d.left d.right d.pad).mp inf_le_right
    exact hR z hz x (fun m hA hW => hM m hA
        (hW.trans_le ((le_max_right a w.length).trans (le_max_right b₀ _))))
      u v j.val ((le_max_left N m₀).trans j.property)
  have hP : s≤actualStagePrefixValue L d := by
    unfold actualStagePrefixValue
    apply le_iInf
    intro x
    apply le_iInf
    intro y
    apply (le_materialImp_iff_r126 _ _ _).mpr
    let z := s⊓actualPrefixMatch x y d.right
    have hz : z≤t := (show z ≤ s from inf_le_left).trans hst
    have hc := (le_actualPrefixMatch_iff_r351 z x y d.right).mp inf_le_right
    apply le_iInf
    intro m
    exact (le_bitEq_iff_r126 _ _ _).mpr (hT z hz x y
      (fun j hj => hc j (hj.trans_le (le_max_left b₀ _))) m.val m.isLt)
  have hAd : s≤crispTruth B (d.admissible k a m₀) := by simp [crispTruth,hD]
  exact ⟨s,hs,hst.trans (htr.trans hrq),le_iSup_of_le d (le_inf hAd (le_inf hS (le_inf hG hP)))⟩

end SetLanguage
end JSP000933
