import JSP000933FirstColor

open Filter
open scoped Topology

namespace JSP000933

noncomputable section

private theorem take_of_take_r13 {α : Type*} (l : List α) (i j : ℕ) (hij : i ≤ j) :
    (l.take j).take i = l.take i := by
  induction i generalizing j l with
  | zero => simp
  | succ i ih =>
    cases j with
    | zero => omega
    | succ j =>
      cases l with
      | nil => simp
      | cons x l =>
        simp [List.take,ih (l := l) (j := j) (Nat.le_of_succ_le_succ hij)]

private theorem prefixes_of_same_list_comparable_r13 {s t u : List Bool}
    (hs : List.IsPrefix s u) (ht : List.IsPrefix t u) :
    List.IsPrefix s t ∨ List.IsPrefix t s := by
  have hS := List.prefix_iff_eq_take.mp hs
  have hT := List.prefix_iff_eq_take.mp ht
  rcases le_total s.length t.length with h | h
  · apply Or.inl
    apply List.prefix_iff_eq_take.mpr
    rw [hT,take_of_take_r13 u _ _ h]
    exact hS
  · apply Or.inr
    apply List.prefix_iff_eq_take.mpr
    rw [hS,take_of_take_r13 u _ _ h]
    exact hT

def labelsIncompatible (s t : List Bool) : Prop :=
  ¬ List.IsPrefix s t ∧ ¬ List.IsPrefix t s

private theorem common_comparable_is_prefix_r13 {s t u : List Bool}
    (hbad : labelsIncompatible s t)
    (huS : List.IsPrefix u s ∨ List.IsPrefix s u)
    (huT : List.IsPrefix u t ∨ List.IsPrefix t u) :
    List.IsPrefix u s := by
  rcases huS with h | h
  · exact h
  · rcases huT with ht | ht
    · exact False.elim (hbad.1 (h.trans ht))
    · rcases prefixes_of_same_list_comparable_r13 h ht with hh | hh
      · exact False.elim (hbad.1 hh)
      · exact False.elim (hbad.2 hh)

private theorem prefix_indices_finite_r13 (e : ℕ ↪ List Bool) (i : ℕ) :
    {k : ℕ | List.IsPrefix (e k) (e i)}.Finite := by
  let v := (Finset.range ((e i).length + 1)).image (fun j => (e i).take j)
  have hfin : (e ⁻¹' (v : Set (List Bool))).Finite :=
    Set.Finite.preimage_embedding e v.finite_toSet
  apply hfin.subset
  intro k hk
  have htake := List.prefix_iff_eq_take.mp hk
  obtain ⟨s,hs⟩ := hk
  have hlen := congrArg List.length hs
  simp only [List.length_append] at hlen
  change e k ∈ v
  refine Finset.mem_image.mpr ⟨(e k).length,Finset.mem_range.mpr (by omega),htake.symm⟩

private def finiteCrossPrefix (e : ℕ ↪ List Bool) (i : ℕ) : Finset ℕ :=
  (prefix_indices_finite_r13 e i).toFinset

private theorem mem_finiteCrossPrefix_r13 (e : ℕ ↪ List Bool) (i k : ℕ) :
    k ∈ finiteCrossPrefix e i ↔ List.IsPrefix (e k) (e i) := by
  simp [finiteCrossPrefix]

abbrev BoolSeq := ℕ → Bool
abbrev CrossingCube := BoolSeq × BoolSeq × BoolSeq × BoolSeq

def crossingGraphCarrier (A : Set (Set ℕ)) (F : Set ℕ → Set ℕ) : Set CrossingCube :=
  {z | (euProfileSet z.1).Infinite ∧ euProfileSet z.2.1 ⊆ euProfileSet z.1 ∧
    (∃ a ∈ A, euProfileSet z.1 ⊆ a) ∧
    euProfileSet z.2.2.1 = F (euProfileSet z.1) ∧
    euProfileSet z.2.2.2 = F (euProfileSet z.2.1)}

abbrev CrossPoint (A : Set (Set ℕ)) (F : Set ℕ → Set ℕ) := ↥(crossingGraphCarrier A F)

def capOf {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (p : CrossPoint A F) : Set ℕ :=
  euProfileSet p.1.1

def payOf {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (p : CrossPoint A F) : Set ℕ :=
  euProfileSet p.1.2.1

theorem payOf_subset_capOf {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (p : CrossPoint A F) :
    payOf p ⊆ capOf p := p.2.2.1

def NeatFamily (A : Set (Set ℕ)) (e : ℕ ↪ List Bool) : Prop :=
  ∀ a ∈ A, ∀ i ∈ a, ∀ j ∈ a, List.IsPrefix (e i) (e j) ∨ List.IsPrefix (e j) (e i)

private theorem cap_labels_comparable_r13 {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    {e : ℕ ↪ List Bool} (hA : NeatFamily A e) (p : CrossPoint A F)
    {i j : ℕ} (hi : i ∈ capOf p) (hj : j ∈ capOf p) :
    List.IsPrefix (e i) (e j) ∨ List.IsPrefix (e j) (e i) := by
  obtain ⟨a,ha,hsub⟩ := p.2.2.2.1
  exact hA a ha i (hsub hi) j (hsub hj)

theorem crossing_intersection_finite_prefix {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    {e : ℕ ↪ List Bool} (hA : NeatFamily A e) (p q : CrossPoint A F) {i j : ℕ}
    (hi : i ∈ capOf p) (hj : j ∈ capOf q) (hc : labelsIncompatible (e i) (e j)) :
    capOf p ∩ capOf q ⊆ (finiteCrossPrefix e i : Set ℕ) := by
  intro k hk
  exact (mem_finiteCrossPrefix_r13 e i k).mpr (common_comparable_is_prefix_r13 hc
    (cap_labels_comparable_r13 hA p hk.1 hi) (cap_labels_comparable_r13 hA q hk.2 hj))

private theorem finite_cross_test_r13 {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    {e : ℕ ↪ List Bool} (hA : NeatFamily A e) (p q : CrossPoint A F) {i j : ℕ}
    (hi : i ∈ capOf p) (hj : j ∈ capOf q) (hc : labelsIncompatible (e i) (e j)) :
    capOf p ∩ payOf q = capOf q ∩ payOf p ↔
      ∀ k ∈ finiteCrossPrefix e i, (k ∈ capOf p ∩ payOf q ↔ k ∈ capOf q ∩ payOf p) := by
  constructor
  · intro h k _
    rw [h]
  · intro h
    ext k
    have hsub := crossing_intersection_finite_prefix hA p q hi hj hc
    constructor
    · intro hk
      exact (h k (hsub ⟨hk.1,payOf_subset_capOf q hk.2⟩)).mp hk
    · intro hk
      exact (h k (hsub ⟨payOf_subset_capOf p hk.2,hk.1⟩)).mpr hk

private def crossSourceBit {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (p q : CrossPoint A F) (m : ℕ) : Bool :=
  p.1.1 m && q.1.2.1 m

private def crossTargetBit {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (p q : CrossPoint A F) (m : ℕ) : Bool :=
  p.1.2.2.1 m && q.1.2.2.2 m

private def crossTargetError {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (z : CrossPoint A F × CrossPoint A F) : BoolSeq :=
  fun m => crossTargetBit z.1 z.2 m != crossTargetBit z.2 z.1 m

private theorem bool_eq_iff_true_r13 (a b : Bool) : a = b ↔ (a = true ↔ b = true) := by
  cases a <;> cases b <;> decide

private theorem crossSourceBit_iff_r13 {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (p q : CrossPoint A F) (m : ℕ) : crossSourceBit p q m = true ↔ m ∈ capOf p ∩ payOf q := by
  simp [crossSourceBit,capOf,payOf,euProfileSet]

private theorem error_profile_eq_r13 {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (z : CrossPoint A F × CrossPoint A F) :
    euProfileSet (crossTargetError z) =
      xorSet (F (capOf z.1) ∩ F (payOf z.2)) (F (capOf z.2) ∩ F (payOf z.1)) := by
  have h₁ : euProfileSet z.1.1.2.2.1 = F (capOf z.1) := z.1.2.2.2.2.1
  have h₂ : euProfileSet z.1.1.2.2.2 = F (payOf z.1) := z.1.2.2.2.2.2
  have h₃ : euProfileSet z.2.1.2.2.1 = F (capOf z.2) := z.2.2.2.2.2.1
  have h₄ : euProfileSet z.2.1.2.2.2 = F (payOf z.2) := z.2.2.2.2.2.2
  rw [← h₁,← h₂,← h₃,← h₄]
  ext m
  simp only [crossTargetError,crossTargetBit,euProfileSet,xorSet,Set.mem_ofPred_eq,
    Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]
  cases z.1.1.2.2.1 m <;> cases z.1.1.2.2.2 m <;>
    cases z.2.1.2.2.1 m <;> cases z.2.1.2.2.2 m <;> decide

private theorem continuous_bool_zip_r13 {T : Type*} [TopologicalSpace T]
    [TopologicalSpace Bool] [DiscreteTopology Bool] (a b : T → Bool)
    (op : Bool → Bool → Bool) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => op (a x) (b x)) := by
  let f (p : Bool × Bool) := op p.1 p.2
  have hf : Continuous f := continuous_def.mpr (fun _ _ => isOpen_discrete _)
  exact hf.comp (ha.prodMk hb)

private theorem continuous_crossSource_r13 [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (m : ℕ) :
    Continuous (fun z : CrossPoint A F × CrossPoint A F => crossSourceBit z.1 z.2 m) := by
  have h₁ : Continuous (fun z : CrossPoint A F × CrossPoint A F => z.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun z : CrossPoint A F × CrossPoint A F => z.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_bool_zip_r13 _ _ (fun b c => b && c)
    ((continuous_apply m).comp h₁.fst) ((continuous_apply m).comp h₂.snd.fst)

private theorem continuous_crossTarget_r13 [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (m : ℕ) :
    Continuous (fun z : CrossPoint A F × CrossPoint A F => crossTargetBit z.1 z.2 m) := by
  have h₁ : Continuous (fun z : CrossPoint A F × CrossPoint A F => z.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun z : CrossPoint A F × CrossPoint A F => z.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact continuous_bool_zip_r13 _ _ (fun b c => b && c)
    ((continuous_apply m).comp h₁.snd.snd.fst) ((continuous_apply m).comp h₂.snd.snd.snd)

private theorem continuous_crossTargetError_r13 [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} :
    Continuous (crossTargetError (A := A) (F := F)) := by
  apply continuous_pi
  intro m
  have hswap : Continuous (fun z : CrossPoint A F × CrossPoint A F => (z.2,z.1)) :=
    continuous_snd.prodMk continuous_fst
  have h₁ := continuous_crossTarget_r13 (A := A) (F := F) m
  exact continuous_bool_zip_r13 _ _ (fun b c => b != c) h₁ (h₁.comp hswap)

def crossingColor {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} (e : ℕ ↪ List Bool) (g : EUWeight)
    (ε : ℝ) : Set (CrossPoint A F × CrossPoint A F) :=
  {z | (∃ i ∈ capOf z.1, ∃ j ∈ capOf z.2, labelsIncompatible (e i) (e j)) ∧
    capOf z.1 ∩ payOf z.2 = capOf z.2 ∩ payOf z.1 ∧
    xorSet (F (capOf z.1) ∩ F (payOf z.2)) (F (capOf z.2) ∩ F (payOf z.1)) ∉
      euPrefixSmall g (ε + ε)}

private def fixedCrossOpen {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (e : ℕ ↪ List Bool) (g : EUWeight) (ε : ℝ) (i j : ℕ) :
    Set (CrossPoint A F × CrossPoint A F) :=
  {z | i ∈ capOf z.1} ∩
    ({z | j ∈ capOf z.2} ∩
      ({z : CrossPoint A F × CrossPoint A F | labelsIncompatible (e i) (e j)} ∩
        ((⋂ m : ↥(finiteCrossPrefix e i),
          {z | crossSourceBit z.1 z.2 m.1 = crossSourceBit z.2 z.1 m.1}) ∩
            {z | euProfileSet (crossTargetError z) ∉ euPrefixSmall g (ε + ε)})))

private theorem isOpen_fixedCrossOpen_r13 [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (e : ℕ ↪ List Bool) (g : EUWeight) (ε : ℝ) (i j : ℕ) :
    IsOpen (fixedCrossOpen (A := A) (F := F) e g ε i j) := by
  let Q := CrossPoint A F × CrossPoint A F
  have h₁ : Continuous (fun z : Q => z.1.1) := continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun z : Q => z.2.1) := continuous_subtype_val.comp continuous_snd
  have hi : IsOpen {z : Q | i ∈ capOf z.1} :=
    (isOpen_discrete ({true} : Set Bool)).preimage ((continuous_apply i).comp h₁.fst)
  have hj : IsOpen {z : Q | j ∈ capOf z.2} :=
    (isOpen_discrete ({true} : Set Bool)).preimage ((continuous_apply j).comp h₂.fst)
  have hC : IsOpen {z : Q | labelsIncompatible (e i) (e j)} := by
    by_cases h : labelsIncompatible (e i) (e j) <;> simp [h]
  have hTest (m : ℕ) : IsOpen {z : Q | crossSourceBit z.1 z.2 m = crossSourceBit z.2 z.1 m} := by
    have hswap : Continuous (fun z : Q => (z.2,z.1)) := continuous_snd.prodMk continuous_fst
    have ha := continuous_crossSource_r13 (A := A) (F := F) m
    let Δ : Set (Bool × Bool) := {b | b.1 = b.2}
    exact (isOpen_discrete Δ).preimage (ha.prodMk (ha.comp hswap))
  have hSmall : IsOpen {z : Q | euProfileSet (crossTargetError z) ∉ euPrefixSmall g (ε + ε)} :=
    ((isClosed_euPrefixSmall_profiles g (ε + ε)).preimage
      (continuous_crossTargetError_r13 (A := A) (F := F))).isOpen_compl
  exact hi.inter (hj.inter (hC.inter ((isOpen_iInter_of_finite (fun m : ↥(finiteCrossPrefix e i) => hTest m.1)).inter hSmall)))

private theorem crossingColor_eq_union_r13 {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    {e : ℕ ↪ List Bool} (hA : NeatFamily A e) (g : EUWeight) (ε : ℝ) :
    crossingColor (A := A) (F := F) e g ε = ⋃ i : ℕ, ⋃ j : ℕ, fixedCrossOpen e g ε i j := by
  ext z
  constructor
  · intro h
    obtain ⟨⟨i,hi,j,hj,hC⟩,he,hE⟩ := h
    apply Set.mem_iUnion₂.mpr
    refine ⟨i,j,hi,hj,hC,?_,?_⟩
    · apply Set.mem_iInter.mpr
      intro k
      exact (bool_eq_iff_true_r13 _ _).mpr ((crossSourceBit_iff_r13 _ _ _).trans
        (((finite_cross_test_r13 hA z.1 z.2 hi hj hC).mp he k.1 k.2).trans
          (crossSourceBit_iff_r13 _ _ _).symm))
    · change euProfileSet (crossTargetError z) ∉ euPrefixSmall g (ε + ε)
      rwa [error_profile_eq_r13]
  · intro h
    obtain ⟨i,j,hi,hj,hC,hT,hE⟩ := Set.mem_iUnion₂.mp h
    refine ⟨⟨i,hi,j,hj,hC⟩,?_,?_⟩
    · apply (finite_cross_test_r13 hA z.1 z.2 hi hj hC).mpr
      intro k hk
      have he := Set.mem_iInter.mp hT ⟨k,hk⟩
      exact (crossSourceBit_iff_r13 _ _ _).symm.trans
        (((bool_eq_iff_true_r13 _ _).mp he).trans (crossSourceBit_iff_r13 _ _ _))
    · change euProfileSet (crossTargetError z) ∉ euPrefixSmall g (ε + ε) at hE
      rwa [error_profile_eq_r13] at hE

theorem isOpen_crossingColor [TopologicalSpace Bool] [DiscreteTopology Bool]
    {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ} {e : ℕ ↪ List Bool}
    (hA : NeatFamily A e) (g : EUWeight) (ε : ℝ) :
    IsOpen (crossingColor (A := A) (F := F) e g ε) := by
  rw [crossingColor_eq_union_r13 hA]
  exact isOpen_iUnion (fun i => isOpen_iUnion (fun j => isOpen_fixedCrossOpen_r13 e g ε i j))

theorem crossingColor_symmetric {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (e : ℕ ↪ List Bool) (g : EUWeight) (ε : ℝ) {p q : CrossPoint A F}
    (h : (p,q) ∈ crossingColor e g ε) : (q,p) ∈ crossingColor e g ε := by
  obtain ⟨⟨i,hi,j,hj,hC⟩,he,hE⟩ := h
  refine ⟨⟨j,hj,i,hi,hC.2,hC.1⟩,he.symm,?_⟩
  have hx : xorSet (F (capOf q) ∩ F (payOf p)) (F (capOf p) ∩ F (payOf q)) =
      xorSet (F (capOf p) ∩ F (payOf q)) (F (capOf q) ∩ F (payOf p)) := by
    unfold xorSet
    exact Set.union_comm _ _
  simpa only [hx] using hE

theorem crossingColor_irreflexive {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    {e : ℕ ↪ List Bool} (hA : NeatFamily A e) (g : EUWeight) (ε : ℝ) (p : CrossPoint A F) :
    (p,p) ∉ crossingColor e g ε := by
  rintro ⟨⟨i,hi,j,hj,hC⟩,_,_⟩
  exact (cap_labels_comparable_r13 hA p hi hj).elim hC.1 hC.2

theorem crossingColor_countable_clique {A : Set (Set ℕ)} {F : Set ℕ → Set ℕ}
    (e : ℕ ↪ List Bool) (g : EUWeight) {ε : ℝ} (hε : 0 < ε)
    (hMeet : ∀ X Y : Set ℕ, WeightedNull g.weight (xorSet (F X ∩ F Y) (F (X ∩ Y))))
    {C : Set (CrossPoint A F)}
    (hC : ∀ p ∈ C, ∀ q ∈ C, p ≠ q → (p,q) ∈ crossingColor e g ε) :
    C.Countable := by
  apply Set.countable_coe_iff.mp
  apply countable_of_crossing_first_color g F (fun (p : ↥C) => capOf p.1) (fun p => payOf p.1)
  · intro p
    exact payOf_subset_capOf p.1
  · exact hMeet
  · exact hε
  · intro p q h
    exact (hC p.1 p.2 q.1 q.2 (fun he => h (Subtype.ext he))).2

end

end JSP000933
