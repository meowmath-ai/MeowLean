import JSP000933BlockLift

set_option autoImplicit false

open scoped BigOperators Topology
open Filter

namespace JSP000933

noncomputable section

theorem weightedNull_finset_of_eu (f : EUWeight) (s : Finset ℕ) :
    WeightedNull f.weight (s : Set ℕ) := by
  intro ε hε
  let M : ℝ := ∑ i ∈ s, f.weight i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => f.nonneg i)
  obtain ⟨N, hN⟩ := (tendsto_atTop_atTop.mp f.divergent) (M / ε + 1)
  refine ⟨N, fun p hp => ?_⟩
  have hbound := hN p hp
  have hden : 0 < weightedPrefixSum f.weight p := by
    refine lt_of_lt_of_le ?_ hbound
    positivity
  have hmass : (∑ i ∈ restrictSet (Finset.range p) (s : Set ℕ), f.weight i) ≤ M := by
    have hs : restrictSet (Finset.range p) (s : Set ℕ) ⊆ s := by
      intro i hi
      exact (mem_restrictSet.mp hi).2
    exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => f.nonneg i)
  have hMdiv : M / ε ≤ weightedPrefixSum f.weight p :=
    (le_add_of_nonneg_right zero_le_one).trans hbound
  unfold weightedSetDensity
  apply (div_le_iff₀ hden).mpr
  exact hmass.trans (by
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hMdiv)

theorem weightedClass_eq_of_xor_subset_finset (f : EUWeight) {X Y : Set ℕ} {s : Finset ℕ}
    (hxy : xorSet X Y ⊆ (s : Set ℕ)) :
    weightedClass f.weight f.nonneg X = weightedClass f.weight f.nonneg Y :=
  (weightedClass_eq_iff f.weight f.nonneg X Y).mpr
    (weightedNull_mono f.weight f.nonneg hxy (weightedNull_finset_of_eu f s))

theorem eventual_closed_constraints_stabilize {T : Type*} [TopologicalSpace T]
    [BaireSpace T] [Nonempty T] (C : ℕ → Set T)
    (hclosed : ∀ p, IsClosed (C p))
    (heventually : ∀ x : T, ∃ N : ℕ, ∀ p ≥ N, x ∈ C p) :
    ∃ N : ℕ, (interior (⋂ p : ℕ, ⋂ _ : N ≤ p, C p)).Nonempty := by
  let Ctail (N : ℕ) := ⋂ p : ℕ, ⋂ _ : N ≤ p, C p
  have htail (N : ℕ) : IsClosed (Ctail N) :=
    isClosed_iInter (fun p => isClosed_iInter (fun _ => hclosed p))
  have hcover : (⋃ N : ℕ, Ctail N) = Set.univ := by
    ext x
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      obtain ⟨N, hN⟩ := heventually x
      apply Set.mem_iUnion.mpr
      refine ⟨N, ?_⟩
      simp only [Ctail, Set.mem_iInter]
      exact hN
  exact nonempty_interior_of_iUnion_of_closed htail hcover

def patchProfile {ι : Type*} (s : Finset ι) (p : ↥s → Bool) (x : ι → Bool) : ι → Bool := by
  classical
  exact fun i => if h : i ∈ s then p ⟨i, h⟩ else x i

theorem patchProfile_eq_left {ι : Type*} (s : Finset ι) (p : ↥s → Bool)
    (x : ι → Bool) {i : ι} (hi : i ∈ s) :
    patchProfile s p x i = p ⟨i, hi⟩ := by
  classical
  simp only [patchProfile, dite_eq_left hi]

theorem patchProfile_eq_right {ι : Type*} (s : Finset ι) (p : ↥s → Bool)
    (x : ι → Bool) {i : ι} (hi : i ∉ s) :
    patchProfile s p x i = x i := by
  classical
  simp only [patchProfile, dite_eq_right hi]

theorem patchProfile_over_patch {ι : Type*} (s : Finset ι) (p q : ↥s → Bool) (x : ι → Bool) :
    patchProfile s p (patchProfile s q x) = patchProfile s p x := by
  funext i
  classical
  by_cases hi : i ∈ s
  · simp only [patchProfile_eq_left _ _ _ hi]
  · simp only [patchProfile_eq_right _ _ _ hi]

theorem continuous_patchProfile {ι : Type*} [TopologicalSpace Bool]
    (s : Finset ι) (p : ↥s → Bool) : Continuous (patchProfile s p) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i ∈ s
  · simpa only [patchProfile_eq_left _ _ _ hi] using
      (continuous_const : Continuous (fun _ : ι → Bool => p ⟨i, hi⟩))
  · simpa only [patchProfile_eq_right _ _ _ hi] using
      (continuous_apply i : Continuous (fun x : ι → Bool => x i))

def profileOfSet {A : Set ℕ} (X : Set ℕ) : ↥A → Bool := by
  classical
  exact fun i => decide (i.1 ∈ X)

@[simp] theorem profileOfSet_true {A X : Set ℕ} (i : ↥A) :
    profileOfSet (A := A) X i = true ↔ i.1 ∈ X := by
  classical
  simp [profileOfSet]

theorem subsetOfProfile_profileOfSet {A X : Set ℕ} (hX : X ⊆ A) :
    subsetOfProfile A (profileOfSet X) = X := by
  ext m
  change (∃ h : m ∈ A, profileOfSet X ⟨m, h⟩ = true) ↔ m ∈ X
  exact ⟨fun ⟨h, hp⟩ => (profileOfSet_true (X := X) ⟨m, h⟩).mp hp,
    fun hm => ⟨hX hm, (profileOfSet_true (X := X) ⟨m, hX hm⟩).mpr hm⟩⟩

def outputOfProfile {A : Set ℕ} (L : (↥A → Bool) → (ℕ → Bool)) (x : ↥A → Bool) : Set ℕ :=
  {m | L x m = true}

def LiftEquation (f g : EUWeight) (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    {A : Set ℕ} (L : (↥A → Bool) → (ℕ → Bool)) : Prop :=
  ∀ x, F (weightedClass f.weight f.nonneg (subsetOfProfile A x)) =
    weightedClass g.weight g.nonneg (outputOfProfile L x)

def patchOutputDifference {A : Set ℕ} (L : (↥A → Bool) → (ℕ → Bool))
    (s : Finset ↥A) (p q : ↥s → Bool) (x : ↥A → Bool) : Set ℕ :=
  xorSet (outputOfProfile L (patchProfile s p x)) (outputOfProfile L (patchProfile s q x))

theorem patchOutputDifference_null {f g : EUWeight} {A : Set ℕ}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    {L : (↥A → Bool) → (ℕ → Bool)} (hL : LiftEquation f g F L)
    (s : Finset ↥A) (p q : ↥s → Bool) (x : ↥A → Bool) :
    WeightedNull g.weight (patchOutputDifference L s p q x) := by
  classical
  let X := subsetOfProfile A (patchProfile s p x)
  let Y := subsetOfProfile A (patchProfile s q x)
  let D : Finset ℕ := s.image Subtype.val
  have hfin : xorSet X Y ⊆ (D : Set ℕ) := by
    intro m hm
    by_contra hn
    have hmem : m ∈ X ↔ m ∈ Y := by
      change (∃ hA : m ∈ A, patchProfile s p x ⟨m,hA⟩ = true) ↔
        (∃ hA : m ∈ A, patchProfile s q x ⟨m,hA⟩ = true)
      constructor <;> rintro ⟨hA, htruth⟩
      all_goals
        have hnot : (⟨m, hA⟩ : ↥A) ∉ s := by
          intro hs
          exact hn (Finset.mem_image.mpr ⟨⟨m, hA⟩, hs, rfl⟩)
        refine ⟨hA, ?_⟩
        simpa only [patchProfile_eq_right _ _ _ hnot] using htruth
    change (m ∈ X ∧ m ∉ Y) ∨ (m ∈ Y ∧ m ∉ X) at hm
    exact hm.elim (fun h => h.2 (hmem.mp h.1)) (fun h => h.2 (hmem.mpr h.1))
  have hclasses := congrArg F (weightedClass_eq_of_xor_subset_finset f hfin)
  unfold patchOutputDifference
  apply (weightedClass_eq_iff g.weight g.nonneg _ _).mp
  exact (hL (patchProfile s p x)).symm.trans
    (hclasses.trans (hL (patchProfile s q x)))

private def prefixWordSet (n : ℕ) (x : Fin n → Bool) : Set ℕ :=
  {m | ∃ hm : m < n, x ⟨m, hm⟩ = true}

private theorem prefixXor_consistent (a : ℕ → ℝ) {A : Set ℕ}
    (L : (↥A → Bool) → (ℕ → Bool)) (s : Finset ↥A) (p q : ↥s → Bool)
    (n : ℕ) (x : ↥A → Bool) :
    weightedSetDensity a (patchOutputDifference L s p q x) n =
      weightedSetDensity a (xorSet
        (prefixWordSet n (fun i => L (patchProfile s p x) i.1))
        (prefixWordSet n (fun i => L (patchProfile s q x) i.1))) n := by
  have hcut : restrictSet (Finset.range n) (patchOutputDifference L s p q x) =
      restrictSet (Finset.range n) (xorSet
        (prefixWordSet n (fun i => L (patchProfile s p x) i.1))
        (prefixWordSet n (fun i => L (patchProfile s q x) i.1))) := by
    ext i
    simp only [mem_restrictSet, Finset.mem_range]
    by_cases hi : i < n
    · have hb (r : ↥s → Bool) :
          i ∈ prefixWordSet n (fun j => L (patchProfile s r x) j.1) ↔
            L (patchProfile s r x) i = true :=
        ⟨fun ⟨_, h⟩ => h, fun h => ⟨hi, h⟩⟩
      simp only [hi, true_and, patchOutputDifference, xorSet, Set.mem_union, Set.mem_sdiff,
        outputOfProfile, Set.mem_ofPred_eq, hb]
    · simp only [hi, false_and]
  simp only [weightedSetDensity, hcut]

private theorem isClosed_prefixError {A : Set ℕ} [TopologicalSpace Bool] [DiscreteTopology Bool]
    (a : ℕ → ℝ) (L : (↥A → Bool) → (ℕ → Bool)) (hL : Continuous L)
    (s : Finset ↥A) (p q : ↥s → Bool) (n : ℕ) (ε : ℝ) :
    IsClosed {x | weightedSetDensity a (patchOutputDifference L s p q x) n ≤ ε} := by
  let G (x : ↥A → Bool) : (Fin n → Bool) × (Fin n → Bool) :=
    (fun j => L (patchProfile s p x) j.1, fun j => L (patchProfile s q x) j.1)
  have hG : Continuous G := by
    change Continuous (fun x : ↥A → Bool =>
      ((fun j : Fin n => L (patchProfile s p x) j.1),
        (fun j : Fin n => L (patchProfile s q x) j.1)))
    apply Continuous.prodMk
    · apply continuous_pi
      intro j
      exact (continuous_apply j.1).comp (hL.comp (continuous_patchProfile s p))
    · apply continuous_pi
      intro j
      exact (continuous_apply j.1).comp (hL.comp (continuous_patchProfile s q))
  let T : Set ((Fin n → Bool) × (Fin n → Bool)) :=
    {v | weightedSetDensity a (xorSet (prefixWordSet n v.1) (prefixWordSet n v.2)) n ≤ ε}
  have hEq : {x | weightedSetDensity a (patchOutputDifference L s p q x) n ≤ ε} = G ⁻¹' T := by
    ext x
    change weightedSetDensity a (patchOutputDifference L s p q x) n ≤ ε ↔
      weightedSetDensity a (xorSet
        (prefixWordSet n (fun j => L (patchProfile s p x) j.1))
        (prefixWordSet n (fun j => L (patchProfile s q x) j.1))) n ≤ ε
    rw [prefixXor_consistent a L s p q n x]
  rw [hEq]
  exact (isClosed_discrete T).preimage hG

theorem finitePast_stabilizer {f g : EUWeight} {A : Set ℕ}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    (L : (↥A → Bool) → (ℕ → Bool)) (hc : Continuous L) (hLift : LiftEquation f g F L)
    (s : Finset ↥A) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ u : Finset ↥A, ∃ c : ↥A → Bool,
      ∀ x : ↥A → Bool, (∀ i ∈ u, i ∉ s → x i = c i) →
        ∀ p q : ↥s → Bool, ∀ n ≥ N,
          weightedSetDensity g.weight (patchOutputDifference L s p q x) n ≤ ε := by
  classical
  let E (n : ℕ) : Set (↥A → Bool) := ⋂ p : ↥s → Bool, ⋂ q : ↥s → Bool,
    {x | weightedSetDensity g.weight (patchOutputDifference L s p q x) n ≤ ε}
  have hclosed (n : ℕ) : IsClosed (E n) :=
    isClosed_iInter (fun p => isClosed_iInter (fun q => isClosed_prefixError g.weight L hc s p q n ε))
  have htail (x : ↥A → Bool) : ∃ N : ℕ, ∀ n ≥ N, x ∈ E n := by
    have h (r : (↥s → Bool) × (↥s → Bool)) : ∃ N : ℕ, ∀ n ≥ N,
        weightedSetDensity g.weight (patchOutputDifference L s r.1 r.2 x) n ≤ ε :=
      patchOutputDifference_null (f := f) (g := g) hLift s r.1 r.2 x ε hε
    choose N hN using h
    let M := Finset.univ.sup N
    refine ⟨M, fun n hn => ?_⟩
    simp only [E, Set.mem_iInter, Set.mem_ofPred_eq]
    intro p q
    have hb : N (p, q) ≤ M := Finset.le_sup (Finset.mem_univ (p, q))
    exact hN (p, q) n (hb.trans hn)
  obtain ⟨N, c, hcN⟩ := eventual_closed_constraints_stabilize E hclosed htail
  have hnh : (⋂ n : ℕ, ⋂ _ : N ≤ n, E n) ∈ 𝓝 c := mem_interior_iff_mem_nhds.mp hcN
  rw [nhds_pi] at hnh
  obtain ⟨u, t, ht, hcut⟩ := Filter.mem_pi'.mp hnh
  refine ⟨N, u, c, fun x hx p q n hn => ?_⟩
  let y := patchProfile s (fun i => c i.1) x
  have hy : y ∈ Set.pi (u : Set ↥A) t := by
    intro i hi
    have heq : y i = c i := by
      by_cases h : i ∈ s
      · exact patchProfile_eq_left _ _ _ h
      · exact (patchProfile_eq_right _ _ _ h).trans (hx i hi h)
    change y i ∈ t i
    rw [heq]
    exact mem_of_mem_nhds (ht i)
  have hh := hcut hy
  simp only [Set.mem_iInter, E, Set.mem_ofPred_eq] at hh
  have hout := hh n hn p q
  simpa only [patchOutputDifference, y, patchProfile_over_patch] using hout

def domainPrefix {A : Set ℕ} (n : ℕ) : Finset ↥A := by
  classical
  let v := restrictSet (Finset.range n) A
  exact v.attach.image (fun i => ⟨i.1, (mem_restrictSet.mp i.2).2⟩)

@[simp] theorem mem_domainPrefix {A : Set ℕ} {n : ℕ} {i : ↥A} :
    i ∈ domainPrefix (A := A) n ↔ i.1 < n := by
  classical
  constructor
  · intro hi
    unfold domainPrefix at hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    have hj' := Finset.mem_range.mp (mem_restrictSet.mp j.2).1
    have he : j.1 = i.1 := congrArg Subtype.val hj
    simpa only [he] using hj'
  · intro hi
    let v := restrictSet (Finset.range n) A
    let j : ↥v := ⟨i.1, mem_restrictSet.mpr ⟨Finset.mem_range.mpr hi, i.2⟩⟩
    unfold domainPrefix
    exact Finset.mem_image.mpr ⟨j, by simp, Subtype.ext rfl⟩

def PrefixDetermines {A : Set ℕ} (L : (↥A → Bool) → (ℕ → Bool)) (b m : ℕ) : Prop :=
  ∀ x y : ↥A → Bool, (∀ i : ↥A, i.1 < b → x i = y i) →
    ∀ j < m, L x j = L y j

def MiddleStabilizes {A : Set ℕ} (g : EUWeight) (L : (↥A → Bool) → (ℕ → Bool))
    (a b m : ℕ) (c : ↥A → Bool) (ε : ℝ) : Prop :=
  ∀ x : ↥A → Bool, (∀ i : ↥A, a ≤ i.1 → i.1 < b → x i = c i) →
    ∀ p q : ↥(domainPrefix (A := A) a) → Bool, ∀ n ≥ m,
      weightedSetDensity g.weight (patchOutputDifference L (domainPrefix a) p q x) n ≤ ε

theorem exists_stabilized_cut {f g : EUWeight} {A : Set ℕ}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    (L : (↥A → Bool) → (ℕ → Bool)) (hc : Continuous L) (hLift : LiftEquation f g F L)
    (a m₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ b m : ℕ, ∃ c : ↥A → Bool,
      a ≤ b ∧ m₀ ≤ m ∧ PrefixDetermines L b m ∧ MiddleStabilizes g L a b m c ε := by
  classical
  obtain ⟨N, T, c, hT⟩ := finitePast_stabilizer (f := f) (g := g) L hc hLift
    (domainPrefix (A := A) a) hε
  let m := max N m₀
  obtain ⟨b₀, hb₀⟩ := continuousLift_finite_prefix L hc m
  let b := max b₀ (max a (T.sup (fun i : ↥A => i.1) + 1))
  refine ⟨b, m, c, ?_, le_max_right N m₀, ?_, ?_⟩
  · exact (le_max_left a _).trans (le_max_right b₀ _)
  · intro x y hxy j hj
    exact hb₀ x y (fun i hi => hxy i (hi.trans_le (le_max_left b₀ _))) j hj
  · intro x hx p q n hn
    apply hT x _ p q n ((le_max_left N m₀).trans hn)
    intro i hi hnot
    have hai : a ≤ i.1 := le_of_not_gt (fun hi => hnot (mem_domainPrefix.mpr hi))
    have hsup : i.1 ≤ T.sup (fun i : ↥A => i.1) := Finset.le_sup hi
    have hib : i.1 < b :=
      (Nat.lt_succ_of_le hsup).trans_le ((le_max_right a _).trans (le_max_right b₀ _))
    exact hx i hai hib

theorem exists_selected_block_after {A : Set ℕ} (u : ℕ → Finset ℕ)
    (hud : Pairwise (fun i j => Disjoint (u i) (u j)))
    (hsel : Set.Infinite {i | (u i : Set ℕ) ⊆ A}) (b k : ℕ) :
    ∃ i, k ≤ i ∧ (u i : Set ℕ) ⊆ A ∧ ∀ m ∈ u i, b ≤ m := by
  obtain ⟨N, hN⟩ := eventually_disjoint_finset_of_pairwise u hud (Finset.range b)
  obtain ⟨i, hi, hnot⟩ := hsel.exists_notMem_finset (Finset.range (max N k))
  have hmax : max N k ≤ i := le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
  refine ⟨i, (le_max_right N k).trans hmax, hi, fun m hm => le_of_not_gt ?_⟩
  intro hmb
  exact Finset.disjoint_left.mp (hN i ((le_max_left N k).trans hmax)) hm (Finset.mem_range.mpr hmb)

def blockErrorRate (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

private theorem blockErrorRate_pos (k : ℕ) : 0 < blockErrorRate k := by
  unfold blockErrorRate
  positivity

structure StableStage {A : Set ℕ} (g : EUWeight)
    (L : (↥A → Bool) → (ℕ → Bool)) (u : ℕ → Finset ℕ) (k : ℕ) where
  left : ℕ
  right : ℕ
  out : ℕ
  position : ℕ
  pad : ↥A → Bool
  left_le_right : left ≤ right
  index_ge : k ≤ position
  selected : (u position : Set ℕ) ⊆ A
  source_after : ∀ m ∈ u position, right ≤ m
  determines : PrefixDetermines L right out
  stabilizes : MiddleStabilizes g L left right out pad (blockErrorRate k)

namespace StableStage

def nextLeft {A : Set ℕ} {g : EUWeight} {L : (↥A → Bool) → (ℕ → Bool)}
    {u : ℕ → Finset ℕ} {k : ℕ} (S : StableStage g L u k) : ℕ :=
  max (S.right + 1) ((u S.position).sup id + 1)

theorem right_lt_nextLeft {A : Set ℕ} {g : EUWeight} {L : (↥A → Bool) → (ℕ → Bool)}
    {u : ℕ → Finset ℕ} {k : ℕ} (S : StableStage g L u k) :
    S.right < S.nextLeft :=
  (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem source_before_nextLeft {A : Set ℕ} {g : EUWeight} {L : (↥A → Bool) → (ℕ → Bool)}
    {u : ℕ → Finset ℕ} {k m : ℕ} (S : StableStage g L u k) (hm : m ∈ u S.position) :
    m < S.nextLeft := by
  have h : m ≤ (u S.position).sup id := Finset.le_sup (f := id) hm
  exact (Nat.lt_succ_of_le h).trans_le (le_max_right _ _)

end StableStage

private theorem exists_stage_at {f g : EUWeight} {A : Set ℕ}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    (L : (↥A → Bool) → (ℕ → Bool)) (hc : Continuous L) (hLift : LiftEquation f g F L)
    (u : ℕ → Finset ℕ) (hud : Pairwise (fun i j => Disjoint (u i) (u j)))
    (hsel : Set.Infinite {i | (u i : Set ℕ) ⊆ A}) (k left m₀ : ℕ) :
    ∃ S : StableStage g L u k, S.left = left ∧ m₀ ≤ S.out := by
  obtain ⟨right, out, pad, h₁, h₂, h₃, h₄⟩ := exists_stabilized_cut (f := f) (g := g)
    L hc hLift left m₀ (blockErrorRate_pos k)
  obtain ⟨i, hi, hA, hsource⟩ := exists_selected_block_after u hud hsel right k
  exact ⟨⟨left, right, out, i, pad, h₁, hi, hA, hsource, h₃, h₄⟩, rfl, h₂⟩

private def stageAt {f g : EUWeight} {A : Set ℕ}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    (L : (↥A → Bool) → (ℕ → Bool)) (hc : Continuous L) (hLift : LiftEquation f g F L)
    (u : ℕ → Finset ℕ) (hud : Pairwise (fun i j => Disjoint (u i) (u j)))
    (hsel : Set.Infinite {i | (u i : Set ℕ) ⊆ A}) (k left m₀ : ℕ) :
    {S : StableStage g L u k // S.left = left ∧ m₀ ≤ S.out} :=
  ⟨Classical.choose (exists_stage_at (f := f) (g := g) L hc hLift u hud hsel k left m₀),
    Classical.choose_spec (exists_stage_at (f := f) (g := g) L hc hLift u hud hsel k left m₀)⟩

theorem exists_stable_stage_sequence {f g : EUWeight} {A : Set ℕ}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    (L : (↥A → Bool) → (ℕ → Bool)) (hc : Continuous L) (hLift : LiftEquation f g F L)
    (u : ℕ → Finset ℕ) (hud : Pairwise (fun i j => Disjoint (u i) (u j)))
    (hsel : Set.Infinite {i | (u i : Set ℕ) ⊆ A}) :
    ∃ S : ∀ k, StableStage g L u k, ∀ k,
      (S (k + 1)).left = (S k).nextLeft ∧ (S k).out < (S (k + 1)).out := by
  let get := stageAt (f := f) (g := g) L hc hLift u hud hsel
  let S : ∀ k, StableStage g L u k :=
    Nat.rec (motive := fun k => StableStage g L u k)
      (get 0 0 0).1 (fun k prev => (get (k + 1) prev.nextLeft (prev.out + 1)).1)
  refine ⟨S, fun k => ?_⟩
  have h := (get (k + 1) (S k).nextLeft ((S k).out + 1)).2
  exact ⟨h.1, (Nat.lt_succ_self _).trans_le h.2⟩

namespace StableStage

variable {A : Set ℕ} {g : EUWeight} {L : (↥A → Bool) → (ℕ → Bool)}
  {u : ℕ → Finset ℕ} (S : ∀ k, StableStage g L u k)

def Link : Prop :=
  ∀ k, (S (k + 1)).left = (S k).nextLeft ∧ (S k).out < (S (k + 1)).out

def source (k : ℕ) : Finset ℕ := u (S k).position

def window (k : ℕ) : Finset ℕ := Finset.Ico (S k).out (S (k + 1)).out

def paddedSlice (k : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (S k).left (S k).right).filter
    (fun m => ∃ h : m ∈ A, (S k).pad ⟨m, h⟩ = true)

def padding : Set ℕ := glueBlocks (paddedSlice S)

theorem mem_paddedSlice {k m : ℕ} :
    m ∈ paddedSlice S k ↔ ((S k).left ≤ m ∧ m < (S k).right) ∧
      ∃ h : m ∈ A, (S k).pad ⟨m, h⟩ = true := by
  classical
  simp only [paddedSlice, Finset.mem_filter, Finset.mem_Ico]

theorem left_strictMono (hS : Link S) : StrictMono (fun k => (S k).left) := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [(hS k).1]
  exact (S k).left_le_right.trans_lt (S k).right_lt_nextLeft

theorem out_strictMono (hS : Link S) : StrictMono (fun k => (S k).out) :=
  strictMono_nat_of_lt_succ (fun k => (hS k).2)

theorem right_lt_left_of_lt (hS : Link S) {k j : ℕ} (hkj : k < j) :
    (S k).right < (S j).left := by
  have hnext : (S k).right < (S (k + 1)).left := by
    rw [(hS k).1]
    exact (S k).right_lt_nextLeft
  exact hnext.trans_le ((left_strictMono S hS).monotone (Nat.succ_le_of_lt hkj))

theorem source_lt_left_of_lt (hS : Link S) {k j m : ℕ} (hkj : k < j)
    (hm : m ∈ source S k) : m < (S j).left := by
  have hnext : m < (S (k + 1)).left := by
    rw [(hS k).1]
    exact (S k).source_before_nextLeft hm
  exact hnext.trans_le ((left_strictMono S hS).monotone (Nat.succ_le_of_lt hkj))

theorem source_subset (k : ℕ) : (source S k : Set ℕ) ⊆ A :=
  (S k).selected

theorem padding_subset : padding S ⊆ A := by
  rintro m ⟨k, hm⟩
  obtain ⟨_, h, _⟩ := (mem_paddedSlice S).mp hm
  exact h

theorem glued_source_subset : glueBlocks (source S) ⊆ A := by
  rintro m ⟨k, hm⟩
  exact source_subset S k hm

theorem padding_disjoint_source (hS : Link S) {m : ℕ}
    (hc : m ∈ padding S) (hu : m ∈ glueBlocks (source S)) : False := by
  obtain ⟨j, hj⟩ := hc
  obtain ⟨k, hk⟩ := hu
  have hpad := (mem_paddedSlice S).mp hj
  rcases lt_trichotomy j k with h | rfl | h
  · have hle : (S k).left ≤ m := (S k).left_le_right.trans ((S k).source_after _ hk)
    exact (not_lt_of_ge hle) (hpad.1.2.trans (right_lt_left_of_lt S hS h))
  · exact (not_lt_of_ge ((S j).source_after _ hk)) hpad.1.2
  · exact (not_lt_of_ge hpad.1.1) (source_lt_left_of_lt S hS h hk)

theorem source_pairwise (hS : Link S) :
    Pairwise (fun i j => Disjoint (source S i) (source S j)) := by
  have hleft (i j : ℕ) (hij : i < j) : Disjoint (source S i) (source S j) := by
    apply Finset.disjoint_left.mpr
    intro m hi hj
    exact (not_lt_of_ge ((S j).left_le_right.trans ((S j).source_after _ hj)))
      (source_lt_left_of_lt S hS hij hi)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hleft i j h
  · exact (hleft j i h).symm

theorem window_pairwise (hS : Link S) :
    Pairwise (fun i j => Disjoint (window S i) (window S j)) := by
  have hleft (i j : ℕ) (hij : i < j) : Disjoint (window S i) (window S j) := by
    apply Finset.disjoint_left.mpr
    intro m hi hj
    have hi' := (Finset.mem_Ico.mp (show m ∈ Finset.Ico (S i).out (S (i + 1)).out from hi)).2
    have hj' := (Finset.mem_Ico.mp (show m ∈ Finset.Ico (S j).out (S (j + 1)).out from hj)).1
    have hnext : (S (i + 1)).out ≤ (S j).out :=
      (out_strictMono S hS).monotone (Nat.succ_le_of_lt hij)
    exact (not_lt_of_ge (hnext.trans hj')) hi'
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hleft i j h
  · exact (hleft j i h).symm

theorem padding_mem_iff (hS : Link S) (k : ℕ) (i : ↥A)
    (hl : (S k).left ≤ i.1) (hr : i.1 < (S k).right) :
    i.1 ∈ padding S ↔ (S k).pad i = true := by
  constructor
  · rintro ⟨j, hj⟩
    have hj' := (mem_paddedSlice S).mp hj
    have hEq : j = k := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (not_lt_of_ge hl) (hj'.1.2.trans (right_lt_left_of_lt S hS h))
      · exact (not_lt_of_ge hj'.1.1) (hr.trans (right_lt_left_of_lt S hS h))
    subst j
    obtain ⟨h, hp⟩ := hj'.2
    have hi : (⟨i.1, h⟩ : ↥A) = i := Subtype.ext rfl
    simpa only [hi] using hp
  · intro hp
    exact ⟨k, (mem_paddedSlice S).mpr ⟨⟨hl, hr⟩, i.2, hp⟩⟩

theorem exists_window_of_le (hS : Link S) {m : ℕ} (hm : (S 0).out ≤ m) :
    ∃ k, m ∈ window S k := by
  have hbound (k : ℕ) : k ≤ (S k).out := by
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      have hk := (hS k).2
      omega
  have hex : ∃ n : ℕ, m < (S n).out :=
    ⟨m + 1, (Nat.lt_succ_self m).trans_le (hbound (m + 1))⟩
  let n := Nat.find hex
  have hn : m < (S n).out := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hn
    exact (not_lt_of_ge hm) hn
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hkn : k < n := by rw [hk]; exact Nat.lt_succ_self _
  have hprev : (S k).out ≤ m := le_of_not_gt (Nat.find_min hex hkn)
  refine ⟨k, Finset.mem_Ico.mpr ⟨hprev, ?_⟩⟩
  rw [hk] at hn
  exact hn

end StableStage

private def finiteGlue (D : ℕ → Finset ℕ) (N : ℕ) : Set ℕ :=
  {m | ∃ k < N, m ∈ D k}

private theorem finiteGlue_eq_coe (D : ℕ → Finset ℕ) (N : ℕ) :
    finiteGlue D N = ((Finset.range N).biUnion D : Finset ℕ) := by
  ext m
  constructor
  · rintro ⟨k, hk, hm⟩
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, hm⟩
  · intro hm
    obtain ⟨k, hk, hmk⟩ := Finset.mem_biUnion.mp (show m ∈ (Finset.range N).biUnion D from hm)
    exact ⟨k, Finset.mem_range.mp hk, hmk⟩

private theorem finiteGlue_succ (D : ℕ → Finset ℕ) (N : ℕ) :
    finiteGlue D (N + 1) = finiteGlue D N ∪ (D N : Set ℕ) := by
  ext m
  constructor
  · rintro ⟨k, hk, hm⟩
    by_cases h : k < N
    · exact Or.inl ⟨k, h, hm⟩
    · have hkN : k = N := by omega
      subst k
      exact Or.inr hm
  · rintro (⟨k,hk,hm⟩ | hm)
    · exact ⟨k, hk.trans (Nat.lt_succ_self N), hm⟩
    · exact ⟨N, Nat.lt_succ_self N, hm⟩

private theorem weightedSetDensity_finiteGlue_le (g : EUWeight) (D : ℕ → Finset ℕ)
    (p N : ℕ) :
    weightedSetDensity g.weight (finiteGlue D N) p ≤
      ∑ k ∈ Finset.range N, weightedSetDensity g.weight (D k : Set ℕ) p := by
  induction N with
  | zero =>
    have he : finiteGlue D 0 = ∅ := by
      ext m
      simp [finiteGlue]
    have he' : restrictSet (Finset.range p) (∅ : Set ℕ) = ∅ := by ext m; simp
    simp [he, weightedSetDensity, he']
  | succ N ih =>
    rw [finiteGlue_succ, Finset.sum_range_succ]
    exact (weightedSetDensity_union_le g.weight g.nonneg _ _ p).trans
      (add_le_add_left ih _)

private theorem dyadic_tail_finite (K J : ℕ) :
    (∑ j ∈ Finset.range J, blockErrorRate (K + j)) ≤ 2 * blockErrorRate K := by
  have hs : ∀ N : ℕ,
      (∑ j ∈ Finset.range N, blockErrorRate (K + j)) =
        2 * (blockErrorRate K - blockErrorRate (K + N)) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : blockErrorRate (K + (N + 1)) = blockErrorRate (K + N) / 2 := by
        unfold blockErrorRate
        rw [← Nat.add_assoc, pow_succ]
        ring
      rw [hstep]
      ring
  rw [hs J]
  linarith only [(blockErrorRate_pos (K + J)).le]

private theorem weightedSetDensity_le_of_prefix_subset (g : EUWeight) {A B : Set ℕ} (p : ℕ)
    (h : restrictSet (Finset.range p) A ⊆ restrictSet (Finset.range p) B) :
    weightedSetDensity g.weight A p ≤ weightedSetDensity g.weight B p := by
  unfold weightedSetDensity weightedPrefixSum
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => g.nonneg i))
    (Finset.sum_nonneg (fun i _ => g.nonneg i))

theorem weightedNull_glue_of_dyadic_bounds (g : EUWeight) (D : ℕ → Finset ℕ)
    (hD : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hbound : ∀ k p, weightedSetDensity g.weight (D k : Set ℕ) p ≤ blockErrorRate k) :
    WeightedNull g.weight (glueBlocks D) := by
  intro ε hε
  have hlim : Tendsto blockErrorRate atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hlim (ε / 4) (by positivity)
  have hrate : blockErrorRate K < ε / 4 := by
    have h := hK K le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (blockErrorRate_pos K).le] at h
    exact h
  let H := (Finset.range K).biUnion D
  obtain ⟨P, hP⟩ := weightedNull_finset_of_eu g H (ε / 2) (by positivity)
  refine ⟨P, fun p hp => ?_⟩
  obtain ⟨N, hN⟩ := eventually_disjoint_finset_of_pairwise D hD (Finset.range p)
  let T := finiteGlue (fun j => D (K + j)) N
  have hcut : restrictSet (Finset.range p) (glueBlocks D) ⊆
      restrictSet (Finset.range p) ((H : Set ℕ) ∪ T) := by
    intro m hm
    obtain ⟨hmr, ⟨k, hmk⟩⟩ := mem_restrictSet.mp hm
    apply mem_restrictSet.mpr
    refine ⟨hmr, ?_⟩
    by_cases hk : k < K
    · exact Or.inl (Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hk, hmk⟩)
    · have hkN : k < N := by
        by_contra hbad
        exact Finset.disjoint_left.mp (hN k (le_of_not_gt hbad)) hmk hmr
      have hkK : K ≤ k := le_of_not_gt hk
      refine Or.inr ⟨k - K, by omega, ?_⟩
      have he : K + (k - K) = k := by omega
      simpa only [he] using hmk
  have ht : weightedSetDensity g.weight T p ≤ 2 * blockErrorRate K := by
    calc
      _ ≤ ∑ j ∈ Finset.range N,
          weightedSetDensity g.weight (D (K + j) : Set ℕ) p :=
        weightedSetDensity_finiteGlue_le g (fun j => D (K + j)) p N
      _ ≤ ∑ j ∈ Finset.range N, blockErrorRate (K + j) :=
        Finset.sum_le_sum (fun j _ => hbound (K + j) p)
      _ ≤ _ := dyadic_tail_finite K N
  calc
    _ ≤ weightedSetDensity g.weight ((H : Set ℕ) ∪ T) p :=
      weightedSetDensity_le_of_prefix_subset g p hcut
    _ ≤ weightedSetDensity g.weight (H : Set ℕ) p + weightedSetDensity g.weight T p :=
      weightedSetDensity_union_le g.weight g.nonneg _ _ p
    _ ≤ ε / 2 + 2 * blockErrorRate K := add_le_add (hP p hp) ht
    _ ≤ ε := by linarith only [hrate]

private theorem bool_eq_of_true_iff_r3 {x y : Bool} (h : x = true ↔ y = true) : x = y := by
  cases x <;> cases y <;> simp_all

private theorem patchProfile_self_r3 {ι : Type*} (s : Finset ι) (x : ι → Bool) :
    patchProfile s (fun i : ↥s => x i.1) x = x := by
  classical
  funext i
  by_cases h : i ∈ s
  · exact patchProfile_eq_left _ _ _ h
  · exact patchProfile_eq_right _ _ _ h

def outputForSet {A : Set ℕ} (L : (↥A → Bool) → (ℕ → Bool)) (X : Set ℕ) : Set ℕ :=
  outputOfProfile L (profileOfSet X)

theorem liftEquation_on_sets {f g : EUWeight} {A : Set ℕ}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg}
    {L : (↥A → Bool) → (ℕ → Bool)} (hL : LiftEquation f g F L)
    {X : Set ℕ} (hX : X ⊆ A) :
    F (weightedClass f.weight f.nonneg X) = weightedClass g.weight g.nonneg (outputForSet L X) := by
  simpa only [outputForSet, subsetOfProfile_profileOfSet hX] using hL (profileOfSet X)

namespace StableStage

variable {A : Set ℕ} {g : EUWeight} {L : (↥A → Bool) → (ℕ → Bool)}
  {u : ℕ → Finset ℕ} (S : ∀ k, StableStage g L u k)

theorem middle_not_mem_source (hS : Link S) {k m : ℕ} (ha : (S k).left ≤ m)
    (hb : m < (S k).right) : m ∉ glueBlocks (source S) := by
  rintro ⟨j, hj⟩
  rcases lt_trichotomy j k with h | rfl | h
  · exact (not_lt_of_ge ha) (source_lt_left_of_lt S hS h hj)
  · exact (not_lt_of_ge ((S j).source_after _ hj)) hb
  · have hbound : (S j).left ≤ m := (S j).left_le_right.trans ((S j).source_after _ hj)
    exact (not_lt_of_ge hbound) (hb.trans (right_lt_left_of_lt S hS h))

private theorem right_mono (hS : Link S) : Monotone (fun k => (S k).right) := by
  intro k j hkj
  rcases eq_or_lt_of_le hkj with rfl | h
  · exact le_rfl
  · exact (right_lt_left_of_lt S hS h).le.trans (S j).left_le_right

theorem source_mem_iff_current (hS : Link S) {X : Set ℕ} (hX : X ⊆ glueBlocks (source S))
    (k : ℕ) {m : ℕ} (ha : (S k).left ≤ m) (hb : m < (S (k + 1)).right) :
    m ∈ X ↔ m ∈ restrictSet (source S k) X := by
  constructor
  · intro hm
    obtain ⟨j, hj⟩ := hX hm
    have hEq : j = k := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact (not_lt_of_ge ha) (source_lt_left_of_lt S hS h hj)
      · have hright : (S (k + 1)).right ≤ (S j).right :=
          right_mono S hS (Nat.succ_le_of_lt h)
        exact (not_lt_of_ge (hright.trans ((S j).source_after _ hj))) hb
    subst j
    exact mem_restrictSet.mpr ⟨hj, hm⟩
  · exact fun hm => (mem_restrictSet.mp hm).2

def rawLocal (k : ℕ) (x : Finset ℕ) : Finset ℕ :=
  restrictSet (window S k) (outputForSet L (padding S ∪ (x : Set ℕ)))

def rawEval (X : Set ℕ) : Set ℕ :=
  glueBlocks (fun k => rawLocal S k (restrictSet (source S k) X))

def rawErrorPiece (X : Set ℕ) (k : ℕ) : Finset ℕ :=
  restrictSet (window S k) (xorSet (outputForSet L (padding S ∪ X))
    (outputForSet L (padding S ∪ (restrictSet (source S k) X : Set ℕ))))

theorem rawLocal_subset_window (k : ℕ) (x : Finset ℕ) :
    rawLocal S k x ⊆ window S k := fun _ hm => (mem_restrictSet.mp hm).1

theorem rawErrorPiece_subset_window (X : Set ℕ) (k : ℕ) :
    rawErrorPiece S X k ⊆ window S k := fun _ hm => (mem_restrictSet.mp hm).1

private theorem rawErrorPiece_bound (hS : Link S) {X : Set ℕ}
    (hX : X ⊆ glueBlocks (source S)) (k n : ℕ) :
    weightedSetDensity g.weight (rawErrorPiece S X k : Set ℕ) n ≤ blockErrorRate k := by
  classical
  by_cases hn : (S k).out ≤ n
  · let x := profileOfSet (A := A) (padding S ∪ X)
    let z := profileOfSet (A := A) (padding S ∪ (restrictSet (source S k) X : Set ℕ))
    let s := domainPrefix (A := A) (S k).left
    let p : ↥s → Bool := fun i => x i.1
    let q : ↥s → Bool := fun i => z i.1
    let y := patchProfile s q x
    have hmid (i : ↥A) (hlo : (S k).left ≤ i.1) (hhi : i.1 < (S k).right) :
        x i = (S k).pad i := by
      have hnot : i.1 ∉ X := fun h => middle_not_mem_source S hS hlo hhi (hX h)
      apply bool_eq_of_true_iff_r3
      change profileOfSet (padding S ∪ X) i = true ↔ _
      rw [profileOfSet_true, Set.mem_union, or_iff_left hnot, padding_mem_iff S hS k i hlo hhi]
    have hbefore (i : ↥A) (hi : i.1 < (S (k + 1)).right) : y i = z i := by
      by_cases hlt : i.1 < (S k).left
      · exact patchProfile_eq_left _ _ _ (mem_domainPrefix.mpr hlt)
      · have hnot : i ∉ s := fun h => hlt (mem_domainPrefix.mp h)
        rw [show y i = x i from patchProfile_eq_right _ _ _ hnot]
        apply bool_eq_of_true_iff_r3
        change profileOfSet (padding S ∪ X) i = true ↔
          profileOfSet (padding S ∪ (restrictSet (source S k) X : Set ℕ)) i = true
        simp only [profileOfSet_true, Set.mem_union]
        exact or_congr Iff.rfl (source_mem_iff_current S hS hX k (le_of_not_gt hlt) hi)
    have hOut (m : ℕ) (hm : m < (S (k + 1)).out) : L y m = L z m :=
      (S (k + 1)).determines y z hbefore m hm
    have hxid : patchProfile s p x = x := patchProfile_self_r3 s x
    have hbound := (S k).stabilizes x hmid p q n hn
    have he :
        rawErrorPiece S X k = restrictSet (window S k) (patchOutputDifference L s p q x) := by
      ext m
      simp only [rawErrorPiece, outputForSet, mem_restrictSet, patchOutputDifference, hxid]
      by_cases hm : m ∈ window S k
      · have hlt : m < (S (k + 1)).out :=
          (Finset.mem_Ico.mp (show m ∈ Finset.Ico (S k).out (S (k + 1)).out from hm)).2
        have heq : L (patchProfile s q x) m = L z m := hOut m hlt
        change (m ∈ window S k ∧ m ∈ xorSet (outputOfProfile L x) (outputOfProfile L z)) ↔
          (m ∈ window S k ∧ m ∈ xorSet (outputOfProfile L x)
            (outputOfProfile L (patchProfile s q x)))
        simp only [xorSet, Set.mem_union, Set.mem_sdiff, outputOfProfile, Set.mem_ofPred_eq, heq]
      · simp only [hm, false_and]
    have hsub : (rawErrorPiece S X k : Set ℕ) ⊆ patchOutputDifference L s p q x := by
      intro m hm
      have hm' : m ∈ rawErrorPiece S X k := hm
      rw [he] at hm'
      exact (mem_restrictSet.mp hm').2
    exact (weightedSetDensity_mono g.weight g.nonneg hsub n).trans hbound
  · have hempty : restrictSet (Finset.range n) (rawErrorPiece S X k : Set ℕ) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hmr, hpiece⟩ := mem_restrictSet.mp hm
      have hmwin := rawErrorPiece_subset_window S X k hpiece
      have hlo : (S k).out ≤ m :=
        (Finset.mem_Ico.mp (show m ∈ Finset.Ico (S k).out (S (k + 1)).out from hmwin)).1
      exact hn (hlo.trans (Finset.mem_range.mp hmr).le)
    simp [weightedSetDensity, hempty, (blockErrorRate_pos k).le]

private theorem mem_rawEval_in_window (hS : Link S) (X : Set ℕ) {k m : ℕ}
    (hm : m ∈ window S k) :
    m ∈ rawEval S X ↔ m ∈ rawLocal S k (restrictSet (source S k) X) := by
  have he := restrictSet_glueBlocks (window S)
    (fun k => rawLocal S k (restrictSet (source S k) X))
    (window_pairwise S hS) (fun k => rawLocal_subset_window S k _) k (by rfl : window S k ⊆ window S k)
  rw [Finset.inter_eq_left.mpr (rawLocal_subset_window S k _)] at he
  change m ∈ glueBlocks (fun k => rawLocal S k (restrictSet (source S k) X)) ↔ _
  rw [← he, mem_restrictSet]
  simp only [hm, true_and]

theorem rawEval_error_null (hS : Link S) {X : Set ℕ} (hX : X ⊆ glueBlocks (source S)) :
    WeightedNull g.weight (xorSet (outputForSet L (padding S ∪ X)) (rawEval S X)) := by
  let D := rawErrorPiece S X
  have hD : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    exact Disjoint.mono (rawErrorPiece_subset_window S X i)
      (rawErrorPiece_subset_window S X j) (window_pairwise S hS hij)
  have hnull : WeightedNull g.weight (glueBlocks D) :=
    weightedNull_glue_of_dyadic_bounds g D hD (rawErrorPiece_bound S hS hX)
  let head := Finset.range (S 0).out
  have hcontain : xorSet (outputForSet L (padding S ∪ X)) (rawEval S X) ⊆
      (head : Set ℕ) ∪ glueBlocks D := by
    intro m hm
    by_cases hhead : m < (S 0).out
    · exact Or.inl (Finset.mem_range.mpr hhead)
    · obtain ⟨k, hk⟩ := exists_window_of_le S hS (le_of_not_gt hhead)
      apply Or.inr
      refine ⟨k, mem_restrictSet.mpr ⟨hk, ?_⟩⟩
      have he : m ∈ rawEval S X ↔
          m ∈ outputForSet L (padding S ∪ (restrictSet (source S k) X : Set ℕ)) := by
        rw [mem_rawEval_in_window S hS X hk, rawLocal, mem_restrictSet]
        exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
      simp only [xorSet, Set.mem_union, Set.mem_sdiff] at hm ⊢
      exact hm.elim (fun h => Or.inl ⟨h.1, fun h' => h.2 (he.mpr h')⟩)
        (fun h => Or.inr ⟨he.mp h.1, h.2⟩)
  exact weightedNull_mono g.weight g.nonneg hcontain
    (weightedNull_union g.weight g.nonneg (weightedNull_finset_of_eu g head) hnull)

end StableStage

namespace StableStage

variable {A : Set ℕ} {g : EUWeight} {L : (↥A → Bool) → (ℕ → Bool)}
  {u : ℕ → Finset ℕ} (S : ∀ k, StableStage g L u k)

def clampWindow (k : ℕ) : Finset ℕ :=
  restrictSet (rawLocal S k (source S k)) (outputForSet L (glueBlocks (source S)))

theorem clampWindow_subset_raw (k : ℕ) :
    clampWindow S k ⊆ rawLocal S k (source S k) :=
  fun _ hm => (mem_restrictSet.mp hm).1

theorem clampWindow_subset_window (k : ℕ) : clampWindow S k ⊆ window S k :=
  (clampWindow_subset_raw S k).trans (rawLocal_subset_window S k _)

def blockMap (hS : Link S) : FiniteBlockMap where
  dom := source S
  ran := clampWindow S
  act := fun k x => rawLocal S k x ∩ clampWindow S k
  dom_disjoint := source_pairwise S hS
  ran_disjoint := fun {i j} hij =>
    Disjoint.mono (clampWindow_subset_window S i) (clampWindow_subset_window S j)
      (window_pairwise S hS hij)
  act_subset := by
    intro k x _
    exact Finset.inter_subset_right
  act_top := fun k => Finset.inter_eq_right.mpr (clampWindow_subset_raw S k)

private theorem restrict_full_source (k : ℕ) :
    restrictSet (source S k) (glueBlocks (source S)) = source S k := by
  ext m
  rw [mem_restrictSet]
  exact ⟨fun h => h.1, fun h => ⟨h, ⟨k, h⟩⟩⟩

theorem glue_clampWindow_eq :
    glueBlocks (clampWindow S) =
      rawEval S (glueBlocks (source S)) ∩ outputForSet L (glueBlocks (source S)) := by
  ext m
  constructor
  · rintro ⟨k,hk⟩
    have h := mem_restrictSet.mp (show m ∈ restrictSet (rawLocal S k (source S k))
      (outputForSet L (glueBlocks (source S))) from hk)
    refine ⟨⟨k, ?_⟩, h.2⟩
    change m ∈ rawLocal S k (restrictSet (source S k) (glueBlocks (source S)))
    rw [restrict_full_source S k]
    exact h.1
  · rintro ⟨⟨k,hk⟩, hout⟩
    change m ∈ rawLocal S k (restrictSet (source S k) (glueBlocks (source S))) at hk
    rw [restrict_full_source S k] at hk
    exact ⟨k, mem_restrictSet.mpr ⟨hk, hout⟩⟩

theorem blockMap_eval_eq (hS : Link S) (X : Set ℕ) :
    (blockMap S hS).eval X = rawEval S X ∩ glueBlocks (clampWindow S) := by
  ext m
  constructor
  · rintro ⟨k,hk⟩
    change m ∈ rawLocal S k (restrictSet (source S k) X) ∩ clampWindow S k at hk
    obtain ⟨hr,hc⟩ := Finset.mem_inter.mp hk
    exact ⟨⟨k,hr⟩, ⟨k,hc⟩⟩
  · rintro ⟨⟨j,hj⟩, ⟨k,hk⟩⟩
    have hEq : j = k := by
      by_contra hne
      have hr : m ∈ window S j := rawLocal_subset_window S j _ hj
      have hc : m ∈ window S k := clampWindow_subset_window S k hk
      exact Finset.disjoint_left.mp (window_pairwise S hS hne) hr hc
    subst j
    exact ⟨k, Finset.mem_inter.mpr ⟨hj,hk⟩⟩

theorem blockMap_liftEquation {f : EUWeight}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    (hL : LiftEquation f g F L) (hS : Link S) :
    ∀ X : Set ℕ, X ⊆ glueBlocks (blockMap S hS).dom →
      F (weightedClass f.weight f.nonneg X) =
        weightedClass g.weight g.nonneg ((blockMap S hS).eval X) := by
  let C := padding S
  let B := glueBlocks (source S)
  let qf := weightedClass f.weight f.nonneg
  let qg := weightedClass g.weight g.nonneg
  have hCA : C ⊆ A := padding_subset S
  have hBA : B ⊆ A := glued_source_subset S
  have hRaw (X : Set ℕ) (hX : X ⊆ B) : qg (rawEval S X) = F (qf (C ∪ X)) := by
    have hXA : X ⊆ A := hX.trans hBA
    have hCX : C ∪ X ⊆ A := by
      intro m hm
      rcases hm with hC | hX
      · exact hCA hC
      · exact hXA hX
    have hclose : qg (outputForSet L (C ∪ X)) = qg (rawEval S X) :=
      (weightedClass_eq_iff g.weight g.nonneg _ _).mpr (rawEval_error_null S hS hX)
    exact hclose.symm.trans (liftEquation_on_sets (f := f) (g := g) hL hCX).symm
  have hClamp : qg (glueBlocks (clampWindow S)) = F (qf B) := by
    have hBfull : B ⊆ B := fun _ hm => hm
    have hBlift := liftEquation_on_sets (f := f) (g := g) hL hBA
    have hcap : (C ∪ B) ∩ B = B := Set.union_inter_cancel_right
    change weightedClass g.weight g.nonneg (glueBlocks (clampWindow S)) =
      F (weightedClass f.weight f.nonneg B)
    rw [glue_clampWindow_eq, weightedClass_inter]
    change qg (rawEval S B) * qg (outputForSet L B) = F (qf B)
    rw [hRaw B hBfull, show qg (outputForSet L B) = F (qf B) from hBlift.symm, ← map_mul]
    change F (weightedClass f.weight f.nonneg (C ∪ B) * weightedClass f.weight f.nonneg B) = _
    rw [← weightedClass_inter, hcap]
  intro X hX
  have hXB : X ⊆ B := hX
  have hcap : (C ∪ X) ∩ B = X := by
    ext m
    constructor
    · rintro ⟨h | h, hm⟩
      · exact False.elim (padding_disjoint_source S hS h hm)
      · exact h
    · intro hm
      exact ⟨Or.inr hm, hXB hm⟩
  rw [blockMap_eval_eq, weightedClass_inter]
  change F (qf X) = qg (rawEval S X) * qg (glueBlocks (clampWindow S))
  rw [hRaw X hXB, hClamp, ← map_mul]
  change F (weightedClass f.weight f.nonneg X) =
    F (weightedClass f.weight f.nonneg (C ∪ X) * weightedClass f.weight f.nonneg B)
  rw [← weightedClass_inter, hcap]

end StableStage

theorem exists_finiteBlockMap_of_continuousLift {f g : EUWeight} {A : Set ℕ}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    (hL : HasContinuousLift (f := f) (g := g) F A)
    (u : ℕ → Finset ℕ) (hud : Pairwise (fun i j => Disjoint (u i) (u j)))
    (hsel : Set.Infinite {i | (u i : Set ℕ) ⊆ A}) :
    ∃ B : FiniteBlockMap,
      (∀ k, ∃ i ≥ k, B.dom k = u i) ∧
      ∀ X : Set ℕ, X ⊆ glueBlocks B.dom →
        F (weightedClass f.weight f.nonneg X) = weightedClass g.weight g.nonneg (B.eval X) := by
  letI : TopologicalSpace Bool := ⊥
  letI : DiscreteTopology Bool := ⟨rfl⟩
  unfold HasContinuousLift at hL
  obtain ⟨L, hC, hD⟩ := hL
  have hD' : LiftEquation f g F L := hD
  obtain ⟨S, hlink⟩ := exists_stable_stage_sequence (f := f) (g := g) L hC hD' u hud hsel
  let hS : StableStage.Link S := hlink
  refine ⟨StableStage.blockMap S hS, ?_, StableStage.blockMap_liftEquation S F hD' hS⟩
  intro k
  exact ⟨(S k).position, (S k).index_ge, rfl⟩

theorem CSPD.exists_finiteBlockMap_on_long_source_blocks (hC : CSPD)
    (e : WeightedAlgebra ordinaryEU.weight ordinaryEU.nonneg ≃o
      WeightedAlgebra harmonicEU.weight harmonicEU.nonneg) :
    ∃ B : FiniteBlockMap,
      (∀ k, ∃ i ≥ k, B.dom k = justSourceBlock i) ∧
      ∀ X : Set ℕ, X ⊆ glueBlocks B.dom →
        (ringEquivOfBoolAlgebraOrderIso e).toRingHom
          (weightedClass ordinaryEU.weight ordinaryEU.nonneg X) =
            weightedClass harmonicEU.weight harmonicEU.nonneg (B.eval X) := by
  obtain ⟨A, hsel, hL⟩ := hC.exists_lift_on_long_source_blocks e
  exact exists_finiteBlockMap_of_continuousLift (f := ordinaryEU) (g := harmonicEU)
    (ringEquivOfBoolAlgebraOrderIso e).toRingHom hL justSourceBlock justSourceBlock_pairwise hsel

end

end JSP000933
