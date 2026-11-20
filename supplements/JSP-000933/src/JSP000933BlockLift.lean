import JSP000933Lemma21

open scoped BigOperators Topology
open Filter

namespace JSP000933

noncomputable section

def restrictSet (s : Finset ℕ) (A : Set ℕ) : Finset ℕ := by
  classical
  exact s.filter (fun m => m ∈ A)

@[simp] theorem mem_restrictSet {s : Finset ℕ} {A : Set ℕ} {m : ℕ} :
    m ∈ restrictSet s A ↔ m ∈ s ∧ m ∈ A := by
  classical
  exact Finset.mem_filter

def xorSet (A B : Set ℕ) : Set ℕ := (A \ B) ∪ (B \ A)

theorem restrictSet_xorSet (s : Finset ℕ) (A B : Set ℕ) :
    restrictSet s (xorSet A B) = xorFinset (restrictSet s A) (restrictSet s B) := by
  ext m
  simp only [mem_restrictSet, xorSet, xorFinset, Set.mem_union, Set.mem_sdiff,
    Finset.mem_union, Finset.mem_sdiff]
  tauto

def weightedPrefixSum (a : ℕ → ℝ) (p : ℕ) : ℝ := ∑ m ∈ Finset.range p, a m

def weightedSetDensity (a : ℕ → ℝ) (A : Set ℕ) (p : ℕ) : ℝ :=
  (∑ m ∈ restrictSet (Finset.range p) A, a m) / weightedPrefixSum a p

def WeightedNull (a : ℕ → ℝ) (A : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, weightedSetDensity a A p ≤ ε

abbrev HarmonicNull (A : Set ℕ) : Prop := WeightedNull harmonicAtom A

private theorem harmonicAtom_pos_r2 (m : ℕ) : 0 < harmonicAtom m := by
  unfold harmonicAtom
  positivity

theorem weightedSetDensity_mono (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    {A B : Set ℕ} (hab : A ⊆ B) (p : ℕ) :
    weightedSetDensity a A p ≤ weightedSetDensity a B p := by
  have hs : restrictSet (Finset.range p) A ⊆ restrictSet (Finset.range p) B := by
    intro m hm
    obtain ⟨hp, hA⟩ := mem_restrictSet.mp hm
    exact mem_restrictSet.mpr ⟨hp, hab hA⟩
  unfold weightedSetDensity
  apply div_le_div_of_nonneg_right
  · exact Finset.sum_le_sum_of_subset_of_nonneg hs (fun m _ _ => ha m)
  · exact Finset.sum_nonneg (fun m _ => ha m)

theorem logPrefixDensity_eq_weightedSetDensity (u : Finset ℕ) (p : ℕ) :
    logPrefixDensity u p = weightedSetDensity harmonicAtom (u : Set ℕ) p := by
  have hu : prefixBlock u p = restrictSet (Finset.range p) (u : Set ℕ) := by
    ext m
    simp only [prefixBlock, Finset.mem_filter, mem_restrictSet, Finset.mem_range,
      Finset.mem_coe]
    exact and_comm
  simp only [logPrefixDensity, logPrefixMass, hu, weightedSetDensity, weightedPrefixSum,
    harmonicSum]

theorem weightedSetDensity_nonneg (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (A : Set ℕ) (p : ℕ) :
    0 ≤ weightedSetDensity a A p := by
  unfold weightedSetDensity weightedPrefixSum
  exact div_nonneg (Finset.sum_nonneg (fun m _ => ha m)) (Finset.sum_nonneg (fun m _ => ha m))

theorem weightedNull_iff_tendsto (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (A : Set ℕ) :
    WeightedNull a A ↔ Tendsto (weightedSetDensity a A) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (by positivity)
    refine ⟨N, fun p hp => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (weightedSetDensity_nonneg a ha A p)]
    exact (hN p hp).trans_lt (by linarith only [hε])
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun p hp => ?_⟩
    have hp' := hN p hp
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (weightedSetDensity_nonneg a ha A p)] at hp'
    exact hp'.le

theorem weightedSetDensity_union_le (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (A B : Set ℕ) (p : ℕ) :
    weightedSetDensity a (A ∪ B) p ≤ weightedSetDensity a A p + weightedSetDensity a B p := by
  let s := restrictSet (Finset.range p) A
  let t := restrictSet (Finset.range p) B
  have hcut : restrictSet (Finset.range p) (A ∪ B) = s ∪ t := by
    ext m
    simp only [s, t, mem_restrictSet, Finset.mem_union, Set.mem_union]
    tauto
  unfold weightedSetDensity
  rw [hcut, ← add_div]
  unfold weightedPrefixSum
  apply div_le_div_of_nonneg_right _ (Finset.sum_nonneg (fun m _ => ha m))
  change (∑ m ∈ s ∪ t, a m) ≤ (∑ m ∈ s, a m) + (∑ m ∈ t, a m)
  calc
    _ ≤ (∑ m ∈ s ∪ t, a m) + (∑ m ∈ s ∩ t, a m) :=
      le_add_of_nonneg_right (Finset.sum_nonneg (fun m _ => ha m))
    _ = _ := Finset.sum_union_inter

theorem weightedNull_empty (a : ℕ → ℝ) : WeightedNull a ∅ := by
  intro ε hε
  have h (p : ℕ) : restrictSet (Finset.range p) (∅ : Set ℕ) = ∅ := by
    ext m
    simp
  exact ⟨0, fun p _ => by simpa [weightedSetDensity, h p] using hε.le⟩

theorem weightedNull_mono (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) {A B : Set ℕ}
    (hsub : A ⊆ B) (hB : WeightedNull a B) : WeightedNull a A := by
  intro ε hε
  obtain ⟨N, hN⟩ := hB ε hε
  exact ⟨N, fun p hp => (weightedSetDensity_mono a ha hsub p).trans (hN p hp)⟩

theorem weightedNull_union (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) {A B : Set ℕ}
    (hA : WeightedNull a A) (hB : WeightedNull a B) : WeightedNull a (A ∪ B) := by
  intro ε hε
  have hh : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := hA (ε / 2) hh
  obtain ⟨M, hM⟩ := hB (ε / 2) hh
  refine ⟨max N M, fun p hp => ?_⟩
  have hsum := add_le_add (hN p ((le_max_left N M).trans hp)) (hM p ((le_max_right N M).trans hp))
  exact (weightedSetDensity_union_le a ha A B p).trans (hsum.trans (by linarith))

abbrev PowerSetRing := AsBoolRing (Set ℕ)

def weightedNullIdeal (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) : Ideal PowerSetRing where
  carrier := {x | WeightedNull a (ofBoolRing x)}
  zero_mem' := weightedNull_empty a
  add_mem' := by
    intro x y hx hy
    change WeightedNull a (ofBoolRing x) at hx
    change WeightedNull a (ofBoolRing y) at hy
    change WeightedNull a (ofBoolRing (x + y))
    rw [ofBoolRing_add]
    apply weightedNull_mono a ha _ (weightedNull_union a ha hx hy)
    intro m hm
    change (m ∈ ofBoolRing x ∧ m ∉ ofBoolRing y) ∨
      (m ∈ ofBoolRing y ∧ m ∉ ofBoolRing x) at hm
    exact hm.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  smul_mem' := by
    intro x y hy
    change WeightedNull a (ofBoolRing y) at hy
    change WeightedNull a (ofBoolRing (x * y))
    rw [ofBoolRing_mul]
    exact weightedNull_mono a ha (fun _ hm => hm.2) hy

abbrev WeightedRing (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) :=
  PowerSetRing ⧸ weightedNullIdeal a ha

instance (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) : BooleanRing (WeightedRing a ha) where
  __ := (inferInstance : Ring (WeightedRing a ha))
  isIdempotentElem := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective (I := weightedNullIdeal a ha) q
    change Ideal.Quotient.mk (weightedNullIdeal a ha) x *
      Ideal.Quotient.mk (weightedNullIdeal a ha) x = Ideal.Quotient.mk (weightedNullIdeal a ha) x
    rw [← map_mul, BooleanRing.mul_self]

abbrev WeightedAlgebra (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) := AsBoolAlg (WeightedRing a ha)

def ringEquivOfBoolAlgebraOrderIso {R S : Type*} [BooleanRing R] [BooleanRing S]
    (e : AsBoolAlg R ≃o AsBoolAlg S) : R ≃+* S := by
  let h : BoundedLatticeHom (AsBoolAlg R) (AsBoolAlg S) :=
    { toFun := e
      map_sup' := e.map_sup
      map_inf' := e.map_inf
      map_top' := e.map_top
      map_bot' := e.map_bot }
  let F := h.asBoolRing
  have hf : Function.Bijective F := by
    change Function.Bijective ((@toBoolRing (AsBoolAlg S)) ∘
      (e : AsBoolAlg R → AsBoolAlg S) ∘ (@ofBoolRing (AsBoolAlg R)))
    exact toBoolRing.bijective.comp (e.bijective.comp ofBoolRing.bijective)
  exact (RingEquiv.asBoolRingAsBoolAlg R).symm.trans
    ((RingEquiv.ofBijective F hf).trans (RingEquiv.asBoolRingAsBoolAlg S))

def weightedClass (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (X : Set ℕ) : WeightedRing a ha :=
  Ideal.Quotient.mk (weightedNullIdeal a ha) (toBoolRing X)

theorem weightedClass_eq_iff (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (X Y : Set ℕ) :
    weightedClass a ha X = weightedClass a ha Y ↔ WeightedNull a (xorSet X Y) := by
  unfold weightedClass
  rw [Ideal.Quotient.eq]
  change WeightedNull a (ofBoolRing (toBoolRing X - toBoolRing Y)) ↔ _
  simp only [ofBoolRing_sub, ofBoolRing_toBoolRing, xorSet, symmDiff]

theorem weightedClass_inter (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (X Y : Set ℕ) :
    weightedClass a ha (X ∩ Y) = weightedClass a ha X * weightedClass a ha Y :=
  map_mul (Ideal.Quotient.mk (weightedNullIdeal a ha)) (toBoolRing X) (toBoolRing Y)

theorem weightedClass_surjective (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) :
    Function.Surjective (weightedClass a ha) := by
  intro q
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (I := weightedNullIdeal a ha) q
  refine ⟨ofBoolRing x, ?_⟩
  simpa only [weightedClass, toBoolRing_ofBoolRing] using hx

structure EUWeight where
  weight : ℕ → ℝ
  pos : ∀ m, 0 < weight m
  divergent : Tendsto (weightedPrefixSum weight) atTop atTop
  negligible : Tendsto (fun n => weight n / weightedPrefixSum weight (n + 1)) atTop (𝓝 0)

theorem EUWeight.nonneg (f : EUWeight) (n : ℕ) : 0 ≤ f.weight n := (f.pos n).le

theorem weightedSetDensity_univ (f : EUWeight) {p : ℕ} (hp : 0 < p) :
    weightedSetDensity f.weight Set.univ p = 1 := by
  have hcut : restrictSet (Finset.range p) (Set.univ : Set ℕ) = Finset.range p := by
    ext m
    simp only [mem_restrictSet, Set.mem_univ, and_true]
  have hsum : 0 < weightedPrefixSum f.weight p := by
    unfold weightedPrefixSum
    exact (f.pos 0).trans_le
      (Finset.single_le_sum (fun m _ => f.nonneg m) (Finset.mem_range.mpr hp))
  simp only [weightedSetDensity, hcut]
  change weightedPrefixSum f.weight p / weightedPrefixSum f.weight p = 1
  exact div_self hsum.ne'

theorem not_weightedNull_univ (f : EUWeight) : ¬ WeightedNull f.weight Set.univ := by
  intro h
  obtain ⟨N, hN⟩ := h (1 / 2) (by norm_num)
  have hsmall := hN (N + 1) (Nat.le_succ N)
  rw [weightedSetDensity_univ f (Nat.zero_lt_succ N)] at hsmall
  norm_num at hsmall

private theorem inverse_succ_tendsto_zero_r2 :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (ε⁻¹)
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlt : ε⁻¹ < (n : ℝ) + 1 := by linarith only [hN, hNn]
  have hpos : 0 < ((n : ℝ) + 1) := by positivity
  have hupper := inv_strictAnti₀ (inv_pos.mpr hε) hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
  simpa only [inv_inv] using hupper

private theorem constantWeight_prefix (p : ℕ) :
    weightedPrefixSum (fun _ => (1 : ℝ)) p = (p : ℝ) := by
  simp [weightedPrefixSum]

def ordinaryEU : EUWeight where
  weight := fun _ => 1
  pos := fun _ => zero_lt_one
  divergent := by
    have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
      apply tendsto_atTop_atTop.mpr
      intro a
      obtain ⟨N, hN⟩ := exists_nat_gt a
      refine ⟨N, fun n hn => hN.le.trans ?_⟩
      exact_mod_cast hn
    have heq : weightedPrefixSum (fun _ => (1 : ℝ)) = fun n : ℕ => (n : ℝ) :=
      funext constantWeight_prefix
    exact heq.symm ▸ hn
  negligible := by
    simp only [constantWeight_prefix, Nat.cast_add, Nat.cast_one, one_div]
    exact inverse_succ_tendsto_zero_r2

private theorem harmonicAtom_tendsto_zero :
    Tendsto harmonicAtom atTop (𝓝 0) := inverse_succ_tendsto_zero_r2

private theorem harmonic_prefix_ge_one (n : ℕ) :
    1 ≤ weightedPrefixSum harmonicAtom (n + 1) := by
  unfold weightedPrefixSum
  have h := Finset.single_le_sum (f := harmonicAtom)
    (fun m _ => (harmonicAtom_pos_r2 m).le) (Finset.mem_range.mpr (Nat.zero_lt_succ n))
  simpa [harmonicAtom] using h

def harmonicEU : EUWeight where
  weight := harmonicAtom
  pos := harmonicAtom_pos_r2
  divergent := by
    unfold weightedPrefixSum harmonicAtom
    simpa only [one_div] using Real.tendsto_sum_range_one_div_nat_succ_atTop
  negligible := by
    refine squeeze_zero ?_ ?_ harmonicAtom_tendsto_zero
    · intro n
      exact div_nonneg (harmonicAtom_pos_r2 n).le (zero_le_one.trans (harmonic_prefix_ge_one n))
    · intro n
      exact div_le_self (harmonicAtom_pos_r2 n).le (harmonic_prefix_ge_one n)

def OrdinaryHarmonicIsomorphic : Prop :=
  Nonempty (WeightedAlgebra ordinaryEU.weight ordinaryEU.nonneg ≃o
    WeightedAlgebra harmonicEU.weight harmonicEU.nonneg)

def subsetOfProfile (A : Set ℕ) (x : ↥A → Bool) : Set ℕ :=
  {m | ∃ h : m ∈ A, x ⟨m, h⟩ = true}

theorem subsetOfProfile_subset (A : Set ℕ) (x : ↥A → Bool) :
    subsetOfProfile A x ⊆ A := by
  rintro m ⟨hm, _⟩
  exact hm

theorem exists_profile_of_subset {A X : Set ℕ} (hX : X ⊆ A) :
    ∃ x : ↥A → Bool, subsetOfProfile A x = X := by
  classical
  refine ⟨fun i => decide (i.1 ∈ X), ?_⟩
  ext m
  constructor
  · rintro ⟨hA, hx⟩
    simpa using hx
  · intro hx
    exact ⟨hX hx, by simp [hx]⟩

def HasContinuousLift {f g : EUWeight}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg) (A : Set ℕ) : Prop := by
  letI : TopologicalSpace Bool := ⊥
  exact ∃ L : (↥A → Bool) → (ℕ → Bool), Continuous L ∧
    ∀ x, F (weightedClass f.weight f.nonneg (subsetOfProfile A x)) =
      weightedClass g.weight g.nonneg {j | L x j = true}

def CSPD : Prop :=
  ∀ f g : EUWeight, ∀ F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg,
    ∀ u : ℕ → Finset ℕ, Pairwise (fun i j => Disjoint (u i) (u j)) →
      ∃ A : Set ℕ, Set.Infinite {i | (u i : Set ℕ) ⊆ A} ∧ HasContinuousLift F A

def justSourceStart : ℕ → ℕ
  | 0 => 2
  | k + 1 => justSourceStart k * 2 ^ justSourceStart k

private theorem justSourceStart_pos (k : ℕ) : 0 < justSourceStart k := by
  induction k with
  | zero => decide
  | succ k ih =>
    change 0 < justSourceStart k * 2 ^ justSourceStart k
    exact Nat.mul_pos ih (pow_pos (by decide : 0 < (2 : ℕ)) _)

private theorem two_le_pow_two_of_pos {n : ℕ} (hn : 0 < n) : 2 ≤ (2 : ℕ) ^ n := by
  cases n with
  | zero => omega
  | succ n =>
    rw [pow_succ']
    have h : 1 ≤ (2 : ℕ) ^ n := Nat.succ_le_of_lt (pow_pos (by decide : 0 < (2 : ℕ)) n)
    simpa only [mul_one] using Nat.mul_le_mul_left 2 h

theorem twice_justSourceStart_le_next (k : ℕ) :
    justSourceStart k * 2 ≤ justSourceStart (k + 1) := by
  change justSourceStart k * 2 ≤ justSourceStart k * 2 ^ justSourceStart k
  exact Nat.mul_le_mul_left _ (two_le_pow_two_of_pos (justSourceStart_pos k))

theorem justSourceStart_strictMono : StrictMono justSourceStart := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hpos := justSourceStart_pos k
  have hmore := twice_justSourceStart_le_next k
  omega

theorem justSourceStart_growth (k : ℕ) : k + 2 ≤ justSourceStart k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h : justSourceStart k < justSourceStart (k + 1) :=
      justSourceStart_strictMono (Nat.lt_succ_self k)
    change k + 1 + 2 ≤ justSourceStart (k + 1)
    omega

def justSourceBlock (k : ℕ) : Finset ℕ :=
  Finset.Ico (justSourceStart k) (justSourceStart (k + 1))

theorem justSourceBlock_pairwise :
    Pairwise (fun i j => Disjoint (justSourceBlock i) (justSourceBlock j)) := by
  have hleft (i j : ℕ) (hij : i < j) : Disjoint (justSourceBlock i) (justSourceBlock j) := by
    rw [Finset.disjoint_left]
    intro m hi hj
    change m ∈ Finset.Ico (justSourceStart i) (justSourceStart (i + 1)) at hi
    change m ∈ Finset.Ico (justSourceStart j) (justSourceStart (j + 1)) at hj
    have hi' := (Finset.mem_Ico.mp hi).2
    have hj' := (Finset.mem_Ico.mp hj).1
    have hnext : justSourceStart (i + 1) ≤ justSourceStart j :=
      justSourceStart_strictMono.monotone (Nat.succ_le_of_lt hij)
    exact (not_lt_of_ge (hnext.trans hj')) hi'
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hleft i j h
  · exact (hleft j i h).symm

theorem justSourceBlock_card_growth (k : ℕ) : k < (justSourceBlock k).card := by
  unfold justSourceBlock
  rw [Nat.card_Ico]
  have hstart := justSourceStart_growth k
  have hmore := twice_justSourceStart_le_next k
  omega

theorem CSPD.exists_lift_on_long_source_blocks (hC : CSPD)
    (e : WeightedAlgebra ordinaryEU.weight ordinaryEU.nonneg ≃o
      WeightedAlgebra harmonicEU.weight harmonicEU.nonneg) :
    ∃ A : Set ℕ, Set.Infinite {i | (justSourceBlock i : Set ℕ) ⊆ A} ∧
      HasContinuousLift (ringEquivOfBoolAlgebraOrderIso e).toRingHom A :=
  hC ordinaryEU harmonicEU (ringEquivOfBoolAlgebraOrderIso e).toRingHom
    justSourceBlock justSourceBlock_pairwise

theorem continuousBool_finite_coordinates {ι : Type*}
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    (f : (ι → Bool) → Bool) (hf : Continuous f) :
    ∃ s : Finset ι, ∀ x y : ι → Bool, (∀ i ∈ s, x i = y i) → f x = f y := by
  classical
  have hlocal (x : ι → Bool) :
      ∃ s : Finset ι, ∀ y : ι → Bool, (∀ i ∈ s, y i = x i) → f y = f x := by
    have hs : ({f x} : Set Bool) ∈ 𝓝 (f x) :=
      (isOpen_discrete _).mem_nhds (Set.mem_singleton _)
    have hpre : f ⁻¹' ({f x} : Set Bool) ∈ 𝓝 x := hf.continuousAt.preimage_mem_nhds hs
    rw [nhds_pi] at hpre
    obtain ⟨s, t, ht, hst⟩ := Filter.mem_pi'.mp hpre
    refine ⟨s, fun y hy => ?_⟩
    have hy' : y ∈ Set.pi (s : Set ι) t := by
      intro i hi
      change y i ∈ t i
      rw [hy i hi]
      exact mem_of_mem_nhds (ht i)
    exact Set.mem_singleton_iff.mp (hst hy')
  choose s hs using hlocal
  let U (x : ι → Bool) : Set (ι → Bool) := Set.pi (s x : Set ι) (fun i => {x i})
  have hU (x : ι → Bool) : U x ∈ 𝓝 x := by
    apply set_pi_mem_nhds (s x).finite_toSet
    intro i _
    exact (isOpen_discrete _).mem_nhds (Set.mem_singleton _)
  obtain ⟨t, ht⟩ := finite_cover_nhds hU
  refine ⟨t.biUnion s, fun x y hxy => ?_⟩
  have hxU : x ∈ ⋃ z ∈ t, U z := by
    rw [ht]
    exact Set.mem_univ _
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxU
  have hx (i : ι) (hi : i ∈ s z) : x i = z i := Set.mem_singleton_iff.mp (hxz i hi)
  have hy (i : ι) (hi : i ∈ s z) : y i = z i := by
    have hit : i ∈ t.biUnion s := Finset.mem_biUnion.mpr ⟨z, hz, hi⟩
    exact (hxy i hit).symm.trans (hx i hi)
  exact (hs z x hx).trans (hs z y hy).symm

theorem continuousLift_finite_prefix {A : Set ℕ}
    [TopologicalSpace Bool] [DiscreteTopology Bool]
    (L : (↥A → Bool) → (ℕ → Bool)) (hL : Continuous L) (m : ℕ) :
    ∃ n : ℕ, ∀ x y : ↥A → Bool, (∀ i : ↥A, i.1 < n → x i = y i) →
      ∀ j < m, L x j = L y j := by
  classical
  have hcoords (j : ℕ) := continuousBool_finite_coordinates (fun x => L x j)
    ((continuous_apply j).comp hL)
  choose s hs using hcoords
  let t := (Finset.range m).biUnion s
  refine ⟨t.sup (fun i : ↥A => i.1) + 1, fun x y hxy j hj => ?_⟩
  apply hs j x y
  intro i hi
  have ht : i ∈ t := Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hi⟩
  have hi' : i.1 ≤ t.sup (fun c : ↥A => c.1) := Finset.le_sup ht
  exact hxy i (Nat.lt_succ_of_le hi')

theorem HasContinuousLift.exists_prefix_determination {f g : EUWeight}
    {F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg} {A : Set ℕ}
    (h : HasContinuousLift F A) :
    ∃ L : (↥A → Bool) → (ℕ → Bool),
      (∀ m : ℕ, ∃ n : ℕ, ∀ x y : ↥A → Bool, (∀ i : ↥A, i.1 < n → x i = y i) →
        ∀ j < m, L x j = L y j) ∧
      ∀ x, F (weightedClass f.weight f.nonneg (subsetOfProfile A x)) =
        weightedClass g.weight g.nonneg {j | L x j = true} := by
  letI : TopologicalSpace Bool := ⊥
  letI : DiscreteTopology Bool := ⟨rfl⟩
  unfold HasContinuousLift at h
  obtain ⟨L, hL, heq⟩ := h
  exact ⟨L, continuousLift_finite_prefix L hL, heq⟩

theorem eventually_disjoint_finset_of_pairwise (v : ℕ → Finset ℕ)
    (hdis : Pairwise (fun i j => Disjoint (v i) (v j))) (s : Finset ℕ) :
    ∃ N : ℕ, ∀ k ≥ N, Disjoint (v k) s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨0, fun _ _ => by simp⟩
  | insert m s _ ih =>
    obtain ⟨N, hN⟩ := ih
    by_cases hm : ∃ i, m ∈ v i
    · obtain ⟨i, hi⟩ := hm
      refine ⟨max N (i + 1), fun k hk => Finset.disjoint_left.mpr ?_⟩
      intro a ha hmem
      rcases Finset.mem_insert.mp hmem with heq | hs
      · subst a
        have hik : i < k := lt_of_lt_of_le (Nat.lt_succ_self i) ((le_max_right N (i + 1)).trans hk)
        exact Finset.disjoint_left.mp (hdis hik.ne.symm) ha hi
      · exact Finset.disjoint_left.mp (hN k ((le_max_left N (i + 1)).trans hk)) ha hs
    · refine ⟨N, fun k hk => Finset.disjoint_left.mpr ?_⟩
      intro a ha hmem
      rcases Finset.mem_insert.mp hmem with heq | hs
      · subst a
        exact hm ⟨k, ha⟩
      · exact Finset.disjoint_left.mp (hN k hk) ha hs

theorem harmonicNull_eventually_small_block (v : ℕ → Finset ℕ)
    (hdis : Pairwise (fun i j => Disjoint (v i) (v j)))
    {A : Set ℕ} (hA : HarmonicNull A) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, logConcentration (restrictSet (v k) A) ≤ ε := by
  have hε' : 0 < ε / 2 := by positivity
  obtain ⟨P, hP⟩ := hA (ε / 2) hε'
  obtain ⟨N, hN⟩ := eventually_disjoint_finset_of_pairwise v hdis (Finset.range P)
  refine ⟨N, ?_⟩
  intro k hk
  apply (logConcentration_le_iff _ _).mpr
  intro p
  by_cases hp : P ≤ p
  · rw [logPrefixDensity_eq_weightedSetDensity]
    have hsub : (restrictSet (v k) A : Set ℕ) ⊆ A := by
      intro m hm
      exact (mem_restrictSet.mp (show m ∈ restrictSet (v k) A from hm)).2
    have hmono := weightedSetDensity_mono harmonicAtom (fun m => (harmonicAtom_pos_r2 m).le) hsub p
    exact hmono.trans ((hP p hp).trans (by linarith only [hε]))
  · have he : prefixBlock (restrictSet (v k) A) p = ∅ := by
      ext m
      simp only [Finset.notMem_empty, iff_false]
      intro hm
      obtain ⟨hmem, hmp⟩ := Finset.mem_filter.mp hm
      have hmv := (mem_restrictSet.mp hmem).1
      have hmr : m ∈ Finset.range P :=
        Finset.mem_range.mpr (hmp.trans (Nat.lt_of_not_ge hp))
      exact Finset.disjoint_left.mp (hN k hk) hmv hmr
    simp [logPrefixDensity, logPrefixMass, he, hε.le]

def glueBlocks (u : ℕ → Finset ℕ) : Set ℕ := {m | ∃ i, m ∈ u i}

theorem restrictSet_glueBlocks (v u : ℕ → Finset ℕ)
    (hdis : Pairwise (fun i j => Disjoint (v i) (v j)))
    (hu : ∀ i, u i ⊆ v i) (k : ℕ) {w : Finset ℕ} (hw : w ⊆ v k) :
    restrictSet w (glueBlocks u) = u k ∩ w := by
  ext m
  rw [mem_restrictSet, Finset.mem_inter]
  constructor
  · rintro ⟨hmw, j, hmj⟩
    have hj : j = k := by
      by_contra hn
      exact Finset.disjoint_left.mp (hdis hn) (hu j hmj) (hw hmw)
    subst j
    exact ⟨hmj, hmw⟩
  · rintro ⟨hmk, hmw⟩
    exact ⟨hmw, ⟨k, hmk⟩⟩

structure FiniteBlockMap where
  dom : ℕ → Finset ℕ
  ran : ℕ → Finset ℕ
  act : ℕ → Finset ℕ → Finset ℕ
  dom_disjoint : Pairwise (fun i j => Disjoint (dom i) (dom j))
  ran_disjoint : Pairwise (fun i j => Disjoint (ran i) (ran j))
  act_subset : ∀ k {x}, x ⊆ dom k → act k x ⊆ ran k
  act_top : ∀ k, act k (dom k) = ran k

namespace FiniteBlockMap

def eval (B : FiniteBlockMap) (A : Set ℕ) : Set ℕ :=
  glueBlocks (fun i => B.act i (restrictSet (B.dom i) A))

theorem restrict_eval (B : FiniteBlockMap) (A : Set ℕ) (k : ℕ) {w : Finset ℕ}
    (hw : w ⊆ B.ran k) :
    restrictSet w (B.eval A) = B.act k (restrictSet (B.dom k) A) ∩ w := by
  apply restrictSet_glueBlocks B.ran _ B.ran_disjoint _ k hw
  intro i
  exact B.act_subset i (fun _ hm => (mem_restrictSet.mp hm).1)

def SurjectiveOnSupport (B : FiniteBlockMap) : Prop :=
  ∀ Z : Set ℕ, Z ⊆ glueBlocks B.ran →
    ∃ X : Set ℕ, X ⊆ glueBlocks B.dom ∧ HarmonicNull (xorSet Z (B.eval X))

theorem eval_domain (B : FiniteBlockMap) : B.eval (glueBlocks B.dom) = glueBlocks B.ran := by
  have hdom (i : ℕ) : restrictSet (B.dom i) (glueBlocks B.dom) = B.dom i := by
    ext m
    rw [mem_restrictSet]
    exact ⟨fun h => h.1, fun hm => ⟨hm, ⟨i, hm⟩⟩⟩
  unfold eval
  apply congrArg glueBlocks
  funext i
  rw [hdom i, B.act_top i]

theorem surjectiveOnSupport_of_quotientLift (B : FiniteBlockMap) {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i)
    (F : WeightedRing a ha →+*
      WeightedRing harmonicAtom (fun i => (harmonicAtom_pos_r2 i).le))
    (hF : Function.Surjective F)
    (hLift : ∀ X : Set ℕ, X ⊆ glueBlocks B.dom →
      F (weightedClass a ha X) =
        weightedClass harmonicAtom (fun i => (harmonicAtom_pos_r2 i).le) (B.eval X)) :
    B.SurjectiveOnSupport := by
  let hpos : ∀ i, 0 ≤ harmonicAtom i := fun i => (harmonicAtom_pos_r2 i).le
  let U := glueBlocks B.dom
  let V := glueBlocks B.ran
  intro Z hZ
  obtain ⟨q, hq⟩ := hF (weightedClass harmonicAtom hpos Z)
  obtain ⟨X, hX⟩ := weightedClass_surjective a ha q
  have hCut : X ∩ U ⊆ glueBlocks B.dom := Set.inter_subset_right
  have hU : U ⊆ glueBlocks B.dom := fun _ hm => hm
  have hUV : B.eval U = V := B.eval_domain
  have hUcls :
      F (weightedClass a ha U) = weightedClass harmonicAtom hpos V :=
    (hLift U hU).trans (congrArg (weightedClass harmonicAtom hpos) hUV)
  have hXZ :
      F (weightedClass a ha (X ∩ U)) = weightedClass harmonicAtom hpos Z := by
    rw [weightedClass_inter, map_mul, hX, hq, hUcls, ← weightedClass_inter]
    have hZV : Z ⊆ V := hZ
    rw [Set.inter_eq_left.mpr hZV]
  refine ⟨X ∩ U, hCut, ?_⟩
  apply (weightedClass_eq_iff harmonicAtom hpos _ _).mp
  exact hXZ.symm.trans (hLift (X ∩ U) hCut)

private theorem windows_disjoint (B : FiniteBlockMap) (w : ℕ → Finset ℕ)
    (hw : ∀ k, w k ⊆ B.ran k) : Pairwise (fun i j => Disjoint (w i) (w j)) := by
  intro i j hij
  exact Disjoint.mono (hw i) (hw j) (B.ran_disjoint hij)

theorem eventually_approx_every_subset (B : FiniteBlockMap)
    (honto : B.SurjectiveOnSupport) (w : ℕ → Finset ℕ) (hw : ∀ k, w k ⊆ B.ran k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ z : Finset ℕ, z ⊆ w k →
      ∃ x : Finset ℕ, x ⊆ B.dom k ∧
        logConcentration (xorFinset z (B.act k x ∩ w k)) ≤ ε := by
  classical
  let Good (k : ℕ) : Prop :=
    ∀ z : Finset ℕ, z ⊆ w k →
      ∃ x : Finset ℕ, x ⊆ B.dom k ∧
        logConcentration (xorFinset z (B.act k x ∩ w k)) ≤ ε
  change ∃ N : ℕ, ∀ k ≥ N, Good k
  by_contra hnever
  have hbadTail (N : ℕ) : ∃ k, N ≤ k ∧ ¬ Good k := by
    by_contra h
    apply hnever
    refine ⟨N, fun k hk => ?_⟩
    by_contra hg
    exact h ⟨k, hk, hg⟩
  have hbadAt (k : ℕ) (hbad : ¬ Good k) :
      ∃ z : Finset ℕ, z ⊆ w k ∧ ∀ x : Finset ℕ, x ⊆ B.dom k →
        ε < logConcentration (xorFinset z (B.act k x ∩ w k)) := by
    by_contra h
    apply hbad
    intro z hz
    by_contra hn
    apply h
    refine ⟨z, hz, fun x hx => ?_⟩
    exact lt_of_not_ge (fun hr => hn ⟨x, hx, hr⟩)
  let z (k : ℕ) : Finset ℕ := if h : Good k then ∅ else Classical.choose (hbadAt k h)
  have hz (k : ℕ) : z k ⊆ w k := by
    by_cases h : Good k
    · simp [z, h]
    · simpa only [z, dite_eq_right h] using (Classical.choose_spec (hbadAt k h)).1
  have hzbad (k : ℕ) (hbad : ¬ Good k) (x : Finset ℕ) (hx : x ⊆ B.dom k) :
      ε < logConcentration (xorFinset (z k) (B.act k x ∩ w k)) := by
    simpa only [z, dite_eq_right hbad] using (Classical.choose_spec (hbadAt k hbad)).2 x hx
  let Z := glueBlocks z
  have hZ : Z ⊆ glueBlocks B.ran := by
    rintro m ⟨i, hi⟩
    exact ⟨i, hw i (hz i hi)⟩
  obtain ⟨X, -, hnull⟩ := honto Z hZ
  obtain ⟨N, hN⟩ := harmonicNull_eventually_small_block w (windows_disjoint B w hw) hnull hε
  obtain ⟨k, hk, hkbad⟩ := hbadTail N
  have hcut : restrictSet (w k) Z = z k := by
    change restrictSet (w k) (glueBlocks z) = z k
    rw [restrictSet_glueBlocks w z (windows_disjoint B w hw) hz k (by rfl),
      Finset.inter_eq_left.mpr (hz k)]
  have hs := hN k hk
  rw [restrictSet_xorSet, hcut, B.restrict_eval X k (hw k)] at hs
  let x := restrictSet (B.dom k) X
  have hx : x ⊆ B.dom k := fun _ hm => (mem_restrictSet.mp hm).1
  exact (not_lt_of_ge hs) (hzbad k hkbad x hx)

def centers (B : FiniteBlockMap) (k : ℕ) (w : Finset ℕ) : Finset (Finset ℕ) :=
  (B.dom k).powerset.image (fun x => B.act k x ∩ w)

theorem centers_card (B : FiniteBlockMap) (k : ℕ) (w : Finset ℕ) :
    (B.centers k w).card ≤ 2 ^ (B.dom k).card := by
  unfold centers
  calc
    _ ≤ (B.dom k).powerset.card := Finset.card_image_le
    _ = _ := Finset.card_powerset _

theorem centers_subset (B : FiniteBlockMap) (k : ℕ) (w y : Finset ℕ)
    (hy : y ∈ B.centers k w) : y ⊆ w := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
  exact Finset.inter_subset_right

theorem st_of_surj_distant_windows (B : FiniteBlockMap) (honto : B.SurjectiveOnSupport)
    (w : ℕ → Finset ℕ) (hw : ∀ k, w k ⊆ B.ran k)
    {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    (hfar : ∀ L : ℕ, ∃ k ≥ L, L < (B.dom k).card ∧
      (∀ m ∈ w k, Real.exp (((B.dom k).card : ℝ) * γ) < (m : ℝ)) ∧
      μ < logConcentration (w k)) :
    STByConcentration := by
  unfold STByConcentration
  refine ⟨γ, μ, hγ, hμ, ?_⟩
  intro ε hε l
  obtain ⟨N, hN⟩ := B.eventually_approx_every_subset honto w hw hε
  obtain ⟨k, hk, hlk, hmin, hmass⟩ := hfar (max N l)
  have hNk : N ≤ k := (le_max_left N l).trans hk
  have hcard : l < (B.dom k).card := (le_max_right N l).trans_lt hlk
  refine ⟨(B.dom k).card, w k, B.centers k (w k), hcard, hmin, hmass,
    B.centers_card k (w k), fun y hy => B.centers_subset k (w k) y hy, ?_⟩
  intro z hz
  obtain ⟨x, hx, hclose⟩ := hN k hNk z hz
  exact ⟨B.act k x ∩ w k, Finset.mem_image.mpr ⟨x, Finset.mem_powerset.mpr hx, rfl⟩, hclose⟩

theorem not_surj_distant_windows (B : FiniteBlockMap)
    (w : ℕ → Finset ℕ) (hw : ∀ k, w k ⊆ B.ran k)
    {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    (hfar : ∀ L : ℕ, ∃ k ≥ L, L < (B.dom k).card ∧
      (∀ m ∈ w k, Real.exp (((B.dom k).card : ℝ) * γ) < (m : ℝ)) ∧
      μ < logConcentration (w k)) :
    ¬ B.SurjectiveOnSupport :=
  fun h => not_STByConcentration (B.st_of_surj_distant_windows h w hw hγ hμ hfar)

theorem no_quotientLift_with_distant_windows (B : FiniteBlockMap) {a : ℕ → ℝ}
    (ha : ∀ i, 0 ≤ a i)
    (F : WeightedRing a ha →+*
      WeightedRing harmonicAtom (fun i => (harmonicAtom_pos_r2 i).le))
    (hF : Function.Surjective F) (w : ℕ → Finset ℕ) (hw : ∀ k, w k ⊆ B.ran k)
    {γ μ : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    (hfar : ∀ L : ℕ, ∃ k ≥ L, L < (B.dom k).card ∧
      (∀ m ∈ w k, Real.exp (((B.dom k).card : ℝ) * γ) < (m : ℝ)) ∧
      μ < logConcentration (w k)) :
    ¬ (∀ X : Set ℕ, X ⊆ glueBlocks B.dom →
      F (weightedClass a ha X) =
        weightedClass harmonicAtom (fun i => (harmonicAtom_pos_r2 i).le) (B.eval X)) := by
  intro hLift
  exact B.not_surj_distant_windows w hw hγ hμ hfar
    (B.surjectiveOnSupport_of_quotientLift ha F hF hLift)

end FiniteBlockMap

end

end JSP000933
