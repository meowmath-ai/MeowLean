import JSP000933CSPD

open scoped BigOperators

namespace JSP000933

noncomputable section

def harmonicIntegerWeight (p m : ℕ) : ℕ := p.factorial / (m + 1)

def harmonicIntegerMass (A : Set ℕ) (p : ℕ) : ℕ :=
  ∑ m ∈ restrictSet (Finset.range p) A, harmonicIntegerWeight p m

def ordinaryIntegerMass (A : Set ℕ) (p : ℕ) : ℕ :=
  (restrictSet (Finset.range p) A).card

def OrdinaryArithmeticNull (A : Set ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ p ≥ N, k * ordinaryIntegerMass A p ≤ p

def HarmonicArithmeticNull (A : Set ℕ) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ p ≥ N,
    k * harmonicIntegerMass A p ≤ harmonicIntegerMass Set.univ p

theorem harmonicIntegerWeight_cast {p m : ℕ} (hm : m < p) :
    (harmonicIntegerWeight p m : ℝ) = (p.factorial : ℝ) * harmonicAtom m := by
  have hdvd : m + 1 ∣ p.factorial := Nat.dvd_factorial (Nat.succ_pos m) (Nat.succ_le_of_lt hm)
  have hn : (p.factorial / (m + 1)) * (m + 1) = p.factorial := Nat.div_mul_cancel hdvd
  have hr : (harmonicIntegerWeight p m : ℝ) * ((m : ℝ) + 1) = (p.factorial : ℝ) := by
    unfold harmonicIntegerWeight
    exact_mod_cast hn
  have hd : 0 < (m : ℝ) + 1 := by positivity
  unfold harmonicAtom
  rw [← div_eq_mul_inv]
  exact (eq_div_iff hd.ne').mpr hr

theorem harmonicIntegerMass_cast (A : Set ℕ) (p : ℕ) :
    (harmonicIntegerMass A p : ℝ) =
      (p.factorial : ℝ) * ∑ m ∈ restrictSet (Finset.range p) A, harmonicAtom m := by
  unfold harmonicIntegerMass
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  exact harmonicIntegerWeight_cast (Finset.mem_range.mp (mem_restrictSet.mp hm).1)

private theorem harmonicIntegerMass_cast_univ (p : ℕ) :
    (harmonicIntegerMass Set.univ p : ℝ) = (p.factorial : ℝ) * harmonicSum p := by
  have hr : restrictSet (Finset.range p) (Set.univ : Set ℕ) = Finset.range p := by
    ext m
    simp [mem_restrictSet]
  rw [harmonicIntegerMass_cast, hr, harmonicSum]

private theorem ratio_le_inverse_iff_r6 {S D k : ℝ} (hD : 0 < D) (hk : 0 < k) :
    S / D ≤ k⁻¹ ↔ k * S ≤ D := by
  rw [div_le_iff₀ hD]
  have he : k⁻¹ * D = D / k := by rw [div_eq_mul_inv, mul_comm]
  rw [he, le_div_iff₀ hk, mul_comm S k]

theorem ordinaryArithmeticBudget_iff (A : Set ℕ) {k p : ℕ} (hk : 0 < k) (hp : 0 < p) :
    k * ordinaryIntegerMass A p ≤ p ↔
      weightedSetDensity ordinaryEU.weight A p ≤ (k : ℝ)⁻¹ := by
  have hK : 0 < (k : ℝ) := by exact_mod_cast hk
  have hP : 0 < (p : ℝ) := by exact_mod_cast hp
  have he : weightedSetDensity ordinaryEU.weight A p = (ordinaryIntegerMass A p : ℝ) / p := by
    simp [weightedSetDensity,weightedPrefixSum,ordinaryEU,ordinaryIntegerMass]
  rw [he, ratio_le_inverse_iff_r6 hP hK]
  constructor <;> intro h <;> exact_mod_cast h

private theorem harmonicSum_pos_r6 {p : ℕ} (hp : 0 < p) : 0 < harmonicSum p := by
  have h := Finset.single_le_sum (f := harmonicAtom)
    (fun m _ => by unfold harmonicAtom; positivity) (Finset.mem_range.mpr hp)
  have h' : 1 ≤ harmonicSum p := by simpa [harmonicAtom,harmonicSum] using h
  exact zero_lt_one.trans_le h'

theorem harmonicArithmeticBudget_iff (A : Set ℕ) {k p : ℕ} (hk : 0 < k) (hp : 0 < p) :
    k * harmonicIntegerMass A p ≤ harmonicIntegerMass Set.univ p ↔
      weightedSetDensity harmonicEU.weight A p ≤ (k : ℝ)⁻¹ := by
  have hK : 0 < (k : ℝ) := by exact_mod_cast hk
  have hF : 0 < (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  have hpH : 0 < harmonicSum p := harmonicSum_pos_r6 hp
  let S : ℝ := ∑ m ∈ restrictSet (Finset.range p) A, harmonicAtom m
  have he : weightedSetDensity harmonicEU.weight A p = S / harmonicSum p := rfl
  rw [he, ratio_le_inverse_iff_r6 hpH hK]
  calc
    _ ↔ (k : ℝ) * (harmonicIntegerMass A p : ℝ) ≤ (harmonicIntegerMass Set.univ p : ℝ) := by
      constructor <;> intro h <;> exact_mod_cast h
    _ ↔ _ := by
      rw [harmonicIntegerMass_cast_univ, harmonicIntegerMass_cast]
      change (k : ℝ) * ((p.factorial : ℝ) * S) ≤ (p.factorial : ℝ) * harmonicSum p ↔
        (k : ℝ) * S ≤ harmonicSum p
      rw [show (k : ℝ) * ((p.factorial : ℝ) * S) = (p.factorial : ℝ) * ((k : ℝ) * S)
        by ring, mul_le_mul_iff_right₀ hF]

private theorem weightedNull_iff_inverse_nat_test_r6 (a : ℕ → ℝ) (A : Set ℕ) :
    WeightedNull a A ↔ ∀ k : ℕ, 0 < k → ∃ N : ℕ, ∀ p ≥ N,
      weightedSetDensity a A p ≤ (k : ℝ)⁻¹ := by
  constructor
  · intro h k hk
    have hz : 0 < (k : ℝ) := by exact_mod_cast hk
    exact h _ (inv_pos.mpr hz)
  · intro h ε hε
    obtain ⟨k,hk⟩ := exists_nat_gt (1 / ε)
    have hz : (0 : ℝ) < 1 / ε := by positivity
    have hkr : 0 < (k : ℝ) := hz.trans hk
    have hk₀ : 0 < k := by exact_mod_cast hkr
    obtain ⟨N,hN⟩ := h k hk₀
    refine ⟨N, fun p hp => (hN p hp).trans ?_⟩
    simpa only [one_div,inv_inv] using inv_anti₀ hz hk.le

theorem ordinaryArithmeticNull_iff (A : Set ℕ) :
    OrdinaryArithmeticNull A ↔ WeightedNull ordinaryEU.weight A := by
  rw [weightedNull_iff_inverse_nat_test_r6]
  constructor <;> intro h k hk <;> obtain ⟨N,hN⟩ := h k hk
  · refine ⟨max N 1,fun p hp => ?_⟩
    have hp₀ : 0 < p := (le_max_right N 1).trans hp
    exact (ordinaryArithmeticBudget_iff A hk hp₀).mp (hN p ((le_max_left N 1).trans hp))
  · refine ⟨max N 1,fun p hp => ?_⟩
    have hp₀ : 0 < p := (le_max_right N 1).trans hp
    exact (ordinaryArithmeticBudget_iff A hk hp₀).mpr (hN p ((le_max_left N 1).trans hp))

theorem harmonicArithmeticNull_iff (A : Set ℕ) :
    HarmonicArithmeticNull A ↔ WeightedNull harmonicEU.weight A := by
  rw [weightedNull_iff_inverse_nat_test_r6]
  constructor <;> intro h k hk <;> obtain ⟨N,hN⟩ := h k hk
  · refine ⟨max N 1,fun p hp => ?_⟩
    have hp₀ : 0 < p := (le_max_right N 1).trans hp
    exact (harmonicArithmeticBudget_iff A hk hp₀).mp (hN p ((le_max_left N 1).trans hp))
  · refine ⟨max N 1,fun p hp => ?_⟩
    have hp₀ : 0 < p := (le_max_right N 1).trans hp
    exact (harmonicArithmeticBudget_iff A hk hp₀).mpr (hN p ((le_max_left N 1).trans hp))

def weightedAlgebraClass (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (A : Set ℕ) :
    WeightedAlgebra a ha :=
  toBoolAlg (weightedClass a ha A)

theorem weightedAlgebraClass_surjective (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) :
    Function.Surjective (weightedAlgebraClass a ha) :=
  toBoolAlg.surjective.comp (weightedClass_surjective a ha)

theorem weightedAlgebraClass_le_iff (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (A B : Set ℕ) :
    weightedAlgebraClass a ha A ≤ weightedAlgebraClass a ha B ↔ WeightedNull a (A \ B) := by
  unfold weightedAlgebraClass
  rw [← inf_eq_left, ← toBoolAlg_mul, ← weightedClass_inter, toBoolAlg_inj, weightedClass_eq_iff]
  have he : xorSet (A ∩ B) A = A \ B := by
    ext m
    simp only [xorSet, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  rw [he]

def RepresentativeIsoGraph {X Y : Type*}
    (leX : X → X → Prop) (leY : Y → Y → Prop) (G : Set (X × Y)) : Prop :=
  (∀ x, ∃ y, (x,y) ∈ G) ∧ (∀ y, ∃ x, (x,y) ∈ G) ∧
    ∀ x x' y y', (x,y) ∈ G → (x',y') ∈ G → (leX x x' ↔ leY y y')

theorem orderIso_iff_exists_representativeIsoGraph {X Y S T : Type*}
    [PartialOrder S] [PartialOrder T] (q : X → S) (r : Y → T)
    (hq : Function.Surjective q) (hr : Function.Surjective r) :
    Nonempty (S ≃o T) ↔ ∃ G : Set (X × Y),
      RepresentativeIsoGraph (fun x x' => q x ≤ q x') (fun y y' => r y ≤ r y') G := by
  classical
  constructor
  · rintro ⟨e⟩
    refine ⟨{xy | r xy.2 = e (q xy.1)}, ?_, ?_, ?_⟩
    · intro x
      exact hr (e (q x))
    · intro y
      obtain ⟨a,ha⟩ := e.surjective (r y)
      obtain ⟨x,hx⟩ := hq a
      exact ⟨x, by change r y = e (q x); rw [hx,ha]⟩
    · intro x x' y y' hx hx'
      change r y = e (q x) at hx
      change r y' = e (q x') at hx'
      change q x ≤ q x' ↔ r y ≤ r y'
      rw [hx,hx',e.le_iff_le]
  · rintro ⟨G,hG,hO,hR⟩
    have hq' : ∀ a : S, ∃ x : X, q x = a := hq
    choose sq hsq using hq'
    choose t ht using hG
    let f (a : S) := r (t (sq a))
    have hRel (a b : S) : a ≤ b ↔ f a ≤ f b := by
      have h := hR (sq a) (sq b) (t (sq a)) (t (sq b)) (ht _) (ht _)
      change q (sq a) ≤ q (sq b) ↔ f a ≤ f b at h
      rw [hsq a, hsq b] at h
      exact h
    have hInj : Function.Injective f := by
      intro a b hab
      apply le_antisymm
      · exact (hRel a b).mpr (le_of_eq hab)
      · exact (hRel b a).mpr (le_of_eq hab.symm)
    have hSurj : Function.Surjective f := by
      intro b
      obtain ⟨y,hy⟩ := hr b
      obtain ⟨x,hx⟩ := hO y
      let a := q x
      refine ⟨a,?_⟩
      have he : q (sq a) = q x := hsq a
      have h₁ : f a ≤ r y :=
        (hR (sq a) x (t (sq a)) y (ht _) hx).mp he.le
      have h₂ : r y ≤ f a :=
        (hR x (sq a) y (t (sq a)) hx (ht _)).mp he.ge
      exact (le_antisymm h₁ h₂).trans hy
    exact ⟨{
      toEquiv := Equiv.ofBijective f ⟨hInj,hSurj⟩
      map_rel_iff' := by
        intro a b
        exact (hRel a b).symm }⟩

def ArithmeticRepresentativeIso : Prop :=
  ∃ G : Set (Set ℕ × Set ℕ),
    RepresentativeIsoGraph
      (fun A B => OrdinaryArithmeticNull (A \ B))
      (fun A B => HarmonicArithmeticNull (A \ B)) G

theorem arithmeticRepresentativeIso_iff_orderIso :
    ArithmeticRepresentativeIso ↔
      Nonempty (WeightedAlgebra ordinaryEU.weight ordinaryEU.nonneg ≃o
        WeightedAlgebra harmonicEU.weight harmonicEU.nonneg) := by
  have h := orderIso_iff_exists_representativeIsoGraph
    (weightedAlgebraClass ordinaryEU.weight ordinaryEU.nonneg)
    (weightedAlgebraClass harmonicEU.weight harmonicEU.nonneg)
    (weightedAlgebraClass_surjective ordinaryEU.weight ordinaryEU.nonneg)
    (weightedAlgebraClass_surjective harmonicEU.weight harmonicEU.nonneg)
  simpa only [ArithmeticRepresentativeIso, RepresentativeIsoGraph,
    weightedAlgebraClass_le_iff, ordinaryArithmeticNull_iff, harmonicArithmeticNull_iff] using h.symm

theorem CSPD.not_arithmeticRepresentativeIso (hC : CSPD) : ¬ ArithmeticRepresentativeIso :=
  fun h => hC.not_orderIso_ordinary_harmonic (arithmeticRepresentativeIso_iff_orderIso.mp h)

end

end JSP000933
