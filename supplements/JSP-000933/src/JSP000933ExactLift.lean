import JSP000933HybridRegular

open Filter
open scoped Topology

namespace JSP000933

noncomputable section

def profileCylinder {ι : Type*} (s : Finset ι) (x : ι → Bool) : Set (ι → Bool) :=
  {y | ∀ i ∈ s, y i = x i}

theorem isOpen_profileCylinder {ι : Type*} [TopologicalSpace Bool] [DiscreteTopology Bool]
    (s : Finset ι) (x : ι → Bool) : IsOpen (profileCylinder s x) := by
  have he : profileCylinder s x =
      ⋂ i : ↥s, (fun y : ι → Bool => y i.1) ⁻¹' ({x i.1} : Set Bool) := by
    ext y
    constructor
    · intro hy
      exact Set.mem_iInter.mpr (fun i => Set.mem_singleton_iff.mpr (hy i.1 i.2))
    · intro hy i hi
      exact Set.mem_singleton_iff.mp (Set.mem_iInter.mp hy ⟨i,hi⟩)
  rw [he]
  exact isOpen_iInter_of_finite (fun i => (isOpen_discrete _).preimage (continuous_apply i.1))

private theorem cylinder_in_nhds_r16 {ι : Type*} [TopologicalSpace Bool] {U : Set (ι → Bool)}
    {x : ι → Bool} (hU : U ∈ 𝓝 x) :
    ∃ s : Finset ι, profileCylinder s x ⊆ U := by
  rw [nhds_pi] at hU
  obtain ⟨s,V,hV,hSV⟩ := Filter.mem_pi'.mp hU
  refine ⟨s,fun y hy => hSV ?_⟩
  intro i hi
  change y i ∈ V i
  rw [hy i hi]
  exact mem_of_mem_nhds (hV i)

private theorem patch_own_bits_r16 {ι : Type*} (s : Finset ι) (x : ι → Bool) :
    patchProfile s (fun i => x i.1) x = x := by
  funext i
  classical
  by_cases hi : i ∈ s
  · exact patchProfile_eq_left _ _ _ hi
  · exact patchProfile_eq_right _ _ _ hi

private theorem dense_preimage_patchProfile_r16 {ι : Type*} [TopologicalSpace Bool]
    [DiscreteTopology Bool] {U : Set (ι → Bool)} (hU : Dense U)
    (s : Finset ι) (p : ↥s → Bool) : Dense ((patchProfile s p) ⁻¹' U) := by
  classical
  apply dense_iff_inter_open.mpr
  intro V hV hv
  obtain ⟨x,hx⟩ := hv
  obtain ⟨t,ht⟩ := cylinder_in_nhds_r16 (hV.mem_nhds hx)
  let W := profileCylinder (s ∪ t) (patchProfile s p x)
  have hW : IsOpen W := isOpen_profileCylinder _ _
  have hWN : W.Nonempty := ⟨patchProfile s p x,fun _ _ => rfl⟩
  obtain ⟨y,hy,hyU⟩ := (dense_iff_inter_open.mp hU) W hW hWN
  let z := patchProfile s (fun i => x i.1) y
  have hz : z ∈ profileCylinder t x := by
    intro i hi
    by_cases hs : i ∈ s
    · exact patchProfile_eq_left _ _ _ hs
    · rw [show z i = y i from patchProfile_eq_right _ _ _ hs,
        hy i (Finset.mem_union.mpr (Or.inr hi)), patchProfile_eq_right _ _ _ hs]
  have hpatch : patchProfile s p z = y := by
    change patchProfile s p (patchProfile s (fun i => x i.1) y) = y
    rw [patchProfile_over_patch]
    funext i
    by_cases hs : i ∈ s
    · rw [patchProfile_eq_left _ _ _ hs, hy i (Finset.mem_union.mpr (Or.inl hs)),
        patchProfile_eq_left _ _ _ hs]
    · exact patchProfile_eq_right _ _ _ hs
  refine ⟨z,ht hz,?_⟩
  change patchProfile s p z ∈ U
  rw [hpatch]
  exact hyU

theorem exists_profile_patch_away {ι : Type*} [TopologicalSpace Bool] [DiscreteTopology Bool]
    [BaireSpace (ι → Bool)] {U : Set (ι → Bool)} (hU : IsOpen U) (hd : Dense U)
    (s : Finset ι) :
    ∃ t : Finset ι, Disjoint t s ∧ ∃ f : ι → Bool, profileCylinder t f ⊆ U := by
  classical
  let W : Set (ι → Bool) := ⋂ p : ↥s → Bool, (patchProfile s p) ⁻¹' U
  have hO (p : ↥s → Bool) : IsOpen ((patchProfile s p) ⁻¹' U) :=
    hU.preimage (continuous_patchProfile s p)
  have hD (p : ↥s → Bool) : Dense ((patchProfile s p) ⁻¹' U) :=
    dense_preimage_patchProfile_r16 hd s p
  have hWO : IsOpen W := isOpen_iInter_of_finite hO
  have hWD : Dense W := dense_iInter_of_isOpen hO hD
  obtain ⟨x,_,hx⟩ := (dense_iff_inter_open.mp hWD) Set.univ isOpen_univ
    ⟨fun _ : ι => false,Set.mem_univ _⟩
  obtain ⟨t,ht⟩ := cylinder_in_nhds_r16 (hWO.mem_nhds hx)
  refine ⟨t \ s,?_,x,fun y hy => ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hsi
    exact (Finset.mem_sdiff.mp hi).2 hsi
  · let z := patchProfile s (fun i => x i.1) y
    have hz : z ∈ profileCylinder t x := by
      intro i hi
      by_cases hs : i ∈ s
      · exact patchProfile_eq_left _ _ _ hs
      · exact (patchProfile_eq_right _ _ _ hs).trans (hy i (Finset.mem_sdiff.mpr ⟨hi,hs⟩))
    have hW' := ht hz
    have hpre := Set.mem_iInter.mp hW' (fun i : ↥s => y i.1)
    change patchProfile s (fun i : ↥s => y i.1)
      (patchProfile s (fun i : ↥s => x i.1) y) ∈ U at hpre
    rw [patchProfile_over_patch,patch_own_bits_r16] at hpre
    exact hpre

def mixWithTemplate {ι : Type*} (P : Set ι) (template x : ι → Bool) (i : ι) : Bool := by
  classical
  exact if i ∈ P then x i else template i

theorem continuous_mixWithTemplate {ι : Type*} [TopologicalSpace Bool]
    (P : Set ι) (template : ι → Bool) : Continuous (mixWithTemplate P template) := by
  classical
  apply continuous_pi
  intro i
  by_cases h : i ∈ P
  · simpa only [mixWithTemplate,ite_eq_left h] using (continuous_apply i : Continuous (fun x : ι → Bool => x i))
  · simpa only [mixWithTemplate,ite_eq_right h] using (continuous_const : Continuous (fun _ : ι → Bool => template i))

private structure GoodOpenPatch {ι : Type*} (U : Set (ι → Bool)) (previous : Finset ι) where
  positions : Finset ι
  pattern : ι → Bool
  outside : Disjoint positions previous
  force : profileCylinder positions pattern ⊆ U

theorem exists_complementary_sections_dense_open {ι : Type*}
    [TopologicalSpace Bool] [DiscreteTopology Bool] [BaireSpace (ι → Bool)]
    (U : ℕ → Set (ι → Bool)) (hO : ∀ n, IsOpen (U n)) (hD : ∀ n, Dense (U n)) :
    ∃ P : Set ι, ∃ v : ι → Bool, ∀ x : ι → Bool,
      mixWithTemplate P v x ∈ (⋂ n, U n) ∧ mixWithTemplate Pᶜ v x ∈ (⋂ n, U n) := by
  classical
  let choose (n : ℕ) (s : Finset ι) : GoodOpenPatch (U (n/2)) s := by
    have h : Nonempty (GoodOpenPatch (U (n/2)) s) := by
      obtain ⟨t,ht,p,hp⟩ := exists_profile_patch_away (hO (n/2)) (hD (n/2)) s
      exact ⟨⟨t,p,ht,hp⟩⟩
    exact Classical.choice h
  let past : ℕ → Finset ι := Nat.rec ∅ (fun n s => s ∪ (choose n s).positions)
  let pad (n : ℕ) := (choose n (past n)).positions
  let word (n : ℕ) := (choose n (past n)).pattern
  have hf (n : ℕ) : profileCylinder (pad n) (word n) ⊆ U (n/2) := (choose n (past n)).force
  have hdis (n : ℕ) : Disjoint (pad n) (past n) := (choose n (past n)).outside
  have hpast (n : ℕ) : past (n+1) = past n ∪ pad n := rfl
  have hMono : Monotone past := monotone_nat_of_le_succ (fun n => by
    rw [hpast]
    exact Finset.subset_union_left)
  have hd (i j : ℕ) (h : i < j) : Disjoint (pad i) (pad j) := by
    rw [Finset.disjoint_left]
    intro m him hjm
    have hs : pad i ⊆ past (i+1) := by rw [hpast]; exact Finset.subset_union_right
    have hm : m ∈ past j := hMono (Nat.succ_le_of_lt h) (hs him)
    exact Finset.disjoint_left.mp (hdis j) hjm hm
  have pd : Pairwise (fun i j => Disjoint (pad i) (pad j)) := by
    intro i j h
    rcases lt_or_gt_of_ne h with h | h
    · exact hd i j h
    · exact (hd j i h).symm
  let P : Set ι := {m | ∃ n, m ∈ pad (2*n)}
  let v (m : ι) : Bool := if h : ∃ n, m ∈ pad n then word (Classical.choose h) m else false
  have hv (n : ℕ) (m : ι) (hm : m ∈ pad n) : v m = word n m := by
    have he : ∃ j, m ∈ pad j := ⟨n,hm⟩
    have hspec := Classical.choose_spec he
    have hi : Classical.choose he = n := by
      by_contra hh
      exact Finset.disjoint_left.mp (pd hh) hspec hm
    simp only [v,dite_eq_left he,hi]
  refine ⟨P,v,fun x => ?_⟩
  constructor
  · apply Set.mem_iInter.mpr
    intro n
    have hc : mixWithTemplate P v x ∈ profileCylinder (pad (2*n+1)) (word (2*n+1)) := by
      intro m hm
      have hn : m ∉ P := by
        rintro ⟨j,hj⟩
        exact Finset.disjoint_left.mp (pd (show (2*n+1) ≠ 2*j by omega)) hm hj
      simpa only [mixWithTemplate,ite_eq_right hn] using hv (2*n+1) m hm
    have hh := hf (2*n+1) hc
    rwa [show (2*n+1)/2 = n by omega] at hh
  · apply Set.mem_iInter.mpr
    intro n
    have hc : mixWithTemplate Pᶜ v x ∈ profileCylinder (pad (2*n)) (word (2*n)) := by
      intro m hm
      have hn : m ∉ Pᶜ := fun hh => hh ⟨n,hm⟩
      simpa only [mixWithTemplate,ite_eq_right hn] using hv (2*n) m hm
    have hh := hf (2*n) hc
    rwa [show (2*n)/2 = n by omega] at hh

private def coordinateSubdomain {A : Set ℕ} (P : Set ↥A) : Set ℕ :=
  {m | ∃ h : m ∈ A, (⟨m,h⟩ : ↥A) ∈ P}

private theorem profile_mix_cut_r16 {A : Set ℕ} (P : Set ↥A) (v x : ↥A → Bool) :
    subsetOfProfile A (mixWithTemplate P v x) ∩ coordinateSubdomain P =
      subsetOfProfile A x ∩ coordinateSubdomain P := by
  classical
  ext m
  by_cases hm : m ∈ A
  · by_cases hP : (⟨m,hm⟩ : ↥A) ∈ P
    · simp [subsetOfProfile,mixWithTemplate,coordinateSubdomain,hm,hP]
    · simp [subsetOfProfile,mixWithTemplate,coordinateSubdomain,hm,hP]
  · simp [subsetOfProfile,coordinateSubdomain,hm]

private theorem profile_cut_xor_all_r16 {A : Set ℕ} (P : Set ↥A) (x : ↥A → Bool) :
    xorSet (subsetOfProfile A x ∩ coordinateSubdomain P)
        (subsetOfProfile A x ∩ coordinateSubdomain Pᶜ) = subsetOfProfile A x := by
  classical
  ext m
  by_cases hm : m ∈ A
  · by_cases hp : (⟨m,hm⟩ : ↥A) ∈ P
    · simp [xorSet,subsetOfProfile,coordinateSubdomain,hm,hp]
    · simp [xorSet,subsetOfProfile,coordinateSubdomain,hm,hp]
  · simp [xorSet,subsetOfProfile,coordinateSubdomain,hm]

private theorem weightedClass_xor_r16 (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m) (X Y : Set ℕ) :
    weightedClass a ha (xorSet X Y) = weightedClass a ha X + weightedClass a ha Y := by
  have he : xorSet X Y = symmDiff X Y := rfl
  unfold weightedClass
  rw [he,toBoolRing_symmDiff,map_add]

private def maskProfile (P : Set ℕ) (y : BoolSeq) (m : ℕ) : Bool := by
  classical
  exact if m ∈ P then y m else false

private theorem maskProfile_set (P : Set ℕ) (y : BoolSeq) :
    euProfileSet (maskProfile P y) = euProfileSet y ∩ P := by
  classical
  ext m
  by_cases hm : m ∈ P <;> simp [euProfileSet,maskProfile,hm]

private theorem continuous_maskProfile [TopologicalSpace Bool] (P : Set ℕ) : Continuous (maskProfile P) := by
  classical
  apply continuous_pi
  intro m
  by_cases hm : m ∈ P
  · simpa only [maskProfile,ite_eq_left hm] using (continuous_apply m : Continuous (fun y : BoolSeq => y m))
  · simpa only [maskProfile,ite_eq_right hm] using (continuous_const : Continuous (fun _ : BoolSeq => false))

private def xorTwoProfiles (y z : BoolSeq) (m : ℕ) : Bool := y m != z m

private theorem xorTwoProfiles_set (y z : BoolSeq) :
    euProfileSet (xorTwoProfiles y z) = xorSet (euProfileSet y) (euProfileSet z) := by
  ext m
  simp only [euProfileSet,xorTwoProfiles,xorSet,Set.mem_union,Set.mem_sdiff,Set.mem_ofPred_eq]
  cases y m <;> cases z m <;> decide

private theorem continuous_xorTwoProfiles {T : Type*} [TopologicalSpace T] [TopologicalSpace Bool]
    [DiscreteTopology Bool] {y z : T → BoolSeq} (hy : Continuous y) (hz : Continuous z) :
    Continuous (fun x => xorTwoProfiles (y x) (z x)) := by
  apply continuous_pi
  intro m
  let f (b : Bool × Bool) : Bool := b.1 != b.2
  have hf : Continuous f := continuous_def.mpr (fun _ _ => isOpen_discrete _)
  exact hf.comp (((continuous_apply m).comp hy).prodMk ((continuous_apply m).comp hz))

theorem exists_continuous_profile_lift_from_regular
    {f g : EUWeight} {A : Set ℕ}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    [TopologicalSpace Bool] [DiscreteTopology Bool] [BaireSpace (↥A → Bool)]
    (H : (↥A → Bool) → BoolSeq)
    (hH : ∀ x, F (weightedClass f.weight f.nonneg (subsetOfProfile A x)) =
      weightedClass g.weight g.nonneg (euProfileSet (H x)))
    (U : ℕ → Set (↥A → Bool)) (hO : ∀ n, IsOpen (U n)) (hD : ∀ n, Dense (U n))
    (hCont : ∀ x ∈ (⋂ n, U n), ContinuousAt H x) :
    ∃ L : (↥A → Bool) → BoolSeq, Continuous L ∧
      ∀ x, F (weightedClass f.weight f.nonneg (subsetOfProfile A x)) =
        weightedClass g.weight g.nonneg (euProfileSet (L x)) := by
  classical
  obtain ⟨P,v,hP⟩ := exists_complementary_sections_dense_open U hO hD
  let M (B : Set ↥A) := mixWithTemplate B v
  let face (B : Set ↥A) := coordinateSubdomain B
  let K (B : Set ↥A) := representativeLiftOfHom (f := f) (g := g) F (face B)
  let Lpart (B : Set ↥A) (x : ↥A → Bool) := maskProfile (K B) (H (M B x))
  have hLcont (B : Set ↥A) (hB : ∀ x, M B x ∈ (⋂ n, U n)) : Continuous (Lpart B) := by
    apply (continuous_maskProfile (K B)).comp
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hCont (M B x) (hB x)).comp' ((continuous_mixWithTemplate B v).continuousAt)
  have hL (B : Set ↥A) (x : ↥A → Bool) :
      weightedClass g.weight g.nonneg (euProfileSet (Lpart B x)) =
        F (weightedClass f.weight f.nonneg (subsetOfProfile A x ∩ face B)) := by
    change weightedClass g.weight g.nonneg (euProfileSet (maskProfile (K B) (H (M B x)))) = _
    rw [maskProfile_set,weightedClass_inter,← hH (M B x)]
    have hK : weightedClass g.weight g.nonneg (K B) = F (weightedClass f.weight f.nonneg (face B)) :=
      representativeLiftOfHom_spec (f := f) (g := g) F (face B)
    rw [hK,← map_mul,← weightedClass_inter]
    exact congrArg (fun X : Set ℕ => F (weightedClass f.weight f.nonneg X))
      (profile_mix_cut_r16 B v x)
  let L (x : ↥A → Bool) := xorTwoProfiles (Lpart P x) (Lpart Pᶜ x)
  refine ⟨L,continuous_xorTwoProfiles (hLcont P (fun x => (hP x).1))
    (hLcont Pᶜ (fun x => (hP x).2)),fun x => ?_⟩
  change _ = weightedClass g.weight g.nonneg (euProfileSet (xorTwoProfiles (Lpart P x) (Lpart Pᶜ x)))
  rw [xorTwoProfiles_set,weightedClass_xor_r16,hL,hL,← map_add,← weightedClass_xor_r16]
  exact congrArg (fun X : Set ℕ => F (weightedClass f.weight f.nonneg X))
    (profile_cut_xor_all_r16 P x).symm

theorem exists_continuous_profile_lift_of_dyadic_approx
    {f g : EUWeight} {A : Set ℕ}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    [TopologicalSpace Bool] [DiscreteTopology Bool] [BaireSpace (↥A → Bool)]
    (D : DyadicApproxFamily (↥A → Bool) g)
    (hD : ∀ x, F (weightedClass f.weight f.nonneg (subsetOfProfile A x)) =
      weightedClass g.weight g.nonneg (D.targetRepresentative x)) :
    ∃ L : (↥A → Bool) → BoolSeq, Continuous L ∧
      ∀ x, F (weightedClass f.weight f.nonneg (subsetOfProfile A x)) =
        weightedClass g.weight g.nonneg (euProfileSet (L x)) := by
  obtain ⟨U,hO,hOpen,he⟩ := D.regularDomain_countable_open_dense
  refine exists_continuous_profile_lift_from_regular F D.output ?_ U hO hOpen ?_
  · intro x
    exact (hD x).trans ((weightedClass_eq_iff g.weight g.nonneg _ _).mpr (D.exact_output x)).symm
  · intro x hx
    exact D.continuousAt_output_of_mem_regularDomain (he ▸ hx)

def HasLocalizedUniformApproxLift {f g : EUWeight}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg) (A : Set ℕ) : Prop := by
  letI : TopologicalSpace Bool := ⊥
  exact ∀ ε : ℝ, 0 < ε → ∃ L : (↥A → Bool) → BoolSeq, Continuous L ∧
    ∀ x : ↥A → Bool, ∃ Y Z : Set ℕ, WeightedNull g.weight Y ∧ Z ∈ euPrefixSmall g ε ∧
      xorSet (euProfileSet (L x))
        (representativeLiftOfHom (f := f) (g := g) F (subsetOfProfile A x)) ⊆ Y ∪ Z

theorem hasContinuousLift_of_localized_uniform_approx {f g : EUWeight} {A : Set ℕ}
    (F : WeightedRing f.weight f.nonneg →+* WeightedRing g.weight g.nonneg)
    (h : HasLocalizedUniformApproxLift (f := f) (g := g) F A) :
    HasContinuousLift (f := f) (g := g) F A := by
  classical
  letI : TopologicalSpace Bool := ⊥
  letI : DiscreteTopology Bool := ⟨rfl⟩
  let X (x : ↥A → Bool) := representativeLiftOfHom (f := f) (g := g) F (subsetOfProfile A x)
  have heach (j : ℕ) : ∃ L : (↥A → Bool) → BoolSeq, Continuous L ∧
      ∀ x : ↥A → Bool, PrefixTailBound g (xorSet (euProfileSet (L x)) (X x)) (blockErrorRate j) := by
    let ε : ℝ := blockErrorRate j / 2
    have hε : 0 < ε := by dsimp [ε,blockErrorRate]; positivity
    obtain ⟨L,hL,hA⟩ := h ε hε
    refine ⟨L,hL,fun x => ?_⟩
    obtain ⟨Y,Z,hY,hZ,hXZ⟩ := hA x
    have hb := PrefixTailBound.of_null_union_small hXZ hY hZ hε
    have hEq : ε + ε = blockErrorRate j := by dsimp [ε]; ring
    simpa only [hEq] using hb
  choose seq hs using heach
  let D : DyadicApproxFamily (↥A → Bool) g :=
    ⟨seq,X,fun j => (hs j).1,fun x j => (hs j).2 x⟩
  exact exists_continuous_profile_lift_of_dyadic_approx F D fun x =>
    (representativeLiftOfHom_spec (f := f) (g := g) F (subsetOfProfile A x)).symm

theorem no_localized_uniform_approxLift_of_orderIso
    (e : WeightedAlgebra ordinaryEU.weight ordinaryEU.nonneg ≃o
      WeightedAlgebra harmonicEU.weight harmonicEU.nonneg)
    (A : Set ℕ) (hA : LongBlockLarge A) :
    ¬ HasLocalizedUniformApproxLift (f := ordinaryEU) (g := harmonicEU)
      (ringEquivOfBoolAlgebraOrderIso e).toRingHom A := by
  intro h
  exact no_localized_continuous_lift_of_ordinary_harmonic_orderIso e A hA
    (hasContinuousLift_of_localized_uniform_approx (ringEquivOfBoolAlgebraOrderIso e).toRingHom h)

end

end JSP000933
