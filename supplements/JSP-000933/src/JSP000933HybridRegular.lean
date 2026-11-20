import JSP000933Hybrid

open Filter
open scoped BigOperators Topology

namespace JSP000933

noncomputable section

section

variable {T : Type*} [TopologicalSpace T] [TopologicalSpace Bool] [DiscreteTopology Bool]

private theorem continuous_of_discrete_source_r15 {X Y : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [TopologicalSpace Y] (f : X → Y) : Continuous f :=
  continuous_def.mpr (fun _ _ => isOpen_discrete _)

private def xorProfiles_r15 (a b : BoolSeq) : BoolSeq := fun m => a m != b m

private theorem euProfileSet_xorProfiles_r15 (a b : BoolSeq) :
    euProfileSet (xorProfiles_r15 a b) = xorSet (euProfileSet a) (euProfileSet b) := by
  ext m
  simp only [euProfileSet,xorProfiles_r15,xorSet,Set.mem_ofPred_eq,Set.mem_union,Set.mem_sdiff]
  cases a m <;> cases b m <;> decide

private theorem continuous_xorProfiles_r15 {f g : T → BoolSeq} (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => xorProfiles_r15 (f x) (g x)) := by
  apply continuous_pi
  intro m
  exact (continuous_of_discrete_source_r15 (fun z : Bool × Bool => z.1 != z.2)).comp
    (((continuous_apply m).comp hf).prodMk ((continuous_apply m).comp hg))

private theorem continuous_weightedProfilePrefix_r15 (f : EUWeight) {L : T → BoolSeq}
    (hL : Continuous L) (p : ℕ) :
    Continuous (fun x => weightedSetDensity f.weight (euProfileSet (L x)) p) := by
  have he (x : T) : weightedSetDensity f.weight (euProfileSet (L x)) p =
      (∑ m ∈ Finset.range p, if L x m = true then f.weight m else 0) / weightedPrefixSum f.weight p := by
    unfold weightedSetDensity restrictSet euProfileSet
    rw [Finset.sum_filter] <;>
      (apply congrArg (fun z : ℝ => z / weightedPrefixSum f.weight p)
       apply Finset.sum_congr rfl
       intro m _
       by_cases hm : L x m = true <;> simp [hm])
  have hh : (fun x => weightedSetDensity f.weight (euProfileSet (L x)) p) =
      fun x => (∑ m ∈ Finset.range p, if L x m = true then f.weight m else 0) /
        weightedPrefixSum f.weight p := funext he
  rw [hh]
  apply Continuous.div_const
  apply continuous_finsetSum
  intro m _
  exact (continuous_of_discrete_source_r15 (fun b : Bool => if b = true then f.weight m else 0)).comp
    ((continuous_apply m).comp hL)

structure DyadicApproxFamily (T : Type*) [TopologicalSpace T] [TopologicalSpace Bool]
    (f : EUWeight) where
  approximate : ℕ → T → BoolSeq
  targetRepresentative : T → Set ℕ
  continuousAtEveryStep : ∀ j, Continuous (approximate j)
  close : ∀ x j, PrefixTailBound f
    (xorSet (euProfileSet (approximate j x)) (targetRepresentative x)) (blockErrorRate j)

namespace DyadicApproxFamily

variable {f : EUWeight} (D : DyadicApproxFamily T f)

def sample (x : T) (j : ℕ) : Set ℕ := euProfileSet (D.approximate j x)

theorem gaps (x : T) : ∀ j, PrefixTailBound f (xorSet (D.sample x j) (D.sample x (j+1)))
    (blockErrorRate j + blockErrorRate j) :=
  successive_gapBound_of_dyadic_approx f (D.sample x) (D.targetRepresentative x) (D.close x)

def cut (x : T) : ℕ → ℕ := hybridCut f (D.sample x) (D.gaps x)

theorem cut_strict (x : T) : StrictMono (D.cut x) :=
  hybridCut_strictMono f _ _

theorem cut_zero (x : T) : D.cut x 0 = 0 := rfl

def band (x : T) (m : ℕ) : ℕ := hybridBand (D.cut x) (D.cut_strict x) m

def output (x : T) (m : ℕ) : Bool := D.approximate (D.band x m) x m

theorem exact_output (x : T) :
    WeightedNull f.weight (xorSet (euProfileSet (D.output x)) (D.targetRepresentative x)) :=
  canonicalSetHybrid_exact f (D.sample x) (D.targetRepresentative x) (D.gaps x) (D.close x)

theorem isClosed_leastGapCut_test (j N : ℕ) :
    IsClosed {x : T | leastGapCut f (D.sample x) (D.gaps x) j ≤ N} := by
  have he : {x : T | leastGapCut f (D.sample x) (D.gaps x) j ≤ N} =
      ⋂ p : ℕ, ⋂ _ : N ≤ p,
        {x : T | weightedSetDensity f.weight (xorSet (D.sample x j) (D.sample x (j+1))) p ≤
          blockErrorRate j + blockErrorRate j} := by
    ext x
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,leastGapCut_le_iff]
  rw [he]
  apply isClosed_iInter
  intro p
  apply isClosed_iInter
  intro _
  have hC : Continuous (fun x : T => weightedSetDensity f.weight
      (xorSet (D.sample x j) (D.sample x (j+1))) p) := by
    have h := continuous_weightedProfilePrefix_r15 f
      (continuous_xorProfiles_r15 (D.continuousAtEveryStep j) (D.continuousAtEveryStep (j+1))) p
    simpa only [euProfileSet_xorProfiles_r15,sample] using h
  exact isClosed_le hC continuous_const

theorem isClosed_cut_test (j N : ℕ) : IsClosed {x : T | D.cut x j ≤ N} := by
  induction j generalizing N with
  | zero => simp [D.cut_zero]
  | succ j ih =>
    cases N with
    | zero => simp [cut,hybridCut_succ,max_le_iff]
    | succ N =>
      have he : {x : T | D.cut x (j+1) ≤ N+1} =
          {x : T | D.cut x j ≤ N} ∩ {x : T | leastGapCut f (D.sample x) (D.gaps x) j ≤ N+1} := by
        ext x
        simp [cut,hybridCut_succ,max_le_iff]
      change IsClosed {x : T | D.cut x (j+1) ≤ N+1}
      rw [he]
      exact (ih N).inter (D.isClosed_leastGapCut_test j (N+1))

private def testNeighborhood (j N : ℕ) : Set T :=
  interior {x : T | D.cut x j ≤ N} ∪ {x : T | D.cut x j ≤ N}ᶜ

def regularDomain : Set T := ⋂ p : ℕ × ℕ, D.testNeighborhood p.1 p.2

private theorem isOpen_testNeighborhood (j N : ℕ) : IsOpen (D.testNeighborhood j N) :=
  isOpen_interior.union (D.isClosed_cut_test j N).isOpen_compl

private theorem dense_testNeighborhood (j N : ℕ) : Dense (D.testNeighborhood j N) := by
  let E : Set T := {x | D.cut x j ≤ N}
  apply dense_iff_inter_open.mpr
  intro U hU hUn
  by_cases hSub : U ⊆ E
  · obtain ⟨x,hx⟩ := hUn
    exact ⟨x,hx,Or.inl (interior_maximal hSub hU hx)⟩
  · obtain ⟨x,hx,he⟩ := Set.not_subset.mp hSub
    exact ⟨x,hx,Or.inr he⟩

theorem residual_regularDomain [BaireSpace T] : D.regularDomain ∈ residual T := by
  have ho (p : ℕ × ℕ) := D.isOpen_testNeighborhood p.1 p.2
  have hd (p : ℕ × ℕ) := D.dense_testNeighborhood p.1 p.2
  exact residual_of_dense_Gδ (IsGδ.iInter_of_isOpen ho) (dense_iInter_of_isOpen ho hd)

private theorem cut_truth_eventually_const {x : T} (hx : x ∈ D.regularDomain) (j N : ℕ) :
    ∀ᶠ y in 𝓝 x, (D.cut y j ≤ N ↔ D.cut x j ≤ N) := by
  let E : Set T := {y | D.cut y j ≤ N}
  have hx' : x ∈ interior E ∪ Eᶜ := Set.mem_iInter.mp hx (j,N)
  rcases hx' with hi | ho
  · have hI : interior E ∈ 𝓝 x := isOpen_interior.mem_nhds hi
    exact Filter.mem_of_superset hI (fun y hy =>
      ⟨fun _ => interior_subset hi,fun _ => interior_subset hy⟩)
  · have hO : Eᶜ ∈ 𝓝 x := (D.isClosed_cut_test j N).isOpen_compl.mem_nhds ho
    exact Filter.mem_of_superset hO (fun y hy =>
      ⟨fun h => False.elim (hy h),fun h => False.elim (ho h)⟩)

theorem continuousAt_output_of_mem_regularDomain {x : T} (hx : x ∈ D.regularDomain) :
    ContinuousAt D.output x := by
  apply continuousAt_pi.mpr
  intro m
  let j := D.band x m
  have hj : D.cut x j ≤ m ∧ m < D.cut x (j+1) :=
    (hybridBand_eq_iff (D.cut x) (D.cut_strict x) (D.cut_zero x) m j).mp rfl
  have hLocal : ∀ᶠ y in 𝓝 x, D.band y m = j := by
    filter_upwards [D.cut_truth_eventually_const hx j m,D.cut_truth_eventually_const hx (j+1) m] with y h₁ h₂
    apply (hybridBand_eq_iff (D.cut y) (D.cut_strict y) (D.cut_zero y) m j).mpr
    exact ⟨h₁.mpr hj.1,Nat.lt_of_not_ge (fun hn => (not_le_of_gt hj.2) (h₂.mp hn))⟩
  have hc : ContinuousAt (fun y => D.approximate j y m) x :=
    ((continuous_apply m).comp (D.continuousAtEveryStep j)).continuousAt
  apply hc.congr
  filter_upwards [hLocal] with y hy
  simp only [output,hy]

theorem regularDomain_countable_open_dense :
    ∃ U : ℕ → Set T, (∀ n, IsOpen (U n)) ∧ (∀ n, Dense (U n)) ∧
      (⋂ n, U n) = D.regularDomain := by
  let U (n : ℕ) : Set T := D.testNeighborhood (Nat.unpair n).1 (Nat.unpair n).2
  refine ⟨U,fun n => D.isOpen_testNeighborhood _ _,fun n => D.dense_testNeighborhood _ _,?_⟩
  ext x
  constructor
  · intro hx
    apply Set.mem_iInter.mpr
    rintro ⟨i,j⟩
    have h := Set.mem_iInter.mp hx (Nat.pair i j)
    simpa only [U,Nat.unpair_pair] using h
  · intro hx
    apply Set.mem_iInter.mpr
    intro n
    exact Set.mem_iInter.mp hx (Nat.unpair n)

end DyadicApproxFamily

end

end

end JSP000933
