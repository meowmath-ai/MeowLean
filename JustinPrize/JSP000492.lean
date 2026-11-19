import Mathlib


noncomputable section

namespace JSP000492

open Filter

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev UnitSphere := {v : Space // ‖v‖ = 1}

def distancePairs (S : Finset UnitSphere) (d : ℝ) : Finset (Sym2 UnitSphere) := by
  classical
  exact S.sym2.filter fun e => ∃ x y : UnitSphere,
    e = s(x, y) ∧ x ≠ y ∧ dist x.val y.val = d

private theorem distancePairs_mono {S T : Finset UnitSphere} (h : S ⊆ T) (d : ℝ) :
    distancePairs S d ⊆ distancePairs T d := by
  classical
  intro e he
  unfold distancePairs at he ⊢
  obtain ⟨heS, heD⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨Finset.sym2_mono h heS, heD⟩

private def triple (x y z : ℝ) : Space := WithLp.toLp 2 ![x, y, z]

@[simp] private theorem triple_zero (x y z : ℝ) :
    (triple x y z).ofLp (0 : Fin 3) = x := by rfl

@[simp] private theorem triple_one (x y z : ℝ) :
    (triple x y z).ofLp (1 : Fin 3) = y := by rfl

@[simp] private theorem triple_two (x y z : ℝ) :
    (triple x y z).ofLp (2 : Fin 3) = z := by rfl

private def rawPoint (p : ℝ × ℝ) : Space := triple p.1 p.2 1
private def rawLine (l : ℝ × ℝ) : Space := triple (-l.1) 1 (-l.2)

private theorem ne_zero_of_coord_one {v : Space} {i : Fin 3} (h : v.ofLp i = 1) :
    v ≠ 0 := by
  intro hv
  simp [hv] at h

private theorem rawPoint_ne_zero (p : ℝ × ℝ) : rawPoint p ≠ 0 :=
  ne_zero_of_coord_one (i := 2) (by simp [rawPoint])

private theorem rawLine_ne_zero (l : ℝ × ℝ) : rawLine l ≠ 0 :=
  ne_zero_of_coord_one (i := 1) (by simp [rawLine])

private def normalize (v : Space) : Space := ‖v‖⁻¹ • v

private theorem normalize_norm {v : Space} (hv : v ≠ 0) : ‖normalize v‖ = 1 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [normalize, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  exact inv_mul_cancel₀ hn.ne'

private theorem normalize_coord (v : Space) (i : Fin 3) :
    (normalize v).ofLp i = ‖v‖⁻¹ * v.ofLp i := by
  simp only [normalize, PiLp.smul_apply, smul_eq_mul]

private theorem raw_eq_of_normalize_eq {u v : Space} {i : Fin 3}
    (hu : u.ofLp i = 1) (hv : v.ofLp i = 1)
    (h : normalize u = normalize v) : u = v := by
  have hs : ‖u‖⁻¹ = ‖v‖⁻¹ := by
    simpa only [normalize_coord, hu, hv, mul_one] using
      congrArg (fun q : Space => q.ofLp i) h
  have hn : ‖u‖ ≠ 0 := (norm_pos_iff.mpr (ne_zero_of_coord_one hu)).ne'
  unfold normalize at h
  rw [← hs] at h
  simpa only [smul_smul, mul_inv_cancel₀ hn, one_smul] using
    congrArg (fun q : Space => ‖u‖ • q) h

private def point (p : ℝ × ℝ) : UnitSphere :=
  ⟨normalize (rawPoint p), normalize_norm (rawPoint_ne_zero p)⟩

private def line (l : ℝ × ℝ) : UnitSphere :=
  ⟨normalize (rawLine l), normalize_norm (rawLine_ne_zero l)⟩

private theorem point_injective : Function.Injective point := by
  intro p q h
  have h' : rawPoint p = rawPoint q :=
    raw_eq_of_normalize_eq (i := 2) (by simp [rawPoint]) (by simp [rawPoint])
      (congrArg Subtype.val h)
  exact Prod.ext
    (by simpa only [rawPoint, triple_zero] using
      congrArg (fun v : Space => v.ofLp (0 : Fin 3)) h')
    (by simpa only [rawPoint, triple_one] using
      congrArg (fun v : Space => v.ofLp (1 : Fin 3)) h')

private theorem line_injective : Function.Injective line := by
  intro p q h
  have h' : rawLine p = rawLine q :=
    raw_eq_of_normalize_eq (i := 1) (by simp [rawLine]) (by simp [rawLine])
      (congrArg Subtype.val h)
  have h₁ : -p.1 = -q.1 := by
    simpa only [rawLine, triple_zero] using
      congrArg (fun v : Space => v.ofLp (0 : Fin 3)) h'
  have h₂ : -p.2 = -q.2 := by
    simpa only [rawLine, triple_two] using
      congrArg (fun v : Space => v.ofLp (2 : Fin 3)) h'
  exact Prod.ext (by linarith) (by linarith)

private theorem point_ne_line (p l : ℝ × ℝ) (hb : 0 ≤ l.2) : point p ≠ line l := by
  have hp : 0 < (point p).val.ofLp (2 : Fin 3) := by
    change 0 < (normalize (rawPoint p)).ofLp (2 : Fin 3)
    rw [normalize_coord]
    simp only [rawPoint, triple_two, mul_one]
    exact inv_pos.mpr (norm_pos_iff.mpr (rawPoint_ne_zero p))
  have hl : (line l).val.ofLp (2 : Fin 3) ≤ 0 := by
    change (normalize (rawLine l)).ofLp (2 : Fin 3) ≤ 0
    rw [normalize_coord]
    simp only [rawLine, triple_two]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) (neg_nonpos.mpr hb)
  intro h
  have h₂ : (point p).val.ofLp (2 : Fin 3) = (line l).val.ofLp (2 : Fin 3) :=
    congrArg (fun v : UnitSphere => v.val.ofLp (2 : Fin 3)) h
  rw [h₂] at hp
  exact (not_lt_of_ge hl) hp

private theorem raw_inner_zero (x a b : ℝ) :
    inner ℝ (rawPoint (x, a * x + b)) (rawLine (a, b)) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
  simp only [Pi.star_apply, star_trivial]
  change (-a) * x + 1 * (a * x + b) + (-b) * 1 = (0 : ℝ)
  ring

private theorem chord_of_incidence (x a b : ℝ) :
    dist (point (x, a * x + b)).val (line (a, b)).val = Real.sqrt 2 := by
  let p : UnitSphere := point (x, a * x + b)
  let l : UnitSphere := line (a, b)
  change dist p.val l.val = Real.sqrt 2
  have hinner : inner ℝ p.val l.val = 0 := by
    change inner ℝ (normalize (rawPoint (x, a * x + b))) (normalize (rawLine (a, b))) = 0
    simp only [normalize, real_inner_smul_left, real_inner_smul_right, raw_inner_zero, mul_zero]
  have hsq : dist p.val l.val ^ 2 = 2 := by
    rw [dist_eq_norm, norm_sub_sq_real, p.property, l.property, hinner]; norm_num
  calc
    dist p.val l.val = Real.sqrt (dist p.val l.val ^ 2) :=
      (Real.sqrt_sq dist_nonneg).symm
    _ = Real.sqrt 2 := by rw [hsq]

private abbrev PointIndex (k : ℕ) := Fin k × Fin (2 * k ^ 2)
private abbrev LineIndex (k : ℕ) := Fin k × Fin (k ^ 2)
private abbrev IncidenceIndex (k : ℕ) := Fin k × LineIndex k

private def castPair {m n : ℕ} (p : Fin m × Fin n) : ℝ × ℝ :=
  ((p.1.val : ℝ), (p.2.val : ℝ))

private theorem castPair_injective {m n : ℕ} :
    Function.Injective (castPair (m := m) (n := n)) := by
  intro p q h
  have h₁ : (p.1.val : ℝ) = (q.1.val : ℝ) := congrArg Prod.fst h
  have h₂ : (p.2.val : ℝ) = (q.2.val : ℝ) := congrArg Prod.snd h
  exact Prod.ext (Fin.ext (by exact_mod_cast h₁)) (Fin.ext (by exact_mod_cast h₂))

private def pointVertex (k : ℕ) : PointIndex k ↪ UnitSphere :=
  ⟨fun p => point (castPair p), point_injective.comp castPair_injective⟩

private def lineVertex (k : ℕ) : LineIndex k ↪ UnitSphere :=
  ⟨fun l => line (castPair l), line_injective.comp castPair_injective⟩

private theorem pointVertex_ne_lineVertex {k : ℕ} (p : PointIndex k) (l : LineIndex k) :
    pointVertex k p ≠ lineVertex k l :=
  point_ne_line (castPair p) (castPair l) (show 0 ≤ (l.2.val : ℝ) from Nat.cast_nonneg _)

private def incidentPoint {k : ℕ} (i : IncidenceIndex k) : PointIndex k :=
  (i.1, ⟨i.2.1.val * i.1.val + i.2.2.val, by
    have hmul : i.2.1.val * i.1.val ≤ k ^ 2 := by
      calc
        i.2.1.val * i.1.val ≤ k * k := Nat.mul_le_mul i.2.1.isLt.le i.1.isLt.le
        _ = k ^ 2 := (pow_two k).symm
    have hb : i.2.2.val < k ^ 2 := i.2.2.isLt
    omega⟩)

private def allPoints (k : ℕ) : Finset UnitSphere := Finset.univ.map (pointVertex k)
private def allLines (k : ℕ) : Finset UnitSphere := Finset.univ.map (lineVertex k)

private def sample (k : ℕ) : Finset UnitSphere := by
  classical
  exact allPoints k ∪ allLines k

private theorem sample_card (k : ℕ) : (sample k).card = 3 * k ^ 3 := by
  classical
  have hdisj : Disjoint (allPoints k) (allLines k) := by
    rw [Finset.disjoint_left]
    intro v hvP hvL
    change v ∈ Finset.univ.map (pointVertex k) at hvP
    change v ∈ Finset.univ.map (lineVertex k) at hvL
    obtain ⟨p, _, hp⟩ := Finset.mem_map.mp hvP
    obtain ⟨l, _, hl⟩ := Finset.mem_map.mp hvL
    exact pointVertex_ne_lineVertex p l (hp.trans hl.symm)
  unfold sample
  rw [Finset.card_union_of_disjoint hdisj]
  simp only [allPoints, allLines, Finset.card_map, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
  ring

private def edge (k : ℕ) (i : IncidenceIndex k) : Sym2 UnitSphere :=
  s(pointVertex k (incidentPoint i), lineVertex k i.2)

private theorem edge_injective (k : ℕ) : Function.Injective (edge k) := by
  intro i j h
  unfold edge at h
  rcases Sym2.eq_iff.mp h with hd | hs
  · have hp : incidentPoint i = incidentPoint j := (pointVertex k).injective hd.1
    have hx : i.1 = j.1 := congrArg (fun p : PointIndex k => p.1) hp
    have hl : i.2 = j.2 := (lineVertex k).injective hd.2
    exact Prod.ext hx hl
  · exact False.elim (pointVertex_ne_lineVertex (incidentPoint i) j.2 hs.1)

private theorem edge_mem (k : ℕ) (i : IncidenceIndex k) :
    edge k i ∈ distancePairs (sample k) (Real.sqrt 2) := by
  classical
  unfold distancePairs edge
  refine Finset.mem_filter.mpr ⟨Finset.mk_mem_sym2_iff.mpr ⟨?_, ?_⟩, ?_⟩
  · unfold sample
    apply Finset.mem_union_left
    exact Finset.mem_map_of_mem (pointVertex k) (Finset.mem_univ (incidentPoint i))
  · unfold sample
    apply Finset.mem_union_right
    exact Finset.mem_map_of_mem (lineVertex k) (Finset.mem_univ i.2)
  · refine ⟨pointVertex k (incidentPoint i), lineVertex k i.2, rfl,
      pointVertex_ne_lineVertex (incidentPoint i) i.2, ?_⟩
    change dist (point (castPair (incidentPoint i))).val (line (castPair i.2)).val = Real.sqrt 2
    have hxy : castPair (incidentPoint i) =
        ((i.1.val : ℝ), (i.2.1.val : ℝ) * (i.1.val : ℝ) + (i.2.2.val : ℝ)) := by
      change ((i.1.val : ℝ), ((i.2.1.val * i.1.val + i.2.2.val : ℕ) : ℝ)) =
        ((i.1.val : ℝ), (i.2.1.val : ℝ) * (i.1.val : ℝ) + (i.2.2.val : ℝ))
      simp only [Nat.cast_add, Nat.cast_mul]
    rw [hxy]
    exact chord_of_incidence (i.1.val : ℝ) (i.2.1.val : ℝ) (i.2.2.val : ℝ)

private theorem sample_chords (k : ℕ) :
    k ^ 4 ≤ (distancePairs (sample k) (Real.sqrt 2)).card := by
  let edges := (Finset.univ : Finset (IncidenceIndex k)).map ⟨edge k, edge_injective k⟩
  have hc : edges.card = k ^ 4 := by
    simp only [edges, Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
    ring
  have hr : edges ⊆ distancePairs (sample k) (Real.sqrt 2) := by
    intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp he
    rw [← hi]
    exact edge_mem k i
  rw [← hc]
  exact Finset.card_le_card hr

private theorem sphere_infinite : Infinite UnitSphere :=
  Infinite.of_injective (fun x : ℝ => point (x, 0)) (by
    intro x y h
    exact congrArg Prod.fst (point_injective h))

private theorem pad {S : Finset UnitSphere} {n : ℕ} (hn : S.card ≤ n) :
    ∃ T : Finset UnitSphere, S ⊆ T ∧ T.card = n := by
  classical
  obtain ⟨U, hU⟩ := @Finset.exists_card_eq UnitSphere sphere_infinite n
  have hTotal : n ≤ (S ∪ U).card := by
    rw [← hU]
    exact Finset.card_le_card Finset.subset_union_right
  obtain ⟨T, hST, _, hT⟩ := Finset.exists_subsuperset_card_eq
    (t := S ∪ U) Finset.subset_union_left hn hTotal
  exact ⟨T, hST, hT⟩

private def scale (n : ℕ) : ℕ := Nat.findGreatest (fun k => 3 * k ^ 3 ≤ n) (n + 1)

private theorem scale_fits (n : ℕ) : 3 * (scale n) ^ 3 ≤ n := by
  unfold scale
  exact Nat.findGreatest_spec (P := fun k => 3 * k ^ 3 ≤ n)
    (n := n + 1) (m := 0) (Nat.zero_le _) (by simp)

private theorem scale_le (n : ℕ) : scale n ≤ n := by
  have hc : scale n ≤ (scale n) ^ 3 := Nat.le_self_pow (by decide) _
  have hs := scale_fits n
  omega

private theorem scale_ge {m n : ℕ} (hm : 3 * m ^ 3 ≤ n) : m ≤ scale n := by
  have hCube : m ≤ m ^ 3 := Nat.le_self_pow (by decide) m
  have hBound : m ≤ n + 1 := by omega
  exact Nat.le_findGreatest (P := fun k => 3 * k ^ 3 ≤ n) (n := n + 1) hBound hm

private theorem scale_next (n : ℕ) : n < 3 * (scale n + 1) ^ 3 := by
  have hb : scale n + 1 ≤ n + 1 := Nat.succ_le_succ (scale_le n)
  have ht : scale n < scale n + 1 := Nat.lt_succ_self _
  exact lt_of_not_ge (Nat.findGreatest_is_greatest
    (P := fun k => 3 * k ^ 3 ≤ n) (n := n + 1) ht hb)

private theorem scale_bound (n : ℕ) (hk : 0 < scale n) : n ≤ 24 * (scale n) ^ 3 := by
  have hs : scale n + 1 ≤ 2 * scale n := by omega
  calc
    n ≤ 3 * (scale n + 1) ^ 3 := (scale_next n).le
    _ ≤ 3 * (2 * scale n) ^ 3 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 3)
    _ = 24 * (scale n) ^ 3 := by ring

private theorem scale_div_tends_to_infinity :
    Tendsto (fun n : ℕ => scale n / 24) atTop atTop := by
  apply tendsto_atTop.2
  intro m
  apply eventually_atTop.2
  refine ⟨3 * (m * 24) ^ 3, ?_⟩
  intro n hn
  exact (Nat.le_div_iff_mul_le (by decide : 0 < (24 : ℕ))).2 (scale_ge hn)

private theorem scale_div_bound (n : ℕ) : n * (scale n / 24) ≤ (scale n) ^ 4 := by
  by_cases hk : scale n = 0
  · simp [hk]
  · calc
      n * (scale n / 24) ≤ (24 * (scale n) ^ 3) * (scale n / 24) :=
        Nat.mul_le_mul_right _ (scale_bound n (Nat.pos_of_ne_zero hk))
      _ = (scale n) ^ 3 * (scale n / 24 * 24) := by ring
      _ ≤ (scale n) ^ 3 * scale n :=
        Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      _ = (scale n) ^ 4 := by ring

private theorem exists_padded (n : ℕ) :
    ∃ S : Finset UnitSphere, S.card = n ∧
      (scale n) ^ 4 ≤ (distancePairs S (Real.sqrt 2)).card := by
  have hs : (sample (scale n)).card ≤ n := by
    rw [sample_card]
    exact scale_fits n
  obtain ⟨S, hS, hCard⟩ := pad hs
  exact ⟨S, hCard, (sample_chords (scale n)).trans (Finset.card_le_card
    (distancePairs_mono hS (Real.sqrt 2)))⟩

theorem erdos_605 :
    ∃ (d : ℝ) (f : ℕ → ℕ), 0 < d ∧ Tendsto f atTop atTop ∧
      ∀ n, ∃ S : Finset UnitSphere, S.card = n ∧
        n * f n ≤ (distancePairs S d).card := by
  refine ⟨Real.sqrt 2, fun n => scale n / 24, Real.sqrt_pos.2 (by norm_num),
    scale_div_tends_to_infinity, ?_⟩
  intro n
  obtain ⟨S, hCard, hEdges⟩ := exists_padded n
  exact ⟨S, hCard, (scale_div_bound n).trans hEdges⟩

theorem erdos_605_quantitative (n : ℕ) (hn : 3 ≤ n) :
    ∃ S : Finset UnitSphere, S.card = n ∧
      n ^ 4 ≤ 24 ^ 4 * (distancePairs S (Real.sqrt 2)).card ^ 3 := by
  have h1 : 1 ≤ scale n := scale_ge (m := 1) (by simpa using hn)
  have hpos : 0 < scale n := by omega
  obtain ⟨S, hCard, hEdges⟩ := exists_padded n
  refine ⟨S, hCard, ?_⟩
  calc
    n ^ 4 ≤ (24 * (scale n) ^ 3) ^ 4 :=
      Nat.pow_le_pow_left (scale_bound n hpos) 4
    _ = 24 ^ 4 * ((scale n) ^ 4) ^ 3 := by ring
    _ ≤ 24 ^ 4 * (distancePairs S (Real.sqrt 2)).card ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hEdges 3)

end JSP000492

#print axioms JSP000492.erdos_605
#print axioms JSP000492.erdos_605_quantitative
