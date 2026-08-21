import DomainTraces.FlatBump

/-!
# Section 5.1: construction of the domain

The ambient space is written as `E × ℝ`; `E` is the space of the barred
coordinates and the last coordinate is `y`.  All metric statements hold for
an arbitrary real normed space `E`, while smoothness uses an inner product.

The generic lemmas below are stated for any strictly monotone normalized bump.
The final `paper*` declarations specialize them to the exact function
`flatBump 1` from (5.1).
-/

open Set Filter SignType
open scoped Topology ContDiff

namespace DomainTraces
namespace DomainConstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def s (r : ℝ) (x : E) : ℝ := (‖x‖ ^ 2 - r ^ 2) / r ^ 2

noncomputable def lam (b : ℝ → ℝ) (r : ℝ) (z : E × ℝ) : ℝ :=
  (1 + 2 * z.2 / r) ^ 2 + Real.exp 1 * b (s r z.1) - 1

def omega (b : ℝ → ℝ) (r : ℝ) : Set (E × ℝ) := {z | lam b r z < 0}

noncomputable def amp (b : ℝ → ℝ) (r : ℝ) (x : E) : ℝ :=
  Real.sqrt (1 - Real.exp 1 * b (s r x))

noncomputable def yMinus (b : ℝ → ℝ) (r : ℝ) (x : E) : ℝ :=
  -r / 2 * (1 + amp b r x)

noncomputable def yPlus (b : ℝ → ℝ) (r : ℝ) (x : E) : ℝ :=
  r / 2 * (amp b r x - 1)

noncomputable def hub (r : ℝ) : E × ℝ := (0, -r / 2)

noncomputable def boundingCylinder (r : ℝ) : Set (E × ℝ) :=
  {z | ‖z.1‖ ≤ Real.sqrt 2 * r ∧
    -r * (1 + Real.sqrt 2) / 2 ≤ z.2 ∧
    z.2 ≤ r * (Real.sqrt 2 - 1) / 2}

noncomputable def planeProjection (coord : E → ℝ) (z : E × ℝ) : ℝ × ℝ :=
  (coord z.1, z.2)

noncomputable def planarCube (r : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioo (-2 * r) (2 * r) ×ˢ Set.Ioo (-2 * r) (2 * r)

lemma sq_pos {r : ℝ} (hr : 0 < r) : 0 < r ^ 2 := sq_pos_of_pos hr

lemma s_ge_neg_one {r : ℝ} (hr : 0 < r) (x : E) : -1 ≤ s r x := by
  rw [s]
  rw [le_div_iff₀ (sq_pos hr)]
  nlinarith [sq_nonneg ‖x‖]

lemma s_lt_one_iff_sq {r : ℝ} (hr : 0 < r) (x : E) :
    s r x < 1 ↔ ‖x‖ ^ 2 < 2 * r ^ 2 := by
  rw [s, div_lt_iff₀ (sq_pos hr)]
  constructor <;> intro h <;> nlinarith

lemma s_lt_zero_iff {r : ℝ} (hr : 0 < r) (x : E) :
    s r x < 0 ↔ ‖x‖ < r := by
  rw [s, div_lt_iff₀ (sq_pos hr)]
  constructor
  · intro h
    nlinarith [sq_nonneg (‖x‖ - r), norm_nonneg x]
  · intro h
    nlinarith [norm_nonneg x]

lemma s_eq_zero_iff {r : ℝ} (hr : 0 < r) (x : E) :
    s r x = 0 ↔ ‖x‖ = r := by
  rw [s, div_eq_zero_iff]
  simp only [ne_eq, (sq_pos hr).ne', or_false, sub_eq_zero]
  exact sq_eq_sq₀ (norm_nonneg x) hr.le

lemma s_lt_one_iff {r : ℝ} (hr : 0 < r) (x : E) :
    s r x < 1 ↔ ‖x‖ < Real.sqrt 2 * r := by
  rw [s_lt_one_iff_sq hr]
  have hsqrt : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr.le
  rw [← sq_lt_sq₀ (norm_nonneg x) hsqrt]
  congr 1
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

lemma continuous_s {r : ℝ} : Continuous (s (E := E) r) := by
  unfold s
  fun_prop

lemma contDiff_s [InnerProductSpace ℝ E] {r : ℝ} :
    ContDiff ℝ ∞ (s (E := E) r) := by
  unfold s
  exact ((contDiff_norm_sq ℝ).sub contDiff_const).div_const _

lemma continuous_lam {b : ℝ → ℝ} (hb : Continuous b) {r : ℝ} :
    Continuous (lam (E := E) b r) := by
  unfold lam
  have hs : Continuous (fun z : E × ℝ => s r z.1) :=
    continuous_s.comp continuous_fst
  fun_prop

lemma contDiff_lam [InnerProductSpace ℝ E]
    {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) {r : ℝ} :
    ContDiff ℝ ∞ (lam (E := E) b r) := by
  unfold lam
  have hs : ContDiff ℝ ∞ (fun z : E × ℝ => s r z.1) :=
    contDiff_s.comp contDiff_fst
  fun_prop

lemma isOpen_omega {b : ℝ → ℝ} (hb : Continuous b) {r : ℝ} :
    IsOpen (omega (E := E) b r) := by
  exact isOpen_Iio.preimage (continuous_lam hb)

lemma eb_lt_one_of_mem
    {b : ℝ → ℝ} {r : ℝ} {z : E × ℝ} (hz : z ∈ omega b r) :
    Real.exp 1 * b (s r z.1) < 1 := by
  change lam b r z < 0 at hz
  rw [lam] at hz
  nlinarith [sq_nonneg (1 + 2 * z.2 / r)]

lemma s_lt_one_of_mem
    {b : ℝ → ℝ} (hb : StrictMono b) (hb1 : Real.exp 1 * b 1 = 1)
    {r : ℝ} {z : E × ℝ} (hz : z ∈ omega b r) : s r z.1 < 1 := by
  apply hb.lt_iff_lt.mp
  have hmul : Real.exp 1 * b (s r z.1) < Real.exp 1 * b 1 := by
    rw [hb1]
    exact eb_lt_one_of_mem hz
  exact lt_of_mul_lt_mul_left hmul (Real.exp_pos 1).le

lemma x_norm_lt_of_mem
    {b : ℝ → ℝ} (hb : StrictMono b) (hb1 : Real.exp 1 * b 1 = 1)
    {r : ℝ} (hr : 0 < r) {z : E × ℝ} (hz : z ∈ omega b r) :
    ‖z.1‖ < Real.sqrt 2 * r := by
  exact (s_lt_one_iff hr _).mp (s_lt_one_of_mem hb hb1 hz)

lemma neg_one_le_eb
    {b : ℝ → ℝ} (hb : StrictMono b) (hbm1 : Real.exp 1 * b (-1) = -1)
    {r : ℝ} (hr : 0 < r) (x : E) :
    -1 ≤ Real.exp 1 * b (s r x) := by
  have hmono := hb.monotone (s_ge_neg_one hr x)
  have := mul_le_mul_of_nonneg_left hmono (Real.exp_pos 1).le
  rwa [hbm1] at this

lemma square_lt_two_of_mem
    {b : ℝ → ℝ} (hb : StrictMono b) (hbm1 : Real.exp 1 * b (-1) = -1)
    {r : ℝ} (hr : 0 < r) {z : E × ℝ} (hz : z ∈ omega b r) :
    (1 + 2 * z.2 / r) ^ 2 < 2 := by
  have hlo := neg_one_le_eb hb hbm1 hr z.1
  change lam b r z < 0 at hz
  rw [lam] at hz
  nlinarith

lemma y_bounds_of_mem
    {b : ℝ → ℝ} (hb : StrictMono b) (hbm1 : Real.exp 1 * b (-1) = -1)
    {r : ℝ} (hr : 0 < r) {z : E × ℝ} (hz : z ∈ omega b r) :
    -r * (1 + Real.sqrt 2) / 2 < z.2 ∧
      z.2 < r * (Real.sqrt 2 - 1) / 2 := by
  have hsq := square_lt_two_of_mem hb hbm1 hr hz
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have habs : -(Real.sqrt 2) < 1 + 2 * z.2 / r ∧
      1 + 2 * z.2 / r < Real.sqrt 2 := by
    apply abs_lt_of_sq_lt_sq'
    · simpa [hsqrt_sq]
    · exact hsqrt
  have hlow := mul_lt_mul_of_pos_left habs.1 hr
  have hupp := mul_lt_mul_of_pos_left habs.2 hr
  field_simp [hr.ne'] at hlow hupp
  constructor <;> nlinarith

lemma mem_omega_iff
    {b : ℝ → ℝ} (hb : StrictMono b) (hb1 : Real.exp 1 * b 1 = 1)
    {r : ℝ} (hr : 0 < r) (z : E × ℝ) :
    z ∈ omega b r ↔
      ‖z.1‖ < Real.sqrt 2 * r ∧ yMinus b r z.1 < z.2 ∧ z.2 < yPlus b r z.1 := by
  constructor
  · intro hz
    have hx := x_norm_lt_of_mem hb hb1 hr hz
    have hsq : (1 + 2 * z.2 / r) ^ 2 < 1 - Real.exp 1 * b (s r z.1) := by
      change lam b r z < 0 at hz
      rw [lam] at hz
      linarith
    have hrad : 0 < 1 - Real.exp 1 * b (s r z.1) :=
      lt_of_le_of_lt (sq_nonneg _) hsq
    have hsqrt_sq : (amp b r z.1) ^ 2 = 1 - Real.exp 1 * b (s r z.1) := by
      rw [amp, Real.sq_sqrt hrad.le]
    have habs : -amp b r z.1 < 1 + 2 * z.2 / r ∧
        1 + 2 * z.2 / r < amp b r z.1 := by
      apply abs_lt_of_sq_lt_sq'
      · simpa [hsqrt_sq]
      · exact Real.sqrt_nonneg _
    have hlow := mul_lt_mul_of_pos_left habs.1 hr
    have hupp := mul_lt_mul_of_pos_left habs.2 hr
    field_simp [hr.ne'] at hlow hupp
    refine ⟨hx, ?_, ?_⟩
    · unfold yMinus
      nlinarith
    · unfold yPlus
      nlinarith
  · rintro ⟨hx, hlow, hupp⟩
    have hs : s r z.1 < 1 := (s_lt_one_iff hr _).2 hx
    have hb_lt : b (s r z.1) < b 1 := hb hs
    have heb_lt : Real.exp 1 * b (s r z.1) < 1 := by
      calc
        Real.exp 1 * b (s r z.1) < Real.exp 1 * b 1 :=
          mul_lt_mul_of_pos_left hb_lt (Real.exp_pos 1)
        _ = 1 := hb1
    have hrad : 0 < 1 - Real.exp 1 * b (s r z.1) := sub_pos.2 heb_lt
    have hsqrt_sq : (amp b r z.1) ^ 2 = 1 - Real.exp 1 * b (s r z.1) := by
      rw [amp, Real.sq_sqrt hrad.le]
    unfold yMinus at hlow
    unfold yPlus at hupp
    have hlow' : -amp b r z.1 < 1 + 2 * z.2 / r := by
      apply lt_of_mul_lt_mul_left (a := r) (b := -amp b r z.1)
      · field_simp [hr.ne']
        nlinarith [hlow]
      · exact hr.le
    have hupp' : 1 + 2 * z.2 / r < amp b r z.1 := by
      apply lt_of_mul_lt_mul_left (a := r) (c := amp b r z.1)
      · field_simp [hr.ne']
        nlinarith [hupp]
      · exact hr.le
    have hsq : (1 + 2 * z.2 / r) ^ 2 < (amp b r z.1) ^ 2 :=
      sq_lt_sq' hlow' hupp'
    change lam b r z < 0
    rw [lam]
    nlinarith [hsqrt_sq]

lemma hub_mem_omega
    {b : ℝ → ℝ} (hbm1 : Real.exp 1 * b (-1) = -1)
    {r : ℝ} (hr : 0 < r) : hub (E := E) r ∈ omega b r := by
  change lam b r (hub r) < 0
  have hs : s r (0 : E) = -1 := by
    rw [s, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    field_simp [hr.ne']
    ring
  rw [lam, hub, hs, hbm1]
  field_simp [hr.ne']
  norm_num

lemma starConvex_omega
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    {r : ℝ} (hr : 0 < r) : StarConvex ℝ (hub (E := E) r) (omega bump r) := by
  intro z hz a c ha hc hac
  change lam bump r (a • hub r + c • z) < 0
  have hc1 : c ≤ 1 := by linarith
  have hnorm : ‖c • z.1‖ ≤ ‖z.1‖ := by
    rw [norm_smul, Real.norm_of_nonneg hc]
    exact mul_le_of_le_one_left (norm_nonneg _) hc1
  have hsle : s r (c • z.1) ≤ s r z.1 := by
    rw [s, s, div_le_div_iff_of_pos_right (sq_pos hr)]
    nlinarith [sq_nonneg (‖c • z.1‖ - ‖z.1‖), norm_nonneg (c • z.1), norm_nonneg z.1]
  have hble := hb.monotone hsle
  have hc_sq : c ^ 2 ≤ 1 := by nlinarith
  have hsqmul : c ^ 2 * (1 + 2 * z.2 / r) ^ 2 ≤ (1 + 2 * z.2 / r) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc_sq (sq_nonneg (1 + 2 * z.2 / r))]
  have hcoord : 1 + 2 * (a * (-r / 2) + c * z.2) / r =
      c * (1 + 2 * z.2 / r) := by
    field_simp [hr.ne']
    nlinarith [hac]
  change lam bump r z < 0 at hz
  unfold lam at hz ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, hub,
    Prod.fst, Prod.snd, smul_zero, zero_add, smul_eq_mul]
  change (1 + 2 * (a * (-r / 2) + c * z.2) / r) ^ 2 +
    Real.exp 1 * bump (s r (c • z.1)) - 1 < 0
  rw [hcoord, mul_pow]
  have heb := mul_le_mul_of_nonneg_left hble (Real.exp_pos 1).le
  linarith

lemma isPathConnected_omega
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    (hbm1 : Real.exp 1 * bump (-1) = -1)
    {r : ℝ} (hr : 0 < r) : IsPathConnected (omega (E := E) bump r) := by
  have hstar : StarConvex ℝ (hub (E := E) r) (omega (E := E) bump r) :=
    starConvex_omega hb hr
  have hhub : hub (E := E) r ∈ omega (E := E) bump r := hub_mem_omega hbm1 hr
  exact hstar.isPathConnected hhub

lemma omega_subset_ball
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    (hb1 : Real.exp 1 * bump 1 = 1)
    (hbm1 : Real.exp 1 * bump (-1) = -1)
    {r : ℝ} (hr : 0 < r) :
    omega (E := E) bump r ⊆ Metric.ball 0 (2 * r) := by
  intro z hz
  have hx := x_norm_lt_of_mem hb hb1 hr hz
  have hy := y_bounds_of_mem hb hbm1 hr hz
  have hsqrt_nonneg := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_lt_two : Real.sqrt 2 < 2 := by nlinarith
  have hrsqrt := mul_lt_mul_of_pos_right hsqrt_lt_two hr
  have hx' : ‖z.1‖ < 2 * r := lt_trans hx (by nlinarith)
  have hy' : |z.2| < 2 * r := by
    rw [abs_lt]
    constructor <;> nlinarith [hy.1, hy.2, hrsqrt]
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
  simpa [Real.norm_eq_abs] using max_lt hx' hy'

lemma isBounded_omega
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    (hb1 : Real.exp 1 * bump 1 = 1)
    (hbm1 : Real.exp 1 * bump (-1) = -1)
    {r : ℝ} (hr : 0 < r) : Bornology.IsBounded (omega (E := E) bump r) :=
  Metric.isBounded_ball.subset (omega_subset_ball hb hb1 hbm1 hr)

lemma isClosed_boundingCylinder {r : ℝ} :
    IsClosed (boundingCylinder (E := E) r) := by
  unfold boundingCylinder
  exact (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter <|
    (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const)

lemma closure_omega_subset_boundingCylinder
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    (hb1 : Real.exp 1 * bump 1 = 1)
    (hbm1 : Real.exp 1 * bump (-1) = -1)
    {r : ℝ} (hr : 0 < r) :
    closure (omega (E := E) bump r) ⊆ boundingCylinder r := by
  apply closure_minimal _ isClosed_boundingCylinder
  intro z hz
  exact ⟨(x_norm_lt_of_mem hb hb1 hr hz).le, (y_bounds_of_mem hb hbm1 hr hz).imp le_of_lt le_of_lt⟩

lemma projection_closure_subset_planarCube
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    (hb1 : Real.exp 1 * bump 1 = 1)
    (hbm1 : Real.exp 1 * bump (-1) = -1)
    {r : ℝ} (hr : 0 < r) (coord : E → ℝ)
    (hcoord : ∀ x, |coord x| ≤ ‖x‖) :
    planeProjection coord '' closure (omega (E := E) bump r) ⊆ planarCube r := by
  rintro _ ⟨z, hz, rfl⟩
  have hbounds := closure_omega_subset_boundingCylinder hb hb1 hbm1 hr hz
  rcases hbounds with ⟨hx, hylow, hyupp⟩
  have hsqrt_nonneg := Real.sqrt_nonneg 2
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_lt_two : Real.sqrt 2 < 2 := by nlinarith
  have hrsqrt := mul_lt_mul_of_pos_right hsqrt_lt_two hr
  have hxabs : |coord z.1| < 2 * r := lt_of_le_of_lt (hcoord z.1) (lt_of_le_of_lt hx hrsqrt)
  have hyabs : |z.2| < 2 * r := by
    rw [abs_lt]
    constructor <;> nlinarith [hylow, hyupp, hrsqrt]
  change coord z.1 ∈ Set.Ioo (-2 * r) (2 * r) ∧ z.2 ∈ Set.Ioo (-2 * r) (2 * r)
  constructor
  · change -2 * r < coord z.1 ∧ coord z.1 < 2 * r
    rcases abs_lt.mp hxabs with ⟨hl, hu⟩
    constructor <;> nlinarith
  · change -2 * r < z.2 ∧ z.2 < 2 * r
    rcases abs_lt.mp hyabs with ⟨hl, hu⟩
    constructor <;> nlinarith

def zeroLevel (bump : ℝ → ℝ) (r : ℝ) : Set (E × ℝ) :=
  {z | lam bump r z = 0}

/-! ## Curve certificates for regular zero levels -/

/-- A function has a nonzero directional derivative at `z` if its restriction
to some affine line through `z` has a nonzero derivative there. -/
def HasNonzeroDirectionalDerivativeAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → ℝ) (z : V) : Prop :=
  ∃ v d, HasDerivAt (fun t : ℝ ↦ F (z + t • v)) d 0 ∧ d ≠ 0

/-- Every point of the zero level has a nonzero directional derivative. -/
def IsRegularZeroLevel
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : V → ℝ) : Prop :=
  ∀ z, F z = 0 → HasNonzeroDirectionalDerivativeAt F z

/-- A nonzero directional derivative forces the Fréchet derivative to be
nonzero whenever the latter exists.  This is the differential hypothesis
used by the regular-level-set theorem. -/
lemma HasNonzeroDirectionalDerivativeAt.fderiv_ne_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → ℝ} {z : V} (h : HasNonzeroDirectionalDerivativeAt F z)
    (hF : DifferentiableAt ℝ F z) : fderiv ℝ F z ≠ 0 := by
  rcases h with ⟨v, d, hd, hd0⟩
  intro hfzero
  have hcurve : HasDerivAt (fun t : ℝ ↦ z + t • v) v 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) z).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const v) using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
    · simp
  have hF' : HasFDerivAt F (fderiv ℝ F z) (z + (0 : ℝ) • v) := by
    simpa using hF.hasFDerivAt
  have hcomp := hF'.comp_hasDerivAt 0 hcurve
  have heq := hd.unique hcomp
  rw [hfzero] at heq
  simp at heq
  exact hd0 heq

/-- A slightly more general curve certificate used to turn a nonzero
derivative into a boundary point. -/
def CurveRegularAt {X : Type*} [MetricSpace X] (F : X → ℝ) (z : X) : Prop :=
  ∃ (γ : ℝ → X) (d : ℝ),
    γ 0 = z ∧ Tendsto γ (𝓝 0) (𝓝 z) ∧ HasDerivAt (F ∘ γ) d 0 ∧ d ≠ 0

lemma HasNonzeroDirectionalDerivativeAt.curveRegularAt
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → ℝ} {z : V} (h : HasNonzeroDirectionalDerivativeAt F z) :
    CurveRegularAt F z := by
  rcases h with ⟨v, d, hd, hd0⟩
  refine ⟨fun t : ℝ ↦ z + t • v, d, by simp, ?_, ?_, hd0⟩
  · have ht : Tendsto (fun t : ℝ ↦ t) (𝓝 0) (𝓝 0) := tendsto_id
    have hcurve := (tendsto_const_nhds (x := z)).add (ht.smul_const v)
    convert! hcurve using 1
    simp
  · convert! hd using 1

/-- A nonzero curve derivative through a zero of `F` shows that both signs of
`F` occur arbitrarily close to the point, hence the point lies in the
frontier of `{F < 0}`. -/
lemma frontier_lt_of_curveRegularAt {X : Type*} [MetricSpace X]
    {F : X → ℝ} {z : X} (hFz : F z = 0) (hreg : CurveRegularAt F z) :
    z ∈ frontier {x | F x < 0} := by
  rcases hreg with ⟨γ, d, hγ0, hγ, hd, hd0⟩
  have hcomp0 : (F ∘ γ) 0 = 0 := by
    simp only [Function.comp_apply, hγ0, hFz]
  have hderiv : deriv (F ∘ γ) 0 = d := hd.deriv
  rw [frontier_eq_closure_inter_closure]
  constructor
  · rw [mem_closure_iff_nhds]
    intro U hU
    have hUγ : ∀ᶠ t in 𝓝 0, γ t ∈ U := hγ.eventually hU
    rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · have hsign : ∀ᶠ t in 𝓝 0, sign ((F ∘ γ) t) = sign (0 - t) := by
        apply eventually_nhdsWithin_sign_eq_of_deriv_neg
        · simpa [hderiv] using hdneg
        · exact hcomp0
      have hall : ∀ᶠ t in 𝓝[>] 0,
          γ t ∈ U ∧ sign ((F ∘ γ) t) = sign (0 - t) ∧ t ∈ Ioi 0 := by
        filter_upwards [hUγ.filter_mono inf_le_left,
          hsign.filter_mono inf_le_left, self_mem_nhdsWithin]
        with t htU htSign ht
        exact ⟨htU, htSign, ht⟩
      rcases hall.exists with ⟨t, htU, hsign', ht⟩
      refine ⟨γ t, htU, ?_⟩
      change F (γ t) < 0
      apply sign_eq_neg_one_iff.mp
      change sign ((F ∘ γ) t) = -1
      exact hsign'.trans (sign_neg (sub_neg.mpr ht))
    · have hsign : ∀ᶠ t in 𝓝 0, sign ((F ∘ γ) t) = sign (t - 0) := by
        apply eventually_nhdsWithin_sign_eq_of_deriv_pos
        · simpa [hderiv] using hdpos
        · exact hcomp0
      have hall : ∀ᶠ t in 𝓝[<] 0,
          γ t ∈ U ∧ sign ((F ∘ γ) t) = sign (t - 0) ∧ t ∈ Iio 0 := by
        filter_upwards [hUγ.filter_mono inf_le_left,
          hsign.filter_mono inf_le_left, self_mem_nhdsWithin]
        with t htU htSign ht
        exact ⟨htU, htSign, ht⟩
      rcases hall.exists with ⟨t, htU, hsign', ht⟩
      refine ⟨γ t, htU, ?_⟩
      change F (γ t) < 0
      apply sign_eq_neg_one_iff.mp
      change sign ((F ∘ γ) t) = -1
      exact hsign'.trans (sign_neg (sub_neg.mpr ht))
  · rw [mem_closure_iff_nhds]
    intro U hU
    have hUγ : ∀ᶠ t in 𝓝 0, γ t ∈ U := hγ.eventually hU
    rcases lt_or_gt_of_ne hd0 with hdneg | hdpos
    · have hsign : ∀ᶠ t in 𝓝 0, sign ((F ∘ γ) t) = sign (0 - t) := by
        apply eventually_nhdsWithin_sign_eq_of_deriv_neg
        · simpa [hderiv] using hdneg
        · exact hcomp0
      have hall : ∀ᶠ t in 𝓝[<] 0,
          γ t ∈ U ∧ sign ((F ∘ γ) t) = sign (0 - t) ∧ t ∈ Iio 0 := by
        filter_upwards [hUγ.filter_mono inf_le_left,
          hsign.filter_mono inf_le_left, self_mem_nhdsWithin]
        with t htU htSign ht
        exact ⟨htU, htSign, ht⟩
      rcases hall.exists with ⟨t, htU, hsign', ht⟩
      refine ⟨γ t, htU, ?_⟩
      change ¬F (γ t) < 0
      apply not_lt_of_ge
      exact (sign_eq_one_iff.mp (by
        change sign ((F ∘ γ) t) = 1
        exact hsign'.trans (sign_pos (sub_pos.mpr ht)))).le
    · have hsign : ∀ᶠ t in 𝓝 0, sign ((F ∘ γ) t) = sign (t - 0) := by
        apply eventually_nhdsWithin_sign_eq_of_deriv_pos
        · simpa [hderiv] using hdpos
        · exact hcomp0
      have hall : ∀ᶠ t in 𝓝[>] 0,
          γ t ∈ U ∧ sign ((F ∘ γ) t) = sign (t - 0) ∧ t ∈ Ioi 0 := by
        filter_upwards [hUγ.filter_mono inf_le_left,
          hsign.filter_mono inf_le_left, self_mem_nhdsWithin]
        with t htU htSign ht
        exact ⟨htU, htSign, ht⟩
      rcases hall.exists with ⟨t, htU, hsign', ht⟩
      refine ⟨γ t, htU, ?_⟩
      change ¬F (γ t) < 0
      apply not_lt_of_ge
      exact (sign_eq_one_iff.mp (by
        change sign ((F ∘ γ) t) = 1
        exact hsign'.trans (sign_pos (sub_pos.mpr ht)))).le

lemma lambda_slice_zero {bump : ℝ → ℝ} {r : ℝ} (x : E) :
    lam bump r (x, 0) = Real.exp 1 * bump (s r x) := by
  rw [lam]
  ring

lemma mem_omega_slice_zero_iff
    {bump : ℝ → ℝ} (hb : StrictMono bump) (hb0 : bump 0 = 0)
    {r : ℝ} (hr : 0 < r) (x : E) :
    (x, 0) ∈ omega bump r ↔ ‖x‖ < r := by
  rw [omega, Set.mem_setOf_eq, lambda_slice_zero]
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have hmul : Real.exp 1 * bump (s r x) < 0 ↔ bump (s r x) < 0 := by
    constructor
    · intro h
      apply lt_of_mul_lt_mul_left (a := Real.exp 1) (b := bump (s r x)) (c := 0)
      · simpa using h
      · exact he.le
    · intro h
      exact mul_neg_of_pos_of_neg he h
  have hbneg : bump (s r x) < 0 ↔ s r x < 0 := by
    calc
      bump (s r x) < 0 ↔ bump (s r x) < bump 0 := by rw [hb0]
      _ ↔ s r x < 0 := hb.lt_iff_lt
  rw [hmul, hbneg, s_lt_zero_iff hr]

lemma mem_zeroLevel_slice_zero_iff
    {bump : ℝ → ℝ} (hb : StrictMono bump) (hb0 : bump 0 = 0)
    {r : ℝ} (hr : 0 < r) (x : E) :
    (x, 0) ∈ zeroLevel bump r ↔ ‖x‖ = r := by
  rw [zeroLevel, Set.mem_setOf_eq, lambda_slice_zero, mul_eq_zero]
  simp only [(Real.exp_ne_zero 1), false_or]
  have hzero : bump (s r x) = 0 ↔ s r x = 0 := by
    calc
      bump (s r x) = 0 ↔ bump (s r x) = bump 0 := by rw [hb0]
      _ ↔ s r x = 0 := hb.injective.eq_iff
  rw [hzero, s_eq_zero_iff hr]

lemma frontier_omega_subset_zeroLevel
    {bump : ℝ → ℝ} (hb : Continuous bump) {r : ℝ} :
    frontier (omega (E := E) bump r) ⊆ zeroLevel bump r := by
  simpa only [omega, zeroLevel] using
    (frontier_lt_subset_eq (continuous_lam hb) continuous_const)

lemma s_eq_one_of_lambda_eq_zero_at_center
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    (hb1 : Real.exp 1 * bump 1 = 1)
    {r : ℝ} (hr : 0 < r) (x : E)
    (hzero : lam bump r (x, -r / 2) = 0) : s r x = 1 := by
  have heb : Real.exp 1 * bump (s r x) = 1 := by
    rw [lam] at hzero
    field_simp [hr.ne'] at hzero
    nlinarith
  have heq : bump (s r x) = bump 1 := by
    apply mul_left_cancel₀ (Real.exp_ne_zero 1)
    exact heb.trans hb1.symm
  exact hb.injective heq

lemma norm_eq_sqrt_two_mul_of_lambda_eq_zero_at_center
    {bump : ℝ → ℝ} (hb : StrictMono bump)
    (hb1 : Real.exp 1 * bump 1 = 1)
    {r : ℝ} (hr : 0 < r) (x : E)
    (hzero : lam bump r (x, -r / 2) = 0) : ‖x‖ = Real.sqrt 2 * r := by
  have hs := s_eq_one_of_lambda_eq_zero_at_center hb hb1 hr x hzero
  have hsq : ‖x‖ ^ 2 = 2 * r ^ 2 := by
    rw [s] at hs
    field_simp [hr.ne'] at hs
    nlinarith
  have hright : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr.le
  apply (sq_eq_sq₀ (norm_nonneg x) hright).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  nlinarith

lemma mem_frontier_slice_zero_iff
    {bump : ℝ → ℝ} (hb : StrictMono bump) (hbcont : Continuous bump) (hb0 : bump 0 = 0)
    {r : ℝ} (hr : 0 < r) (x : E) :
    (x, 0) ∈ frontier (omega bump r) ↔ ‖x‖ = r := by
  constructor
  · intro hx
    exact (mem_zeroLevel_slice_zero_iff hb hb0 hr x).1
      (frontier_omega_subset_zeroLevel hbcont hx)
  · intro hxnorm
    rw [frontier_eq_closure_inter_closure]
    constructor
    · rw [Metric.mem_closure_iff]
      intro ε hε
      let δ := min (ε / 2) (r / 2)
      have hδpos : 0 < δ := lt_min (half_pos hε) (half_pos hr)
      have hδleε : δ ≤ ε / 2 := min_le_left _ _
      have hδler : δ ≤ r / 2 := min_le_right _ _
      refine ⟨(x, -δ), ?_, ?_⟩
      · change lam bump r (x, -δ) < 0
        have hs : s r x = 0 := (s_eq_zero_iff hr x).2 hxnorm
        rw [lam, hs, hb0]
        field_simp [hr.ne']
        nlinarith
      · rw [Prod.dist_eq]
        simp only [dist_self, Real.dist_eq, zero_sub, neg_neg, abs_of_pos hδpos,
          max_eq_right hδpos.le]
        linarith
    · apply subset_closure
      change ¬lam bump r (x, 0) < 0
      have hlevel : lam bump r (x, 0) = 0 := by
        rw [lambda_slice_zero]
        have hs : s r x = 0 := (s_eq_zero_iff hr x).2 hxnorm
        rw [hs, hb0, mul_zero]
      rw [hlevel]
      exact lt_irrefl 0

/-! ## Specialization to the function and domain in the paper -/

/-- The function `𝓫` in equation (5.1). -/
noncomputable abbrev paperBump : ℝ → ℝ := flatBump 1

/-- The defining function `Λ` in equation (5.2). -/
noncomputable abbrev paperLambda (r : ℝ) : E × ℝ → ℝ :=
  lam (E := E) paperBump r

/-- The open set `Ω = {Λ < 0}`. -/
abbrev paperOmega (r : ℝ) : Set (E × ℝ) := omega (E := E) paperBump r

noncomputable abbrev paperYMinus (r : ℝ) : E → ℝ := yMinus paperBump r
noncomputable abbrev paperYPlus (r : ℝ) : E → ℝ := yPlus paperBump r

@[simp] lemma exp_mul_paperBump_one : Real.exp 1 * paperBump 1 = 1 := by
  unfold paperBump
  rw [flatBump.one_one_eq_inv_exp]
  exact mul_inv_cancel₀ (Real.exp_ne_zero 1)

@[simp] lemma exp_mul_paperBump_neg_one : Real.exp 1 * paperBump (-1) = -1 := by
  unfold paperBump
  rw [flatBump.neg, flatBump.one_one_eq_inv_exp]
  field_simp [Real.exp_ne_zero]

@[simp] lemma paperBump_zero : paperBump 0 = 0 := flatBump.zero 1

theorem paperBump_strictMono : StrictMono paperBump := flatBump.strictMono zero_lt_one

theorem paperBump_contDiff : ContDiff ℝ ∞ paperBump := by
  unfold paperBump
  exact flatBump.contDiff 1 zero_lt_one

theorem paperOmega_isOpen {r : ℝ} : IsOpen (paperOmega (E := E) r) :=
  isOpen_omega paperBump_contDiff.continuous

theorem paperOmega_membership {r : ℝ} (hr : 0 < r) (z : E × ℝ) :
    z ∈ paperOmega r ↔
      ‖z.1‖ < Real.sqrt 2 * r ∧
        paperYMinus r z.1 < z.2 ∧ z.2 < paperYPlus r z.1 :=
  mem_omega_iff paperBump_strictMono exp_mul_paperBump_one hr z

theorem paperOmega_isBounded {r : ℝ} (hr : 0 < r) :
    Bornology.IsBounded (paperOmega (E := E) r) :=
  isBounded_omega paperBump_strictMono exp_mul_paperBump_one
    exp_mul_paperBump_neg_one hr

theorem paperOmega_isPathConnected {r : ℝ} (hr : 0 < r) :
    IsPathConnected (paperOmega (E := E) r) :=
  isPathConnected_omega paperBump_strictMono exp_mul_paperBump_neg_one hr

theorem paper_projection_closure_subset_cube {r : ℝ} (hr : 0 < r)
    (coord : E → ℝ) (hcoord : ∀ x, |coord x| ≤ ‖x‖) :
    planeProjection coord '' closure (paperOmega (E := E) r) ⊆ planarCube r :=
  projection_closure_subset_planarCube paperBump_strictMono exp_mul_paperBump_one
    exp_mul_paperBump_neg_one hr coord hcoord

theorem paperOmega_slice_zero {r : ℝ} (hr : 0 < r) (x : E) :
    (x, 0) ∈ paperOmega r ↔ ‖x‖ < r :=
  mem_omega_slice_zero_iff paperBump_strictMono paperBump_zero hr x

theorem paperOmega_frontier_slice_zero {r : ℝ} (hr : 0 < r) (x : E) :
    (x, 0) ∈ frontier (paperOmega r) ↔ ‖x‖ = r :=
  mem_frontier_slice_zero_iff paperBump_strictMono paperBump_contDiff.continuous
    paperBump_zero hr x

theorem paperLambda_contDiff [InnerProductSpace ℝ E] {r : ℝ} :
    ContDiff ℝ ∞ (paperLambda (E := E) r) :=
  contDiff_lam paperBump_contDiff

/-- Corrected version of the compressed step in the paper: the lower-equator
level-set equation gives `s x = 1`, not merely `(s x)² = 1`. -/
theorem paper_s_eq_one_at_lower_equator {r : ℝ} (hr : 0 < r) (x : E)
    (hzero : paperLambda r (x, -r / 2) = 0) : s r x = 1 :=
  s_eq_one_of_lambda_eq_zero_at_center paperBump_strictMono
    exp_mul_paperBump_one hr x hzero

theorem paper_norm_eq_sqrt_two_at_lower_equator {r : ℝ} (hr : 0 < r) (x : E)
    (hzero : paperLambda r (x, -r / 2) = 0) : ‖x‖ = Real.sqrt 2 * r :=
  norm_eq_sqrt_two_mul_of_lambda_eq_zero_at_center paperBump_strictMono
    exp_mul_paperBump_one hr x hzero

/-! ### A regularity certificate for the zero level of `paperLambda` -/

/-- Away from the lower equator, the vertical derivative is the nonzero
component displayed in the paper. -/
lemma paperLambda_hasDerivAt_vertical {r : ℝ} (x : E) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ paperLambda (E := E) r ((x, y) + t • ((0 : E), (1 : ℝ))))
      (4 / r * (1 + 2 * y / r)) 0 := by
  have hbase : HasDerivAt (fun t : ℝ ↦ 1 + 2 * (y + t) / r) (2 / r) 0 := by
    convert! ((((hasDerivAt_id (𝕜 := ℝ) 0).const_add y).const_mul 2).div_const r).const_add 1
      using 1 <;> ring
  have hsq := hbase.pow 2
  have hall := hsq.add_const (Real.exp 1 * paperBump (s r x) - 1)
  convert! hall using 1
  · funext t
    simp only [paperLambda, lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_zero, add_zero, smul_eq_mul, mul_one, Pi.pow_apply]
    ring
  · norm_num
    ring

/-- The derivative of `s` along the radial line `x + t x`.  This only uses
norm homogeneity, so no inner product structure is needed. -/
lemma s_hasDerivAt_radial {r : ℝ} (x : E) :
    HasDerivAt (fun t : ℝ ↦ s r (x + t • x)) (2 * ‖x‖ ^ 2 / r ^ 2) 0 := by
  have hline : HasDerivAt (fun t : ℝ ↦ (1 + t) * ‖x‖) ‖x‖ 0 := by
    convert! ((hasDerivAt_id (𝕜 := ℝ) 0).const_add 1).mul_const ‖x‖ using 1 <;> ring
  have hpoly := ((hline.pow 2).sub_const (r ^ 2)).div_const (r ^ 2)
  have hpoly' : HasDerivAt
      (fun t : ℝ ↦ (((1 + t) * ‖x‖) ^ 2 - r ^ 2) / r ^ 2)
      (2 * ‖x‖ ^ 2 / r ^ 2) 0 := by
    convert! hpoly using 1 <;> ring
  refine hpoly'.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t ht
  rw [s]
  have hscalar : ‖(1 + t : ℝ)‖ = 1 + t := by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hvec : x + t • x = (1 + t) • x := by rw [add_smul, one_smul]
  rw [hvec, norm_smul, hscalar]

/-- At the exceptional height `y = -r/2`, the radial derivative is exactly
`8`.  The proof uses `s = 1`, `‖x‖ = √2 r`, and
`flatBump.hasDerivAt_one`. -/
lemma paperLambda_hasDerivAt_radial_at_center {r : ℝ} (hr : 0 < r) (x : E)
    (hzero : paperLambda r (x, -r / 2) = 0) :
    HasDerivAt
      (fun t : ℝ ↦ paperLambda (E := E) r
        ((x, -r / 2) + t • (x, (0 : ℝ)))) 8 0 := by
  have hs : s r x = 1 := paper_s_eq_one_at_lower_equator hr x hzero
  have hnorm : ‖x‖ = Real.sqrt 2 * r :=
    paper_norm_eq_sqrt_two_at_lower_equator hr x hzero
  have hsderiv := s_hasDerivAt_radial (r := r) x
  have hbAt : HasDerivAt (flatBump 1) (2 * Real.exp (-1))
      (s r (x + (0 : ℝ) • x)) := by
    simpa [hs] using flatBump.hasDerivAt_one 1
  have hb := hbAt.comp 0 hsderiv
  have hscaled := hb.const_mul (Real.exp 1)
  have hfull := hscaled.add_const (-1)
  convert! hfull using 1
  · funext t
    simp only [paperLambda, lam, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, add_zero, smul_eq_mul, mul_zero, add_zero]
    have hcenter : (1 + 2 * (-r / 2) / r) ^ 2 = 0 := by
      field_simp [hr.ne']
      ring
    rw [hcenter, zero_add]
    rfl
  · have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hexp : Real.exp 1 * Real.exp (-1) = 1 := by
      rw [Real.exp_neg]
      exact mul_inv_cancel₀ (Real.exp_ne_zero 1)
    rw [hnorm, mul_pow, hsqrt_sq]
    field_simp [hr.ne']
    nlinarith

/-- `paperLambda` has a nonzero derivative in some direction at every point
of its zero level.  The vertical direction works unless `y = -r/2`; at that
height the radial direction has derivative `8`. -/
theorem paperLambda_isRegularZeroLevel {r : ℝ} (hr : 0 < r) :
    IsRegularZeroLevel (paperLambda (E := E) r) := by
  rintro ⟨x, y⟩ hzero
  by_cases hy : y = -r / 2
  · refine ⟨(x, (0 : ℝ)), 8, ?_, by norm_num⟩
    have hradial := paperLambda_hasDerivAt_radial_at_center hr x (by simpa [hy] using hzero)
    simpa [hy] using hradial
  · refine ⟨((0 : E), (1 : ℝ)), 4 / r * (1 + 2 * y / r),
      paperLambda_hasDerivAt_vertical x y, ?_⟩
    apply mul_ne_zero
    · exact div_ne_zero (by norm_num) hr.ne'
    · intro hfac
      apply hy
      field_simp [hr.ne'] at hfac ⊢
      linarith

/-- Fréchet-derivative form of the regularity statement required by the
regular-level-set theorem. -/
theorem paperLambda_fderiv_ne_zero_on_zeroLevel [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (z : E × ℝ) (hz : paperLambda r z = 0) :
    fderiv ℝ (paperLambda r) z ≠ 0 := by
  apply (paperLambda_isRegularZeroLevel (E := E) hr z hz).fderiv_ne_zero
  exact (paperLambda_contDiff (E := E)).differentiable (by simp) z

/-- The regularity certificate supplies the missing reverse inclusion from
the zero level to the frontier. -/
theorem paper_zeroLevel_subset_frontier {r : ℝ} (hr : 0 < r) :
    zeroLevel (E := E) paperBump r ⊆ frontier (paperOmega r) := by
  intro z hz
  have hzero : paperLambda r z = 0 := hz
  have hreg := (paperLambda_isRegularZeroLevel (E := E) hr z hzero).curveRegularAt
  change z ∈ frontier {w | paperLambda r w < 0}
  exact frontier_lt_of_curveRegularAt hzero hreg

/-- For the paper's defining function, the topological boundary is exactly
its zero level. -/
theorem paperOmega_frontier_eq_zeroLevel {r : ℝ} (hr : 0 < r) :
    frontier (paperOmega (E := E) r) = zeroLevel paperBump r := by
  apply Set.Subset.antisymm
  · exact frontier_omega_subset_zeroLevel paperBump_contDiff.continuous
  · exact paper_zeroLevel_subset_frontier hr

/-- Complete regular-defining-function certificate for the boundary.  In
finite-dimensional Euclidean instances, the regular-level-set theorem turns
this data into the paper's `C∞` hypersurface conclusion. -/
theorem paper_regular_defining_function [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (paperLambda (E := E) r) ∧
      frontier (paperOmega (E := E) r) = zeroLevel paperBump r ∧
        ∀ z : E × ℝ, paperLambda (E := E) r z = 0 →
          fderiv ℝ (paperLambda (E := E) r) z ≠ 0 := by
  exact ⟨paperLambda_contDiff, paperOmega_frontier_eq_zeroLevel hr,
    paperLambda_fderiv_ne_zero_on_zeroLevel hr⟩

/-- A compact conjunction of the open/bounded/path-connected conclusions of
Section 5.1. -/
theorem paper_domain_basic_properties {r : ℝ} (hr : 0 < r) :
    IsOpen (paperOmega (E := E) r) ∧
      Bornology.IsBounded (paperOmega (E := E) r) ∧
        IsPathConnected (paperOmega (E := E) r) :=
  ⟨paperOmega_isOpen (E := E), paperOmega_isBounded (E := E) hr,
    paperOmega_isPathConnected (E := E) hr⟩

end DomainConstruction
end DomainTraces
