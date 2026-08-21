import DomainTraces.DomainConstruction

/-!
# Smooth boundary traces in Section 5.2

This file formalizes the algebraic and analytic reduction in Section 5.2.

The results of Sections 3--4 used by the paper are collected in
`PlanarInput`.  In particular, its `gradient` is the chosen planar weak
gradient and its weak Marcinkiewicz estimate is recorded with the elementary
tail predicate `WeakTailBoundOn`.  This avoids pretending that mathlib already
contains the required first-order Sobolev--Marcinkiewicz and trace theories.

For the same reason, `HasSmoothTraceExtension` states exactly the smooth
extension conclusion used in the argument, while `TraceInterface` permits a
later development of a genuine zero-trace Sobolev space to be connected to
the present formalization.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal Topology ContDiff BigOperators

namespace DomainTraces
namespace SmoothBoundaryTraces

open DomainConstruction

/-! ## Cylindrical extension of planar data -/

/-- In dimension `k + 2` we write a point as `((x₁, z), y)`, where `z`
contains the `k` passive coordinates. -/
abbrev Cylinder (Z : Type*) := (ℝ × Z) × ℝ

/-- Projection onto the active `(x₁,y)`-plane, denoted `π_{1;2}` in the
paper. -/
def planarProjection {Z : Type*} (x : Cylinder Z) : ℝ × ℝ :=
  (x.1.1, x.2)

/-- Cylindrical extension of a planar scalar function. -/
def cylindricalLift {Z : Type*} (v : ℝ × ℝ → ℝ) (x : Cylinder Z) : ℝ :=
  v (planarProjection x)

/-- Cylindrical extension of a planar gradient: all passive components are
zero. -/
def cylindricalGradient {Z : Type*} [Zero Z]
    (g : ℝ × ℝ → ℝ × ℝ) (x : Cylinder Z) : Cylinder Z :=
  (((g (planarProjection x)).1, 0), (g (planarProjection x)).2)

@[simp] theorem planarProjection_apply {Z : Type*} (x : Cylinder Z) :
    planarProjection x = (x.1.1, x.2) := rfl

@[simp] theorem cylindricalLift_apply {Z : Type*} (v : ℝ × ℝ → ℝ)
    (x : Cylinder Z) : cylindricalLift v x = v (x.1.1, x.2) := rfl

/-- The active-plane projection is nonexpansive for the product norm. -/
theorem dist_planarProjection_le {Z : Type*} [SeminormedAddCommGroup Z]
    (x y : Cylinder Z) :
    dist (planarProjection x) (planarProjection y) ≤ dist x y := by
  rw [Prod.dist_eq, Prod.dist_eq]
  exact max_le_max (le_max_left _ _) le_rfl

/-- Equation (5.8): adjoining zero passive components does not change the
norm of the planar gradient.  Mathlib's product norm makes this a structural
identity, independent of the number or nature of the passive coordinates. -/
@[simp] theorem norm_cylindricalGradient {Z : Type*} [SeminormedAddCommGroup Z]
    (g : ℝ × ℝ → ℝ × ℝ) (x : Cylinder Z) :
    ‖cylindricalGradient g x‖ = ‖g (planarProjection x)‖ := by
  simp [cylindricalGradient, Prod.norm_def]

/-! The preceding product-coordinate theorem is convenient for later
interfaces.  The following specialization records the same claim with the
literal Euclidean `ℓ²` norm used in the paper. -/

/-- Euclidean `ℝ^m` in mathlib's canonical `ℓ²` model. -/
abbrev Euclidean (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- Inclusion of the two active coordinate indices into dimension `k+2`. -/
def euclideanActiveIndex (k : ℕ) (i : Fin 2) : Fin (k + 2) :=
  ⟨i.1, by omega⟩

/-- Projection of Euclidean `ℝ^(k+2)` onto its first two coordinates. -/
def euclideanPlanarProjection (k : ℕ) (x : Euclidean (k + 2)) : Euclidean 2 :=
  WithLp.toLp 2 (fun i => x (euclideanActiveIndex k i))

/-- Extend a two-dimensional Euclidean gradient by `k` zero components. -/
def euclideanCylindricalGradient (k : ℕ) (g : Euclidean 2 → Euclidean 2)
    (x : Euclidean (k + 2)) : Euclidean (k + 2) :=
  EuclideanSpace.single (euclideanActiveIndex k 0) (g (euclideanPlanarProjection k x) 0) +
    EuclideanSpace.single (euclideanActiveIndex k 1) (g (euclideanPlanarProjection k x) 1)

/-- Euclidean form of equation (5.8)/(0.72): zero passive components do not
change the `ℓ²` norm of the planar gradient. -/
theorem norm_euclideanCylindricalGradient (k : ℕ)
    (g : Euclidean 2 → Euclidean 2) (x : Euclidean (k + 2)) :
    ‖euclideanCylindricalGradient k g x‖ = ‖g (euclideanPlanarProjection k x)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hidx : euclideanActiveIndex k (0 : Fin 2) ≠
      euclideanActiveIndex k (1 : Fin 2) := by
    intro h
    have hval := congrArg Fin.val h
    change (0 : ℕ) = 1 at hval
    omega
  simp only [pow_two]
  have horth : inner ℝ
      (EuclideanSpace.single (euclideanActiveIndex k 0)
        (g (euclideanPlanarProjection k x) 0))
      (EuclideanSpace.single (euclideanActiveIndex k 1)
        (g (euclideanPlanarProjection k x) 1)) = 0 := by
    rw [EuclideanSpace.inner_single_left]
    simp [hidx]
  rw [euclideanCylindricalGradient,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth,
    PiLp.norm_single 2 (fun _ : Fin (k + 2) => ℝ),
    PiLp.norm_single 2 (fun _ : Fin (k + 2) => ℝ)]
  simp only [Real.norm_eq_abs, ← pow_two]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [sq_abs]

/-! ## The exponent and signed flat boundary factor -/

/-- The Hölder exponent `α = 1 - 2/p` appearing throughout Section 5.2. -/
def alpha (p : ℝ) : ℝ := 1 - 2 / p

theorem alpha_pos {p : ℝ} (hp : 2 < p) : 0 < alpha p := by
  unfold alpha
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  rw [sub_pos, div_lt_iff₀ hp0]
  nlinarith

theorem alpha_ne_zero {p : ℝ} (hp : 2 < p) : alpha p ≠ 0 :=
  (alpha_pos hp).ne'

/-- The function `𝓫_p` below equation (5.11). -/
def boundaryBump (p : ℝ) : ℝ → ℝ :=
  flatBump (alpha p)

@[simp] theorem boundaryBump_zero (p : ℝ) : boundaryBump p 0 = 0 := by
  simp [boundaryBump]

theorem boundaryBump_eq_of_pos {p t : ℝ} (ht : 0 < t) :
    boundaryBump p t = Real.exp (-(alpha p) * t⁻¹ ^ 2) := by
  exact flatBump.eq_of_pos ht

theorem boundaryBump_eq_of_neg {p t : ℝ} (ht : t < 0) :
    boundaryBump p t = -Real.exp (-(alpha p) * t⁻¹ ^ 2) := by
  exact flatBump.eq_of_neg ht

theorem boundaryBump_contDiff {p : ℝ} (hp : 2 < p) :
    ContDiff ℝ ∞ (boundaryBump p) := by
  exact flatBump.contDiff (alpha p) (alpha_pos hp)

theorem boundaryBump_vanishes_to_all_orders {p : ℝ} (hp : 2 < p) (m : ℕ) :
    iteratedDeriv m (boundaryBump p) 0 = 0 := by
  exact flatBump.iteratedDeriv_zero (alpha p) (alpha_pos hp) m

/-- Signed real power used in equation (5.9). -/
def signedRpow (a y : ℝ) : ℝ :=
  Real.sign y * |y| ^ a

@[simp] theorem signedRpow_zero (a : ℝ) : signedRpow a 0 = 0 := by
  simp [signedRpow]

/-! ## The upper boundary graph: equation (5.10) -/

/-- First identity in equation (5.10).  The only needed hypothesis says that
the radicand in `paperYPlus` is nonnegative. -/
theorem paperYPlus_mul_add_r {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (x : E)
    (hrad : Real.exp 1 * paperBump (s r x) ≤ 1) :
    paperYPlus r x * (paperYPlus r x + r) =
      -(Real.exp 1 * paperBump (s r x)) * (r / 2) ^ 2 := by
  have hamp_sq : (amp paperBump r x) ^ 2 =
      1 - Real.exp 1 * paperBump (s r x) := by
    rw [amp, Real.sq_sqrt (sub_nonneg.mpr hrad)]
  change (r / 2 * (amp paperBump r x - 1)) *
      (r / 2 * (amp paperBump r x - 1) + r) =
        -(Real.exp 1 * paperBump (s r x)) * (r / 2) ^ 2
  nlinarith

/-- Second identity in equation (5.10). -/
theorem paperYPlus_add_r_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (x : E) : 0 < paperYPlus r x + r := by
  have hamp_nonneg : 0 ≤ amp paperBump r x := Real.sqrt_nonneg _
  change 0 < r / 2 * (amp paperBump r x - 1) + r
  nlinarith

/-- The form of the first identity in (5.10) valid on the range
`s r x ≤ 1`. -/
theorem paperYPlus_mul_add_r_of_s_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (x : E) (hs : s r x ≤ 1) :
    paperYPlus r x * (paperYPlus r x + r) =
      -(Real.exp 1 * paperBump (s r x)) * (r / 2) ^ 2 := by
  apply paperYPlus_mul_add_r x
  have hb : paperBump (s r x) ≤ paperBump 1 :=
    paperBump_strictMono.monotone hs
  have hmul := mul_le_mul_of_nonneg_left hb (Real.exp_pos 1).le
  rw [exp_mul_paperBump_one] at hmul
  exact hmul

/-! ## Explicit interfaces for the analytic input -/

/-- A direct distribution-function formulation of weak `L^q` membership on
a set.  The constant is `ℝ≥0∞`, so an infinite-measure tail cannot be hidden
by `ENNReal.toReal`. -/
def WeakTailBoundOn {X Y : Type*} [MeasurableSpace X] [NormedAddCommGroup Y]
    (μ : Measure X) (Ω : Set X) (q : ℝ) (C : ℝ≥0∞) (f : X → Y) : Prop :=
  ∀ t : ℝ, 0 < t →
    ENNReal.ofReal (t ^ q) * μ (Ω ∩ {x | t < ‖f x‖}) ≤ C

/-- A concrete Hölder estimate, phrased with a real exponent so that the
paper's exact value `1 - 2 / p` appears without a coercion wrapper. -/
def HolderBoundOn {X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    (Ω : Set X) (a C : ℝ) (f : X → Y) : Prop :=
  0 ≤ a ∧ 0 ≤ C ∧ ∀ ⦃x⦄, x ∈ Ω → ∀ ⦃y⦄, y ∈ Ω →
    dist (f x) (f y) ≤ C * Real.rpow (dist x y) a

theorem HolderBoundOn.mono {X Y : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] {s t : Set X} {a C : ℝ} {f : X → Y}
    (h : HolderBoundOn t a C f) (hst : s ⊆ t) : HolderBoundOn s a C f := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x hx y hy
  exact h.2.2 (hst hx) (hst hy)

/-- Hölder estimates survive cylindrical extension with exactly the same
exponent and constant. -/
theorem holderBoundOn_cylindricalLift
    {Z : Type*} [NormedAddCommGroup Z]
    {s : Set (Cylinder Z)} {a C : ℝ} {v : ℝ × ℝ → ℝ}
    (h : HolderBoundOn (planarProjection '' s) a C v) :
    HolderBoundOn s a C (cylindricalLift v) := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x hx y hy
  have hv := h.2.2 (mem_image_of_mem planarProjection hx)
    (mem_image_of_mem planarProjection hy)
  rw [cylindricalLift, cylindricalLift]
  refine hv.trans ?_
  apply mul_le_mul_of_nonneg_left _ h.2.1
  exact Real.rpow_le_rpow (dist_nonneg) (dist_planarProjection_le x y) h.1

/-- The geometric/Fubini input used in (5.13)--(5.14): every cylindrical
gradient tail in `Ω` is bounded by a fixed fiber factor times its planar
tail.  Keeping it explicit isolates the only measure-theoretic step needed
to transport the planar Marcinkiewicz estimate. -/
def CylindricalTailComparison {Z : Type*} [MeasurableSpace (Cylinder Z)]
    [NormedAddCommGroup Z] (μ : Measure (Cylinder Z)) (Ω : Set (Cylinder Z))
    (M : ℝ≥0∞) (g : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∀ t : ℝ, 0 < t →
    μ (Ω ∩ {x | t < ‖cylindricalGradient g x‖}) ≤
      M * volume {z | t < ‖g z‖}

theorem weakTailBoundOn_cylindricalGradient
    {Z : Type*} [MeasurableSpace (Cylinder Z)] [NormedAddCommGroup Z]
    {μ : Measure (Cylinder Z)} {Ω : Set (Cylinder Z)} {q : ℝ} {C M : ℝ≥0∞}
    {g : ℝ × ℝ → ℝ × ℝ}
    (hplanar : WeakTailBoundOn volume Set.univ q C g)
    (hcompare : CylindricalTailComparison μ Ω M g) :
    WeakTailBoundOn μ Ω q (M * C) (cylindricalGradient g) := by
  intro t ht
  calc
    ENNReal.ofReal (t ^ q) * μ (Ω ∩ {x | t < ‖cylindricalGradient g x‖}) ≤
        ENNReal.ofReal (t ^ q) * (M * volume {z | t < ‖g z‖}) :=
      mul_le_mul le_rfl (hcompare t ht) bot_le bot_le
    _ = M * (ENNReal.ofReal (t ^ q) * volume {z | t < ‖g z‖}) := by
      ac_rfl
    _ ≤ M * C := by
      apply mul_le_mul le_rfl _ bot_le bot_le
      simpa only [Set.univ_inter] using hplanar t ht

/-- The precise conclusion meant by saying that the boundary restriction of
`v` has a smooth ambient extension. -/
def HasSmoothTraceExtension {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (boundary : Set X) (v : X → ℝ) : Prop :=
  ∃ v₀ : X → ℝ, ContDiff ℝ ∞ v₀ ∧ Set.EqOn v₀ v boundary

/-- Data imported from the two-dimensional construction of Sections 3--4.
The field `representation_5_9` is exactly equation (5.9). -/
structure PlanarInput (p : ℝ) where
  value : ℝ × ℝ → ℝ
  kernel : ℝ × ℝ → ℝ
  gradient : ℝ × ℝ → ℝ × ℝ
  representation_5_9 :
    ∀ z, value z = signedRpow (alpha p) z.2 * kernel z
  kernel_contDiff : ContDiff ℝ ∞ kernel
  holderConstant : ℝ
  value_holder : HolderBoundOn Set.univ (alpha p) holderConstant value
  weakTailConstant : ℝ≥0∞
  gradient_weakTail :
    WeakTailBoundOn volume Set.univ (p / 2) weakTailConstant gradient

namespace PlanarInput

def liftedValue {p : ℝ} (D : PlanarInput p) {Z : Type*} : Cylinder Z → ℝ :=
  cylindricalLift D.value

def liftedGradient {p : ℝ} (D : PlanarInput p) {Z : Type*} [Zero Z] :
    Cylinder Z → Cylinder Z :=
  cylindricalGradient D.gradient

@[simp] theorem norm_liftedGradient {p : ℝ} (D : PlanarInput p)
    {Z : Type*} [SeminormedAddCommGroup Z] (x : Cylinder Z) :
    ‖D.liftedGradient x‖ = ‖D.gradient (planarProjection x)‖ :=
  norm_cylindricalGradient D.gradient x

theorem liftedValue_holder {p : ℝ} (D : PlanarInput p)
    {Z : Type*} [NormedAddCommGroup Z] (s : Set (Cylinder Z)) :
    HolderBoundOn s (alpha p) D.holderConstant D.liftedValue := by
  apply holderBoundOn_cylindricalLift
  exact D.value_holder.mono (by simp)

theorem liftedGradient_weakTail
    {p : ℝ} (D : PlanarInput p)
    {Z : Type*} [MeasurableSpace (Cylinder Z)] [NormedAddCommGroup Z]
    {μ : Measure (Cylinder Z)} {Ω : Set (Cylinder Z)} {M : ℝ≥0∞}
    (hcompare : CylindricalTailComparison μ Ω M D.gradient) :
    WeakTailBoundOn μ Ω (p / 2) (M * D.weakTailConstant) D.liftedGradient :=
  weakTailBoundOn_cylindricalGradient D.gradient_weakTail hcompare

end PlanarInput

/-- Interface to the zero-trace statement in (5.15).  A future Sobolev trace
development can instantiate `ZeroTrace`; the present file only records the
mathematical data actually consumed later. -/
structure TraceInterface {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (Ω : Set X) (v : X → ℝ) where
  ZeroTrace : (X → ℝ) → Prop
  extension : X → ℝ
  extension_smooth : ContDiff ℝ ∞ extension
  agrees_on_boundary : Set.EqOn extension v (frontier Ω)
  difference_has_zero_trace : ZeroTrace (fun x ↦ v x - extension x)

theorem TraceInterface.hasSmoothTraceExtension
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Ω : Set X} {v : X → ℝ} (T : TraceInterface Ω v) :
    HasSmoothTraceExtension (frontier Ω) v :=
  ⟨T.extension, T.extension_smooth, T.agrees_on_boundary⟩

/-! ## Equations (5.11) and (5.12) -/

/-- The coefficient on the right-hand sides of (5.11)--(5.12). -/
def boundaryCoefficient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p r : ℝ) (x : E) : ℝ :=
  -Real.rpow (Real.exp 1 * r ^ 2 / 4) (alpha p) *
      boundaryBump p (s r x) /
        Real.rpow (paperYPlus r x + r) (alpha p)

/-- Equation (5.11), isolated as the exact algebraic interface used by the
boundary-trace computation. -/
def HasBoundaryPowerIdentity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p r : ℝ) (x : E) : Prop :=
  signedRpow (alpha p) (paperYPlus r x) = boundaryCoefficient p r x

private theorem sign_paperYPlus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (x : E) (hs : s r x < 1) :
    Real.sign (paperYPlus r x) = -Real.sign (s r x) := by
  have hprod := paperYPlus_mul_add_r_of_s_le_one x hs.le
  have hadd : 0 < paperYPlus r x + r := paperYPlus_add_r_pos hr x
  have hrsq : 0 < (r / 2) ^ 2 := sq_pos_of_pos (div_pos hr (by norm_num))
  rcases lt_trichotomy (s r x) 0 with ht | ht | ht
  · have hb : paperBump (s r x) < 0 := (flatBump.neg_iff zero_lt_one).2 ht
    have hrhs : 0 < -(Real.exp 1 * paperBump (s r x)) * (r / 2) ^ 2 := by
      exact mul_pos (neg_pos.mpr (mul_neg_of_pos_of_neg (Real.exp_pos 1) hb)) hrsq
    have hmul : 0 < paperYPlus r x * (paperYPlus r x + r) := hprod.symm ▸ hrhs
    have hy : 0 < paperYPlus r x := by
      rcases (mul_pos_iff.mp hmul) with h | h
      · exact h.1
      · exact (not_lt_of_ge hadd.le h.2).elim
    rw [Real.sign_of_pos hy, Real.sign_of_neg ht]
    norm_num
  · have hmul : paperYPlus r x * (paperYPlus r x + r) = 0 := by
      simpa [ht] using hprod
    have hy : paperYPlus r x = 0 := (mul_eq_zero.mp hmul).resolve_right hadd.ne'
    rw [hy, ht, Real.sign_zero, neg_zero]
  · have hb : 0 < paperBump (s r x) := (flatBump.pos_iff zero_lt_one).2 ht
    have hrhs : -(Real.exp 1 * paperBump (s r x)) * (r / 2) ^ 2 < 0 := by
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (Real.exp_pos 1) hb)) hrsq
    have hmul : paperYPlus r x * (paperYPlus r x + r) < 0 := hprod.symm ▸ hrhs
    have hy : paperYPlus r x < 0 := by
      rcases (mul_neg_iff.mp hmul) with h | h
      · exact (not_lt_of_ge hadd.le h.2).elim
      · exact h.1
    rw [Real.sign_of_neg hy, Real.sign_of_pos ht]

private theorem abs_paperYPlus_mul_add_r
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (hr : 0 < r) (x : E) (hs : s r x < 1) (hs0 : s r x ≠ 0) :
    |paperYPlus r x| * (paperYPlus r x + r) =
      (Real.exp 1 * r ^ 2 / 4) * Real.exp (-(s r x)⁻¹ ^ 2) := by
  have hprod := paperYPlus_mul_add_r_of_s_le_one x hs.le
  have hadd : 0 < paperYPlus r x + r := paperYPlus_add_r_pos hr x
  have habs := congrArg abs hprod
  rw [abs_mul, abs_of_pos hadd, abs_mul, abs_neg, abs_mul,
    abs_of_pos (Real.exp_pos 1), flatBump.abs_of_ne (a := 1) hs0,
    abs_pow, abs_of_pos (div_pos hr (by norm_num))] at habs
  norm_num at habs
  convert habs using 1 <;> ring_nf

private theorem abs_rpow_paperYPlus
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p r : ℝ} (hr : 0 < r) (x : E) (hs : s r x < 1) (hs0 : s r x ≠ 0) :
    |paperYPlus r x| ^ alpha p =
      (Real.exp 1 * r ^ 2 / 4) ^ alpha p *
        Real.exp (-alpha p * (s r x)⁻¹ ^ 2) /
          (paperYPlus r x + r) ^ alpha p := by
  have hbase := abs_paperYPlus_mul_add_r hr x hs hs0
  have hconst : 0 < Real.exp 1 * r ^ 2 / 4 := by positivity
  have hadd : 0 < paperYPlus r x + r := paperYPlus_add_r_pos hr x
  have hrpow := congrArg (fun u : ℝ => u ^ alpha p) hbase
  rw [Real.mul_rpow (abs_nonneg _) hadd.le,
    Real.mul_rpow hconst.le (Real.exp_pos _).le] at hrpow
  have hexp : Real.exp (-(s r x)⁻¹ ^ 2) ^ alpha p =
      Real.exp (-alpha p * (s r x)⁻¹ ^ 2) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hexp] at hrpow
  apply (eq_div_iff (Real.rpow_pos_of_pos hadd (alpha p)).ne').2
  exact hrpow

private theorem paperYPlus_eq_zero_of_s_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r : ℝ} (x : E) (hs : s r x = 0) : paperYPlus r x = 0 := by
  rw [paperYPlus, yPlus, amp, hs, paperBump_zero]
  norm_num

/-- Equation (5.11) for the upper graph of the domain constructed in
Section 5.1.  The proof includes the contact set `s r x = 0`; no
nondegeneracy assumption is hidden in the statement. -/
theorem paper_hasBoundaryPowerIdentity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p r : ℝ} (_hp : 2 < p) (hr : 0 < r) (x : E) (hs : s r x < 1) :
    HasBoundaryPowerIdentity p r x := by
  by_cases hs0 : s r x = 0
  · have hy := paperYPlus_eq_zero_of_s_eq_zero x hs0
    simp [HasBoundaryPowerIdentity, signedRpow, boundaryCoefficient,
      boundaryBump, hy, hs0]
  · rw [HasBoundaryPowerIdentity, signedRpow, boundaryCoefficient,
      sign_paperYPlus hr x hs, Real.rpow_eq_pow, Real.rpow_eq_pow,
      abs_rpow_paperYPlus hr x hs hs0]
    unfold boundaryBump flatBump
    ring

/-- Equation (5.12) follows mechanically from equations (5.9) and (5.11).
Keeping this lemma independent of how (5.11) is established makes the logical
boundary of the paper's argument explicit. -/
theorem equation_5_12
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p r : ℝ} {coord : E → ℝ} {v K : ℝ × ℝ → ℝ}
    (h59 : ∀ z, v z = signedRpow (alpha p) z.2 * K z)
    (x : E) (h511 : HasBoundaryPowerIdentity p r x) :
    v (coord x, paperYPlus r x) =
      boundaryCoefficient p r x * K (coord x, paperYPlus r x) := by
  rw [h59]
  exact congrArg (fun c ↦ c * K (coord x, paperYPlus r x)) h511

/-- Equations (5.9), (5.11), and (5.12) composed with all of the paper's
numerical hypotheses exposed. -/
theorem paper_equation_5_12
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p r : ℝ} {coord : E → ℝ} {v K : ℝ × ℝ → ℝ}
    (hp : 2 < p) (hr : 0 < r)
    (h59 : ∀ z, v z = signedRpow (alpha p) z.2 * K z)
    (x : E) (hs : s r x < 1) :
    v (coord x, paperYPlus r x) =
      boundaryCoefficient p r x * K (coord x, paperYPlus r x) :=
  equation_5_12 h59 x (paper_hasBoundaryPowerIdentity hp hr x hs)

/-- Equation (5.12) specialized to the cylindrical lift of the supplied
planar input. -/
theorem PlanarInput.lifted_boundary_formula
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p r : ℝ} (D : PlanarInput p) (x : ℝ × Z)
    (h511 : HasBoundaryPowerIdentity p r x) :
    D.liftedValue (x, paperYPlus r x) =
      boundaryCoefficient p r x * D.kernel (x.1, paperYPlus r x) := by
  exact equation_5_12 D.representation_5_9 x h511

theorem PlanarInput.lifted_boundary_formula_of_s_lt_one
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {p r : ℝ} (D : PlanarInput p) (hp : 2 < p) (hr : 0 < r)
    (x : ℝ × Z) (hs : s r x < 1) :
    D.liftedValue (x, paperYPlus r x) =
      boundaryCoefficient p r x * D.kernel (x.1, paperYPlus r x) :=
  paper_equation_5_12 hp hr D.representation_5_9 x hs

end SmoothBoundaryTraces

end DomainTraces
