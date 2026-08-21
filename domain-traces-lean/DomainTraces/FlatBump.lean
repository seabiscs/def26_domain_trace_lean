import Mathlib

/-!
# The flat signed exponential used in Sections 5.1 and 5.2

For a parameter `a`, `flatBump a` is the function

`t ↦ sign(t) * exp (-a * t⁻²)`.

Lean's inverse and `Real.sign` are both zero at zero, so this formula already
includes the prescribed value `flatBump a 0 = 0`.
-/

noncomputable section

open scoped Topology

open Filter Set Real ContDiff

namespace DomainTraces

/-- The signed flat exponential `sign(t) exp (-a t⁻²)`, with value zero at zero. -/
def flatBump (a t : ℝ) : ℝ :=
  Real.sign t * Real.exp (-a * t⁻¹ ^ 2)

namespace flatBump

variable {a t : ℝ}

@[simp] theorem zero (a : ℝ) : flatBump a 0 = 0 := by
  simp [flatBump]

@[simp] theorem one (a : ℝ) : flatBump a 1 = Real.exp (-a) := by
  simp [flatBump]

@[simp] theorem neg (a t : ℝ) : flatBump a (-t) = -flatBump a t := by
  simp [flatBump, Real.sign_neg]

theorem odd (a : ℝ) : Function.Odd (flatBump a) := fun t ↦ neg a t

theorem eq_of_pos (ht : 0 < t) : flatBump a t = Real.exp (-a * t⁻¹ ^ 2) := by
  simp [flatBump, Real.sign_of_pos ht]

theorem eq_of_neg (ht : t < 0) : flatBump a t = -Real.exp (-a * t⁻¹ ^ 2) := by
  simp [flatBump, Real.sign_of_neg ht]

theorem sign_flatBump (_ha : 0 < a) (t : ℝ) : Real.sign (flatBump a t) = Real.sign t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [eq_of_neg ht, Real.sign_of_neg (neg_neg_of_pos (Real.exp_pos _)),
      Real.sign_of_neg ht]
  · simp
  · rw [eq_of_pos ht, Real.sign_of_pos (Real.exp_pos _), Real.sign_of_pos ht]

@[simp] theorem eq_zero_iff (ha : 0 < a) : flatBump a t = 0 ↔ t = 0 := by
  rw [← Real.sign_eq_zero_iff, sign_flatBump ha, Real.sign_eq_zero_iff]

@[simp] theorem pos_iff (_ha : 0 < a) : 0 < flatBump a t ↔ 0 < t := by
  constructor
  · intro h
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · rw [eq_of_neg ht] at h
      linarith [Real.exp_pos (-a * t⁻¹ ^ 2)]
    · simp at h
    · exact ht
  · intro ht
    rw [eq_of_pos ht]
    exact Real.exp_pos _

@[simp] theorem neg_iff (_ha : 0 < a) : flatBump a t < 0 ↔ t < 0 := by
  constructor
  · intro h
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact ht
    · simp at h
    · rw [eq_of_pos ht] at h
      exact (not_lt_of_ge (Real.exp_pos _).le h).elim
  · intro ht
    rw [eq_of_neg ht]
    exact neg_neg_of_pos (Real.exp_pos _)

theorem nonneg_iff (ha : 0 < a) : 0 ≤ flatBump a t ↔ 0 ≤ t := by
  rw [← not_lt, ← not_lt, neg_iff ha]

theorem nonpos_iff (ha : 0 < a) : flatBump a t ≤ 0 ↔ t ≤ 0 := by
  rw [← not_lt, ← not_lt, pos_iff ha]

theorem abs (a t : ℝ) : |flatBump a t| = |Real.sign t| * Real.exp (-a * t⁻¹ ^ 2) := by
  simp [flatBump, abs_mul, abs_of_pos (Real.exp_pos _)]

theorem abs_of_ne (ht : t ≠ 0) : |flatBump a t| = Real.exp (-a * t⁻¹ ^ 2) := by
  rw [abs]
  rcases lt_or_gt_of_ne ht with ht | ht
  · simp [Real.sign_of_neg ht]
  · simp [Real.sign_of_pos ht]

theorem neg_one_lt (ha : 0 < a) (t : ℝ) : -1 < flatBump a t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [eq_of_neg ht, neg_lt_neg_iff, Real.exp_lt_one_iff]
    have hs : 0 < t⁻¹ ^ 2 := sq_pos_iff.mpr (inv_ne_zero ht.ne)
    nlinarith [mul_pos ha hs]
  · norm_num
  · rw [eq_of_pos ht]
    exact lt_trans (by norm_num) (Real.exp_pos _)

theorem lt_one (ha : 0 < a) (t : ℝ) : flatBump a t < 1 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [eq_of_neg ht]
    exact lt_trans (neg_neg_of_pos (Real.exp_pos _)) zero_lt_one
  · norm_num
  · rw [eq_of_pos ht, Real.exp_lt_one_iff]
    have hs : 0 < t⁻¹ ^ 2 := sq_pos_iff.mpr (inv_ne_zero ht.ne')
    nlinarith [mul_pos ha hs]

theorem mem_Ioo (ha : 0 < a) (t : ℝ) : flatBump a t ∈ Set.Ioo (-1) 1 :=
  ⟨neg_one_lt ha t, lt_one ha t⟩

theorem range_subset_Ioo (ha : 0 < a) : Set.range (flatBump a) ⊆ Set.Ioo (-1) 1 := by
  rintro _ ⟨t, rfl⟩
  exact mem_Ioo ha t

theorem strictMonoOn_Ioi (ha : 0 < a) : StrictMonoOn (flatBump a) (Set.Ioi 0) := by
  intro x hx y hy hxy
  rw [eq_of_pos hx, eq_of_pos hy, Real.exp_lt_exp]
  have hx2 : 0 < x ^ 2 := sq_pos_iff.mpr hx.ne'
  have hy2 : 0 < y ^ 2 := sq_pos_iff.mpr hy.ne'
  have hxy2 : x ^ 2 < y ^ 2 := (sq_lt_sq₀ hx.le hy.le).mpr hxy
  have hinv : (y ^ 2)⁻¹ < (x ^ 2)⁻¹ := (inv_lt_inv₀ hy2 hx2).mpr hxy2
  simpa only [inv_pow] using
    (mul_lt_mul_of_neg_left hinv (neg_lt_zero.mpr ha) :
      -a * (x ^ 2)⁻¹ < -a * (y ^ 2)⁻¹)

theorem strictMonoOn_Iio (ha : 0 < a) : StrictMonoOn (flatBump a) (Set.Iio 0) := by
  intro x hx y hy hxy
  rw [eq_of_neg hx, eq_of_neg hy, neg_lt_neg_iff, Real.exp_lt_exp]
  have hx2 : 0 < x ^ 2 := sq_pos_iff.mpr hx.ne
  have hy2 : 0 < y ^ 2 := sq_pos_iff.mpr hy.ne
  have hyx2 : y ^ 2 < x ^ 2 := sq_lt_sq.mpr <| by
    rw [abs_of_neg hy, abs_of_neg hx]
    exact neg_lt_neg hxy
  have hinv : (x ^ 2)⁻¹ < (y ^ 2)⁻¹ := (inv_lt_inv₀ hx2 hy2).mpr hyx2
  simpa only [inv_pow] using
    (mul_lt_mul_of_neg_left hinv (neg_lt_zero.mpr ha) :
      -a * (y ^ 2)⁻¹ < -a * (x ^ 2)⁻¹)

/-- For a positive parameter, the signed flat exponential is strictly increasing on `ℝ`. -/
theorem strictMono (ha : 0 < a) : StrictMono (flatBump a) := by
  intro x y hxy
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_or_ge y 0 with hy | hy
    · exact strictMonoOn_Iio ha hx hy hxy
    · exact (neg_iff ha).mpr hx |>.trans_le ((nonneg_iff ha).mpr hy)
  · have hy : 0 < y := hxy
    simpa using (pos_iff ha).mpr hy
  · have hy : 0 < y := hx.trans hxy
    exact strictMonoOn_Ioi ha hx hy hxy

theorem lt_iff_lt (ha : 0 < a) {s t : ℝ} : flatBump a s < flatBump a t ↔ s < t :=
  (strictMono ha).lt_iff_lt

theorem le_iff_le (ha : 0 < a) {s t : ℝ} : flatBump a s ≤ flatBump a t ↔ s ≤ t :=
  (strictMono ha).le_iff_le

theorem injective (ha : 0 < a) : Function.Injective (flatBump a) :=
  (strictMono ha).injective

theorem eq_one_iff (ha : 0 < a) : flatBump a t = flatBump a 1 ↔ t = 1 := by
  constructor
  · exact fun h ↦ (injective ha h)
  · exact fun h ↦ congrArg (flatBump a) h

theorem hasDerivAt_of_pos (ht : 0 < t) :
    HasDerivAt (flatBump a) (2 * a * t⁻¹ ^ 3 * Real.exp (-a * t⁻¹ ^ 2)) t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hinner : HasDerivAt (fun x : ℝ ↦ -a * x⁻¹ ^ 2) (2 * a * t⁻¹ ^ 3) t := by
    have hraw : HasDerivAt (fun x : ℝ ↦ -a * x⁻¹ ^ 2)
        (-a * (2 * t⁻¹ ^ (2 - 1) * -(t ^ 2)⁻¹)) t := by
      simpa only [Pi.pow_apply, Nat.cast_ofNat] using
        ((hasDerivAt_inv ht0).pow 2).const_mul (-a)
    refine hraw.congr_deriv ?_
    rw [← inv_pow]
    norm_num
    ring
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-a * x⁻¹ ^ 2))
      (2 * a * t⁻¹ ^ 3 * Real.exp (-a * t⁻¹ ^ 2)) t := by
    convert hinner.exp using 1
    ring
  refine hexp.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds ht] with x hx
  exact eq_of_pos hx

theorem hasDerivAt_of_neg (ht : t < 0) :
    HasDerivAt (flatBump a) (-2 * a * t⁻¹ ^ 3 * Real.exp (-a * t⁻¹ ^ 2)) t := by
  have ht0 : t ≠ 0 := ht.ne
  have hinner : HasDerivAt (fun x : ℝ ↦ -a * x⁻¹ ^ 2) (2 * a * t⁻¹ ^ 3) t := by
    have hraw : HasDerivAt (fun x : ℝ ↦ -a * x⁻¹ ^ 2)
        (-a * (2 * t⁻¹ ^ (2 - 1) * -(t ^ 2)⁻¹)) t := by
      simpa only [Pi.pow_apply, Nat.cast_ofNat] using
        ((hasDerivAt_inv ht0).pow 2).const_mul (-a)
    refine hraw.congr_deriv ?_
    rw [← inv_pow]
    norm_num
    ring
  have hexp : HasDerivAt (fun x : ℝ ↦ Real.exp (-a * x⁻¹ ^ 2))
      (2 * a * t⁻¹ ^ 3 * Real.exp (-a * t⁻¹ ^ 2)) t := by
    convert hinner.exp using 1
    ring
  have hneg := hexp.neg.congr_of_eventuallyEq (by
    filter_upwards [gt_mem_nhds ht] with x hx
    exact eq_of_neg hx)
  refine hneg.congr_deriv ?_
  ring

theorem norm_of_ne (a : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ‖flatBump a t‖ = Real.exp (-a * ‖t⁻¹‖ ^ 2) := by
  rw [flatBump, norm_mul, Real.norm_eq_abs]
  rcases Real.sign_apply_eq_of_ne_zero t ht with h | h <;> rw [h] <;> simp

/-- Every inverse-power multiple still vanishes at the origin.  This is the
flatness estimate used in the smoothness proof. -/
theorem tendsto_inv_pow_mul_zero (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Tendsto (fun t : ℝ ↦ t⁻¹ ^ n * flatBump a t) (𝓝 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsq : Tendsto (fun t : ℝ ↦ ‖t⁻¹‖ ^ 2) (𝓝[≠] 0) atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      tendsto_norm_inv_nhdsNE_zero_atTop
  have hlim : Tendsto
      (fun t : ℝ ↦ (‖t⁻¹‖ ^ 2) ^ ((n : ℝ) / 2) * Real.exp (-a * (‖t⁻¹‖ ^ 2)))
      (𝓝[≠] 0) (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((n : ℝ) / 2) a ha).comp hsq
  have hlim' : Tendsto (fun t : ℝ ↦ ‖t⁻¹ ^ n * flatBump a t‖) (𝓝[≠] 0) (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rw [norm_mul, norm_pow, norm_of_ne a ht0]
    congr 1
    rw [Real.rpow_div_two_eq_sqrt _ (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _), Real.rpow_natCast]
  have hpure : Tendsto (fun t : ℝ ↦ ‖t⁻¹ ^ n * flatBump a t‖) (pure 0) (𝓝 0) := by
    simpa using (tendsto_pure_nhds (fun t : ℝ ↦ ‖t⁻¹ ^ n * flatBump a t‖) 0)
  simpa only [nhdsNE_sup_pure] using hlim'.sup hpure

/-- Derivative formula valid also at the flat point `x = 0`. -/
theorem hasDerivAt (a : ℝ) (ha : 0 < a) (x : ℝ) :
    HasDerivAt (flatBump a) (2 * a * x⁻¹ ^ 3 * flatBump a x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := hasDerivAt_of_neg (a := a) hx
    refine h.congr_deriv ?_
    rw [eq_of_neg hx]
    ring
  · simp only [inv_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0), mul_zero, zero]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_inv_pow_mul_zero a ha 1).mono_left inf_le_left).congr ?_
    intro t
    simp [slope_def_field, div_eq_mul_inv, mul_comm]
  · have h := hasDerivAt_of_pos (a := a) hx
    refine h.congr_deriv ?_
    rw [eq_of_pos hx]

@[simp] theorem deriv_apply (a : ℝ) (ha : 0 < a) (x : ℝ) :
    deriv (flatBump a) x = 2 * a * x⁻¹ ^ 3 * flatBump a x :=
  (hasDerivAt a ha x).deriv

theorem hasDerivAt_inv_pow_mul (a : ℝ) (ha : 0 < a) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ t⁻¹ ^ n * flatBump a t)
      (-(n : ℝ) * (x⁻¹ ^ (n + 1) * flatBump a x) +
        (2 * a) * (x⁻¹ ^ (n + 3) * flatBump a x)) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [inv_zero, mul_zero, zero, add_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((tendsto_inv_pow_mul_zero a ha (n + 1)).mono_left inf_le_left).congr ?_
    intro t
    simp only [slope_def_field, sub_zero, inv_pow, zero, mul_zero]
    ring
  · have h := ((hasDerivAt_inv hx).pow n).mul (hasDerivAt a ha x)
    change HasDerivAt (fun t : ℝ ↦ t⁻¹ ^ n * flatBump a t) _ x at h
    convert h using 1
    simp only [Pi.pow_apply]
    rcases n with _ | n
    · simp
      ring
    · simp only [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, pow_succ]
      field_simp [hx]

theorem differentiable_inv_pow_mul (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Differentiable ℝ (fun t : ℝ ↦ t⁻¹ ^ n * flatBump a t) := fun x ↦
  (hasDerivAt_inv_pow_mul a ha n x).differentiableAt

theorem deriv_inv_pow_mul (a : ℝ) (ha : 0 < a) (n : ℕ) :
    deriv (fun t : ℝ ↦ t⁻¹ ^ n * flatBump a t) = fun x ↦
      -(n : ℝ) * (x⁻¹ ^ (n + 1) * flatBump a x) +
        (2 * a) * (x⁻¹ ^ (n + 3) * flatBump a x) := by
  funext x
  exact (hasDerivAt_inv_pow_mul a ha n x).deriv

theorem contDiff_inv_pow_mul {m : ℕ∞} (a : ℝ) (ha : 0 < a) (n : ℕ) :
    ContDiff ℝ m (fun t : ℝ ↦ t⁻¹ ^ n * flatBump a t) := by
  apply contDiff_all_iff_nat.2 (fun k ↦ ?_) m
  induction k generalizing n with
  | zero => exact contDiff_zero.2 (differentiable_inv_pow_mul a ha n).continuous
  | succ k ih =>
      rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = k + 1 from rfl]
      refine contDiff_succ_iff_deriv.2
        ⟨differentiable_inv_pow_mul a ha n, by simp, ?_⟩
      rw [deriv_inv_pow_mul a ha n]
      exact (contDiff_const.mul (ih (n + 1))).add (contDiff_const.mul (ih (n + 3)))

/-- `flatBump a` is `C∞` whenever `a > 0`. -/
@[fun_prop] theorem contDiff (a : ℝ) (ha : 0 < a) : ContDiff ℝ ∞ (flatBump a) := by
  simpa using contDiff_inv_pow_mul (m := (⊤ : ℕ∞)) a ha 0

/-- Every derivative of every inverse-power multiple vanishes at the origin. -/
theorem iteratedDeriv_inv_pow_mul_zero (a : ℝ) (ha : 0 < a) (k n : ℕ) :
    iteratedDeriv k (fun t : ℝ ↦ t⁻¹ ^ n * flatBump a t) 0 = 0 := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
      rw [iteratedDeriv_succ', deriv_inv_pow_mul a ha n]
      have hleft : ContDiffAt ℝ k
          (fun x ↦ -(n : ℝ) * (x⁻¹ ^ (n + 1) * flatBump a x)) 0 :=
        (contDiff_const.mul (contDiff_inv_pow_mul (m := (k : ℕ∞)) a ha (n + 1))).contDiffAt
      have hright : ContDiffAt ℝ k
          (fun x ↦ (2 * a) * (x⁻¹ ^ (n + 3) * flatBump a x)) 0 :=
        (contDiff_const.mul (contDiff_inv_pow_mul (m := (k : ℕ∞)) a ha (n + 3))).contDiffAt
      rw [iteratedDeriv_fun_add hleft hright]
      simp only [iteratedDeriv_const_mul_field, ih, mul_zero, add_zero]

/-- `flatBump a` vanishes to every order at the origin. -/
@[simp] theorem iteratedDeriv_zero (a : ℝ) (ha : 0 < a) (k : ℕ) :
    iteratedDeriv k (flatBump a) 0 = 0 := by
  simpa using iteratedDeriv_inv_pow_mul_zero a ha k 0

theorem hasDerivAt_one (a : ℝ) :
    HasDerivAt (flatBump a) (2 * a * Real.exp (-a)) 1 := by
  convert hasDerivAt_of_pos (a := a) zero_lt_one using 1
  norm_num

theorem deriv_one (a : ℝ) : deriv (flatBump a) 1 = 2 * a * Real.exp (-a) :=
  (hasDerivAt_one a).deriv

@[simp] theorem one_one : flatBump 1 1 = Real.exp (-1) := by
  simp

theorem one_one_eq_inv_exp : flatBump 1 1 = (Real.exp 1)⁻¹ := by
  rw [one_one, Real.exp_neg]

theorem one_one_eq_one_div_exp : flatBump 1 1 = 1 / Real.exp 1 := by
  simpa only [one_div] using one_one_eq_inv_exp

@[simp] theorem deriv_one_one : deriv (flatBump 1) 1 = 2 * Real.exp (-1) := by
  rw [deriv_one]
  norm_num

theorem deriv_one_one_eq_two_div_exp : deriv (flatBump 1) 1 = 2 / Real.exp 1 := by
  rw [deriv_one_one, Real.exp_neg, div_eq_mul_inv]

end flatBump

end DomainTraces
