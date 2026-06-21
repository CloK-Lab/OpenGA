import OpenGALib.Riemannian.Curvature.RiemannSymmetries

/-! # Killing vector fields -/

open Bundle VectorField
open scoped ContDiff Manifold Riemannian InnerProductSpace

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianSetup I M]

/-! ## Killing vector fields -/

/-- **Math.** A smooth vector field `X` is a **Killing vector field**
(for the metric) if the symmetric part of $\nabla X$ vanishes:
$g(\nabla_U X, W) + g(\nabla_W X, U) = 0$ for all $U, W$ at every point.
Equivalent to the Lie derivative $\mathcal{L}_X g = 0$ (the flow of $X$
is by isometries).

Reference: do Carmo §3 Ex. 5; Petersen Ch. 8. -/
def IsKilling (g : RiemannianMetric I M) (X : SmoothVectorField I M) : Prop :=
  ∀ (U W : SmoothVectorField I M) (y : M),
    g.metricInner y ((covDeriv g U X) y) (W y)
      + g.metricInner y ((covDeriv g W X) y) (U y) = 0

/-- **Math.** Covariantly differentiating the Killing equation.

For a Killing field `X`, the tensor
`(U, V, W) ↦ ⟪∇_U ∇_V X - ∇_{∇_U V} X, W⟫` is skew in its last two slots.
This is the textbook "differentiate the Killing equation and subtract the
connection terms" step. -/
private lemma IsKilling.second_covDeriv_inner_skew
    (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (hX : IsKilling g X)
    (U V W : SmoothVectorField I M) (x : M) :
    g.metricInner x
        (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x
          - covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x) (W x)
      + g.metricInner x
        (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x
          - covDeriv g (fun y => covDeriv g U.toFun W.toFun y) X.toFun x) (V x)
      = 0 := by
  classical
  let f : M → ℝ := fun y =>
    g.metricInner y (covDeriv g V.toFun X.toFun y) (W y)
  let kw_g : M → ℝ := fun y =>
    g.metricInner y (covDeriv g W.toFun X.toFun y) (V y)
  have h_kill_fun : (fun y : M => f y + kw_g y) = fun _ => 0 := by
    funext y
    exact hX V W y
  have h_deriv_zero : mDirDeriv (fun y : M => f y + kw_g y) x (U x) = 0 := by
    rw [h_kill_fun]
    rw [mDirDeriv, mfderiv_const]
    rfl
  have h_dVX : TangentSmoothAt (fun y : M => covDeriv g V.toFun X.toFun y) x :=
    covDeriv_smoothVF_smoothAt g V X x
  have h_dWX : TangentSmoothAt (fun y : M => covDeriv g W.toFun X.toFun y) x :=
    covDeriv_smoothVF_smoothAt g W X x
  have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) f x := by
    exact g.metricInner_mdifferentiableAt_of_tangentSmoothAt h_dVX (W.smoothAt x)
  have hkw_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) kw_g x := by
    exact g.metricInner_mdifferentiableAt_of_tangentSmoothAt h_dWX (V.smoothAt x)
  have h_deriv_add :
      mDirDeriv (fun y : M => f y + kw_g y) x (U x)
        = mDirDeriv f x (U x) + mDirDeriv kw_g x (U x) := by
    unfold mDirDeriv
    rw [show (fun y : M => f y + kw_g y) = f + kw_g from rfl,
      mfderiv_add hf_mdiff hkw_mdiff]
    rfl
  have h_compat_f := leviCivitaConnection_metric_compatible g
    U.toFun (fun y : M => covDeriv g V.toFun X.toFun y) W.toFun x
    (U.smoothAt x) h_dVX (W.smoothAt x)
  have h_compat_g := leviCivitaConnection_metric_compatible g
    U.toFun (fun y : M => covDeriv g W.toFun X.toFun y) V.toFun x
    (U.smoothAt x) h_dWX (V.smoothAt x)
  change mDirDeriv f x (U x)
      = g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x) (W x)
        + g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
    at h_compat_f
  change mDirDeriv kw_g x (U x)
      = g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x) (V x)
        + g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x)
    at h_compat_g
  have h_expanded :
      g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x) (W x)
        + g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
        + (g.metricInner x
            (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x) (V x)
          + g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x))
        = 0 := by
    linarith [h_deriv_zero, h_deriv_add, h_compat_f, h_compat_g]
  have h_cross_W :
      g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
        = -g.metricInner x
            (covDeriv g (fun y : M => covDeriv g U.toFun W.toFun y) X.toFun x) (V x) := by
    have h := hX (SmoothVectorField.const (I := I) (M := M)
        (covDeriv g U.toFun W.toFun x)) V x
    change
      g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun W.toFun y) x))
          (V x)
        + g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x) = 0 at h
    have h_comm :
        g.metricInner x (covDeriv g V.toFun X.toFun x) (covDeriv g U.toFun W.toFun x)
          + g.metricInner x
            ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun W.toFun y) x))
            (V x) = 0 := by
      rw [add_comm]
      exact h
    exact eq_neg_of_add_eq_zero_left h_comm
  have h_cross_V :
      g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x)
        = -g.metricInner x
            (covDeriv g (fun y : M => covDeriv g U.toFun V.toFun y) X.toFun x) (W x) := by
    have h := hX (SmoothVectorField.const (I := I) (M := M)
        (covDeriv g U.toFun V.toFun x)) W x
    change
      g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun V.toFun y) x))
          (W x)
        + g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x) = 0 at h
    have h_comm :
        g.metricInner x (covDeriv g W.toFun X.toFun x) (covDeriv g U.toFun V.toFun x)
          + g.metricInner x
            ((leviCivitaConnection (I := I) (M := M) g).toFun X.toFun x ((fun y : M => covDeriv g U.toFun V.toFun y) x))
            (W x) = 0 := by
      rw [add_comm]
      exact h
    exact eq_neg_of_add_eq_zero_left h_comm
  rw [g.metricInner_sub_left, g.metricInner_sub_left]
  show g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x) (W x)
      - g.metricInner x (covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x) (W x)
      + (g.metricInner x (covDeriv g U.toFun (fun y => covDeriv g W.toFun X.toFun y) x) (V x)
        - g.metricInner x (covDeriv g (fun y => covDeriv g U.toFun W.toFun y) X.toFun x) (V x))
      = 0
  linarith [h_expanded, h_cross_W, h_cross_V]

/-- **Math.** Commutator of the second covariant derivative operator:
`H(U,V)X - H(V,U)X = R(U,V)X`, where
`H(U,V)X = ∇_U∇_V X - ∇_{∇_U V}X`. -/
private lemma second_covDeriv_commutator
    (g : RiemannianMetric I M)
    (X U V : SmoothVectorField I M) (x : M) :
    (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x
        - covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x)
      - (covDeriv g V.toFun (fun y => covDeriv g U.toFun X.toFun y) x
        - covDeriv g (fun y => covDeriv g V.toFun U.toFun y) X.toFun x)
      = riemannCurvature g U V X x := by
  rw [riemannCurvature_commutator_form]
  have h_torsion := covDeriv_sub_swap_eq_mlieBracket g U.toFun V.toFun x
    (U.smoothAt x) (V.smoothAt x)
  unfold covDeriv at h_torsion ⊢
  rw [← h_torsion]
  simp only [map_sub]
  abel_nf

/-- **Math.** **Killing field PDE**: a Killing vector field `X` satisfies
$$\nabla^2_{Y, Z} X = R(Y, X) Z$$
for all vector fields `Y, Z` and points `x`, where
$\nabla^2_{Y, Z} W := \nabla_Y(\nabla_Z W) - \nabla_{\nabla_Y Z} W$.

This is **the** PDE characterizing infinitesimal isometries — the
linearization of "flow generates isometries". Foundation for the
Bochner–Yano dimension bound `dim Isom(M) ≤ n(n+1)/2` and the rigidity
of constant-sectional-curvature manifolds.

With OpenGA's convention
`Riem(U,V)X = ∇_U∇_V X - ∇_V∇_U X - ∇_[U,V] X`, the right-hand side is
`riemannCurvature g Y X Z`, equivalently `-riemannCurvature g X Y Z`.

Reference: do Carmo, *Riemannian Geometry*, §3 Ex. 5; Petersen, Ch. 8 §2;
Cheeger–Ebin §1.84. -/
theorem IsKilling.second_covDeriv_eq_curvature
    (g : RiemannianMetric I M)
    (X : SmoothVectorField I M) (hX : IsKilling g X)
    (Y Z : SmoothVectorField I M) (x : M) :
    covDeriv g Y.toFun (covDeriv g Z X) x
      - covDeriv g (covDeriv g Y Z) X.toFun x
      = riemannCurvature g Y X Z x := by
  classical
  apply (g.metricInner_eq_iff_eq x _ _).mp
  intro w
  set W : SmoothVectorField I M := SmoothVectorField.const (I := I) (M := M) w with hW_def
  let A (U V W : SmoothVectorField I M) : ℝ :=
    g.metricInner x
      (covDeriv g U.toFun (fun y => covDeriv g V.toFun X.toFun y) x
        - covDeriv g (fun y => covDeriv g U.toFun V.toFun y) X.toFun x) (W x)
  let C (U V W : SmoothVectorField I M) : ℝ :=
    g.metricInner x (riemannCurvature g U V X x) (W x)
  have h_skew_Y : A Y Z W + A Y W Z = 0 := by
    simpa [A] using IsKilling.second_covDeriv_inner_skew g X hX Y Z W x
  have h_skew_Z : A Z W Y + A Z Y W = 0 := by
    simpa [A] using IsKilling.second_covDeriv_inner_skew g X hX Z W Y x
  have h_skew_W : A W Y Z + A W Z Y = 0 := by
    simpa [A] using IsKilling.second_covDeriv_inner_skew g X hX W Y Z x
  have h_comm_YZ : A Y Z W - A Z Y W = C Y Z W := by
    have h := congrArg (fun v => g.metricInner x v (W x))
      (second_covDeriv_commutator g X Y Z x)
    change g.metricInner x
        ((covDeriv g Y.toFun (fun y => covDeriv g Z.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Y.toFun Z.toFun y) X.toFun x)
          - (covDeriv g Z.toFun (fun y => covDeriv g Y.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Z.toFun Y.toFun y) X.toFun x)) (W x)
        = g.metricInner x (riemannCurvature g Y Z X x) (W x) at h
    rw [g.metricInner_sub_left] at h
    simpa [A, C] using h
  have h_comm_ZW : A Z W Y - A W Z Y = C Z W Y := by
    have h := congrArg (fun v => g.metricInner x v (Y x))
      (second_covDeriv_commutator g X Z W x)
    change g.metricInner x
        ((covDeriv g Z.toFun (fun y => covDeriv g W.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Z.toFun W.toFun y) X.toFun x)
          - (covDeriv g W.toFun (fun y => covDeriv g Z.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g W.toFun Z.toFun y) X.toFun x)) (Y x)
        = g.metricInner x (riemannCurvature g Z W X x) (Y x) at h
    rw [g.metricInner_sub_left] at h
    simpa [A, C] using h
  have h_comm_WY : A W Y Z - A Y W Z = C W Y Z := by
    have h := congrArg (fun v => g.metricInner x v (Z x))
      (second_covDeriv_commutator g X W Y x)
    change g.metricInner x
        ((covDeriv g W.toFun (fun y => covDeriv g Y.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g W.toFun Y.toFun y) X.toFun x)
          - (covDeriv g Y.toFun (fun y => covDeriv g W.toFun X.toFun y) x
            - covDeriv g (fun y => covDeriv g Y.toFun W.toFun y) X.toFun x)) (Z x)
        = g.metricInner x (riemannCurvature g W Y X x) (Z x) at h
    rw [g.metricInner_sub_left] at h
    simpa [A, C] using h
  have h_curv : C Y Z W - C Z W Y + C W Y Z
      = 2 * g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
    have h_bianchi := bianchi_first g X W Y x
    have h_inner :
        g.metricInner x (riemannCurvature g X W Y x + riemannCurvature g W Y X x + riemannCurvature g Y X W x) (Z x)
          = 0 := by
      rw [h_bianchi]
      exact g.metricInner_zero_left x (Z x)
    rw [g.metricInner_add_left, g.metricInner_add_left] at h_inner
    have h_pair₁ : C Y Z W = g.metricInner x (riemannCurvature g X W Y x) (Z x) := by
      simpa [C] using riemannCurvature_pair_symm g Y Z X W x
    have h_pair₂ : C Z W Y = g.metricInner x (riemannCurvature g X Y Z x) (W x) := by
      simpa [C] using riemannCurvature_pair_symm g Z W X Y x
    have h_pair₃ : C W Y Z = g.metricInner x (riemannCurvature g X Z W x) (Y x) := by
      simpa [C] using riemannCurvature_pair_symm g W Y X Z x
    have h_antisym12 :
        g.metricInner x (riemannCurvature g X Y Z x) (W x)
          = -g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
      rw [riemannCurvature_antisymm g X.toFun Y.toFun Z.toFun x, g.metricInner_neg_left]
    have h_antisym34 :
        g.metricInner x (riemannCurvature g Y X W x) (Z x)
          = -g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
      have h := riemannCurvature_metric_skew g Y X W Z x
      linarith
    rw [h_pair₁, h_pair₂, h_pair₃]
    linarith [h_inner, h_antisym12, h_antisym34]
  have h_A : 2 * A Y Z W = C Y Z W - C Z W Y + C W Y Z := by
    linarith [h_skew_Y, h_skew_Z, h_skew_W, h_comm_YZ, h_comm_ZW, h_comm_WY]
  have h_target : A Y Z W = g.metricInner x (riemannCurvature g Y X Z x) (W x) := by
    linarith [h_A, h_curv]
  simpa [A, hW_def] using h_target

end Riemannian
