import OpenGALib.Riemannian.Curvature.RiemannCurvature

/-! # Symmetries of the Riemann curvature tensor -/

open Bundle VectorField
open scoped ContDiff Manifold Riemannian InnerProductSpace

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianSetup I M]

/-! ### Diagonal `(3,4)` vanishing: $g(R(X,Y)Z, Z) = 0$

do Carmo §4 Proposition 2.5(iii) closure. The proof reduces, via metric
compatibility applied diagonally at every $y$, to the half-derivative
identity $D_V (g(Z, Z))(y) = 2\,g(\nabla_V Z, Z)(y)$. Differentiating
again at $x$ and using metric-compat once more expresses each
$g(\nabla_W \nabla_V Z, Z)$ in terms of iterated directional derivatives
of $f := g(Z, Z)$; the Hessian–Lie identity
(`mfderiv_iterate_sub_eq_mlieBracket_apply`) collapses
$X(Y(f)) - Y(X(f)) - [X,Y](f) = 0$, closing the chain. -/

/-- **Math.** **Diagonal metric-compat identity**: at every point $y \in M$ with
the direction $V$ smooth, metric compatibility gives
$$D_V (g(Z, Z))(y) = 2\,\langle \nabla_V Z, Z\rangle_g(y).$$
Stated using `mDirDeriv` (the `ℝ`-typed `mfderiv` wrapper) on the LHS
and `(leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun` (definitionally equal to `covDeriv HasMetric.metric`)
on the RHS. -/
private lemma mDirDeriv_self_eq_two_metricInner_leviCivita_self
    (g : RiemannianMetric I M)
    (V : VectorFieldSection I M) (Z : SmoothVectorField I M) (y : M)
    (hV : TangentSmoothAt V y) :
    mDirDeriv (fun y' => g.metricInner y' (Z y') (Z y')) y (V y)
      = 2 * g.metricInner y
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y) := by
  -- Bridge metric-compat ∇ → `.toFun` form so `rw [hsym]` matches the structural shape.
  have h := leviCivitaConnection_metric_compatible g V Z.toFun Z.toFun y
    hV (Z.smoothAt y) (Z.smoothAt y)
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h
  -- Cast h to typeclass `metricInner` form for rw matching.
  change mDirDeriv (fun y' => g.metricInner y' (Z y') (Z y')) y (V y)
      = g.metricInner y
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y))
          (Z y)
        + g.metricInner y (Z y)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y))
    at h
  have hsym :
      g.metricInner y (Z y)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y))
        = g.metricInner y
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y) :=
    g.metricInner_comm y _ _
  rw [hsym] at h
  have h_ℝ : mDirDeriv (fun y' => g.metricInner y' (Z y') (Z y')) y (V y)
      = g.metricInner y
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y)
        + g.metricInner y
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y (V y)) (Z y) :=
    h
  rw [h_ℝ]; ring

/-- **Eng.** Function-equality form: at every $y$, the directional derivative of
$y \mapsto g(Z, Z)(y)$ along the smooth vector field $V$ equals
$2\,g(\nabla_V Z, Z)(y)$. -/
private lemma fun_mDirDeriv_self_eq_two_metricInner_leviCivita_self
    (g : RiemannianMetric I M)
    (V Z : SmoothVectorField I M) :
    (fun y' : M => mDirDeriv (fun y'' => g.metricInner y'' (Z y'') (Z y'')) y' (V.toFun y'))
      = (fun y' : M => 2 * g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := by
  funext y'
  exact mDirDeriv_self_eq_two_metricInner_leviCivita_self g V.toFun Z y' (V.smoothAt y')

/-- **Math.** **Iterated metric-compat identity at $x$**: differentiating the
diagonal identity once more at $x$ in direction $W(x)$ and applying
metric-compat at $x$ yields
$$\tfrac12\,W\!\left(V (g(Z, Z))\right)(x)
  = \langle \nabla_W \nabla_V Z, Z\rangle_g(x)
    + \langle \nabla_V Z, \nabla_W Z\rangle_g(x).$$ -/
private lemma half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (V W Z : SmoothVectorField I M) (x : M) :
    (1/2 : ℝ) * mDirDeriv
        (fun y' : M => mDirDeriv
          (fun y'' => g.metricInner y'' (Z y'') (Z y'')) y' (V.toFun y')) x (W.toFun x)
      = g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun
            (fun y' => covDeriv g V.toFun Z.toFun y') x (W.toFun x))
          (Z x)
        + g.metricInner x (covDeriv g V.toFun Z.toFun x)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (W.toFun x)) := by
  -- Use function-equality form of the diagonal identity to rewrite the LHS
  -- inner function; then apply mfderiv_const_smul and metric-compat at x.
  have h_fun := fun_mDirDeriv_self_eq_two_metricInner_leviCivita_self g V Z
  -- Sections smooth at x.
  have hcovVZ : TangentSmoothAt (fun y' => covDeriv g V.toFun Z.toFun y') x :=
    covDeriv_smoothVF_smoothAt g V Z x
  -- The mfderiv of LHS (the iterated mDirDeriv expression) at x in dir W(x):
  -- by h_fun, equals mfderiv of `fun y' => 2 * g(∇_V Z, Z)(y')` at x in dir W(x).
  -- That = 2 * mfderiv (g(∇_V Z, Z)) x (W x), and by metric-compat at x:
  --      = 2 * [g(∇_W ∇_V Z, Z) + g(∇_V Z, ∇_W Z)] x.
  -- So (1/2) * LHS = g(∇_W ∇_V Z, Z) x + g(∇_V Z, ∇_W Z) x.
  -- Bridge metric-compat ∇ → `.toFun` form for downstream `g.metricInner_comm` / `linarith`.
  have h_compat := leviCivitaConnection_metric_compatible g
    W.toFun (fun y' => covDeriv g V.toFun Z.toFun y') Z.toFun x
    (W.smoothAt x) hcovVZ (Z.smoothAt x)
  simp only [← leviCivitaConnection_toFun_eq_covDeriv] at h_compat
  -- h_compat : mfderiv (fun y' => g(∇_V Z, Z) y') x (W x) =
  --              g(∇_W (∇_V Z), Z) + g(∇_V Z, ∇_W Z)
  -- Rewrite the LHS function via h_fun:
  conv_lhs => rw [show (fun y' : M => mDirDeriv
        (fun y'' => g.metricInner y'' (Z y'') (Z y'')) y' (V.toFun y'))
      = (fun y' : M => 2 * g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) from h_fun]
  -- Now LHS = (1/2) * mfderiv (fun y' => 2 * g(∇_V Z, Z) y') x (W x)
  -- Pull the 2 out: mfderiv (2 * h) x v = 2 * mfderiv h x v (linear).
  -- The function under mfderiv:  fun y' => 2 * g(LC.toFun Z y' (V y'), Z y')
  -- equals  2 • (fun y' => g(LC.toFun Z y' (V y'), Z y'))  via funext.
  -- Use mfderiv_const_smul; we need MDifferentiableAt of the inner section.
  -- The "covDeriv g V Z = LC.toFun Z y (V y)" is def-eq; the inner section's
  -- smoothness at x is hcovVZ (via g.metricInner_mdifferentiableAt).
  have h_inner_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y' : M => g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y')) x := by
    -- The function is `y' ↦ g(covDeriv g V Z y', Z y')` (def-eq covDeriv g ↔ LC.toFun).
    -- Use `g.metricInner_mdifferentiableAt` with `hcovVZ` and `Z.smoothAt x`.
    have h := g.metricInner_mdifferentiableAt
      (v := fun y' => covDeriv g V.toFun Z.toFun y') (w := Z.toFun) hcovVZ (Z.smoothAt x)
    exact h
  -- Avoid continuous linear map-smul issues by writing `2 * h = h + h` and using `mfderiv_add`.
  have h_two_add : (fun y' : M => (2 : ℝ) * g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y'))
      = (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')
        + g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := by
    funext y'; ring
  rw [h_two_add]
  -- Now: (1/2) * mDirDeriv (fun y' => h y' + h y') x (W x) where h := g(∇_V Z, Z) y'.
  -- Convert `fun y' => h y' + h y'` to the Pi-add form `h + h` (definitional).
  have h_pi_add : (fun y' : M => g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y')
      + g.metricInner y'
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
        (Z y'))
      = (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) := rfl
  rw [h_pi_add]
  -- `mfderiv (f + g) x v = mfderiv f x v + mfderiv g x v`.
  -- Compute the continuous linear map add via `mfderiv_add` then evaluate at `W.toFun x`.
  have h_clm_add :
      mfderiv I 𝓘(ℝ, ℝ) ((fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y'))) x
        = mfderiv I 𝓘(ℝ, ℝ) (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y')) x
          + mfderiv I 𝓘(ℝ, ℝ) (fun y' : M => g.metricInner y'
              ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
              (Z y')) x :=
    mfderiv_add h_inner_mdiff h_inner_mdiff
  -- Apply both sides to (W.toFun x) and use continuous linear map-add evaluation.
  have h_val_add : mDirDeriv ((fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y'))
        + (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y'))) x (W.toFun x)
      = mDirDeriv (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) x (W.toFun x)
        + mDirDeriv (fun y' : M => g.metricInner y'
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
            (Z y')) x (W.toFun x) := by
    show mfderiv I 𝓘(ℝ, ℝ) _ x (W.toFun x) = _
    rw [h_clm_add]
    rfl
  rw [h_val_add]
  -- Now: (1/2) * (mDirDeriv h x v + mDirDeriv h x v) = h_compat
  have h_compat_ℝ :
      mDirDeriv (fun y' : M => g.metricInner y'
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun y' (V.toFun y'))
          (Z y')) x (W.toFun x)
        = g.metricInner x
            ((leviCivitaConnection (I := I) (M := M) g).toFun
              (fun y' => covDeriv g V.toFun Z.toFun y') x (W.toFun x))
            (Z x)
          + g.metricInner x (covDeriv g V.toFun Z.toFun x)
            ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (W.toFun x)) :=
    h_compat
  rw [h_compat_ℝ]; ring

/-- **Math.** $\langle R(X, Y) Z, Z \rangle_g(x) = 0$ for smooth vector fields
$X, Y, Z$.

The Hessian–Lie identity used internally requires $\mathrm{extChartAt}\,I\,x\,x$
to lie in the closure of the interior of $\mathrm{range}\,I$; this holds
unconditionally here because `I.Boundaryless` makes `Set.range I = univ`,
so the hypothesis is discharged inside the proof rather than exposed.

Reference: do Carmo §4 Proposition 2.5(iii). -/
theorem riemannCurvature_inner_self_zero
    (g : RiemannianMetric I M)
    [IsManifold I 2 M]
    (X Y Z : SmoothVectorField I M) (x : M) :
    g.metricInner x (riemannCurvature g X.toFun Y.toFun Z.toFun x) (Z x) = 0 := by
  classical
  -- `I.Boundaryless` makes `Set.range I = univ`, so the interior-closure
  -- membership required by the Hessian–Lie identity holds unconditionally.
  have h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) := by
    rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
    exact Set.mem_univ _
  -- Setup: f := g(Z, Z), the self-norm-squared scalar function.
  set f : M → ℝ := fun y' => g.metricInner y' (Z y') (Z y') with hf_def
  -- f is C∞ globally, hence C² at x.
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := fun y =>
    g.metricInner_contMDiffAt (n := ∞) (Z.smooth y) (Z.smooth y)
  have hf_2 : ContMDiffAt I 𝓘(ℝ, ℝ) 2 f x :=
    (hf_smooth x).of_le (by
      show ((2 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤))
  -- [X, Y] is smooth at x (Mathlib + framework's mlieBracket_tangentSmoothAt).
  have hXY_br : TangentSmoothAt (mlieBracket I X.toFun Y.toFun) x :=
    mlieBracket_tangentSmoothAt X.smooth Y.smooth
  -- Equations (A) and (B): iterated metric-compat at x.
  have hA := half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv g X Y Z x  -- (V=X, W=Y)
  have hB := half_mDirDeriv_iterate_eq_metricInner_iterCovDeriv g Y X Z x  -- (V=Y, W=X)
  -- Equation (C): metric-compat at x for V = [X, Y].
  have hC := mDirDeriv_self_eq_two_metricInner_leviCivita_self g
    (mlieBracket I X.toFun Y.toFun) Z x hXY_br
  -- Hessian–Lie identity at x: X(Y(f))(x) - Y(X(f))(x) = mfderiv f x ([X,Y](x))
  have hX1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, X.toFun y⟩ : TangentBundle I M)) x :=
    (X.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hY1 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, Y.toFun y⟩ : TangentBundle I M)) x :=
    (Y.smooth x).of_le (by
      show ((1 : ℕ∞) : ℕ∞ω) ≤ ∞
      exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hHL : mDirDeriv (fun y' => mDirDeriv f y' (Y.toFun y')) x (X.toFun x)
      - mDirDeriv (fun y' => mDirDeriv f y' (X.toFun y')) x (Y.toFun x)
      = mDirDeriv f x (mlieBracket I X.toFun Y.toFun x) :=
    mfderiv_iterate_sub_eq_mlieBracket_apply f X.toFun Y.toFun x h_interior hf_2 hX1 hY1
  -- Inner product cross-cancel: g(∇_X Z, ∇_Y Z) = g(∇_Y Z, ∇_X Z).
  have h_inner_comm : g.metricInner x (covDeriv g X.toFun Z.toFun x)
        ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (Y.toFun x))
      = g.metricInner x (covDeriv g Y.toFun Z.toFun x)
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (X.toFun x)) := by
    show g.metricInner x ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (X.toFun x))
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (Y.toFun x))
      = g.metricInner x ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (Y.toFun x))
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x (X.toFun x))
    exact g.metricInner_comm x _ _
  -- Expand R via riemannCurvature_commutator_form g + g.metricInner_sub_left twice.
  show g.metricInner x (riemannCurvature g X.toFun Y.toFun Z.toFun x) (Z x) = 0
  rw [riemannCurvature_commutator_form]
  -- Goal: g(∇_X ∇_Y Z - ∇_Y ∇_X Z - ∇_{[X,Y]} Z, Z) x = 0
  rw [show g.metricInner x (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
        - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
        - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x) (Z x)
      = g.metricInner x (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x) (Z x)
        - g.metricInner x (covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x) (Z x)
        - g.metricInner x (covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x) (Z x)
      from by
    rw [show ((covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
          - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x
          - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x : TangentSpace I x))
        = (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z.toFun y) x
          - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z.toFun y) x)
          - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z.toFun x from rfl,
      g.metricInner_sub_left, g.metricInner_sub_left]]
  -- Now: g(∇_X ∇_Y Z, Z) - g(∇_Y ∇_X Z, Z) - g(∇_{[X,Y]} Z, Z) = 0
  -- From hB (V=Y, W=X): (1/2) X(Y(f))(x) = g(∇_X ∇_Y Z, Z) + g(∇_Y Z, ∇_X Z)
  --                    ⇒ g(∇_X ∇_Y Z, Z) = (1/2) X(Y(f))(x) - g(∇_Y Z, ∇_X Z)
  -- From hA (V=X, W=Y): g(∇_Y ∇_X Z, Z) = (1/2) Y(X(f))(x) - g(∇_X Z, ∇_Y Z)
  -- From hC: 2 g(∇_{[X,Y]} Z, Z) = D_{[X,Y]} f(x)
  --        ⇒ g(∇_{[X,Y]} Z, Z) = (1/2) D_{[X,Y]} f(x) = (1/2) mDirDeriv f x ([X,Y] x)
  -- Combine: difference = (1/2) [X(Y(f)) - Y(X(f)) - [X,Y](f)] - inner cross-cancel = 0.
  -- Show all four covDeriv g terms are def-equal to LC.toFun forms:
  show g.metricInner x
        ((leviCivitaConnection (I := I) (M := M) g).toFun
          (fun y => covDeriv g Y.toFun Z.toFun y) x (X.toFun x)) (Z x)
      - g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun
            (fun y => covDeriv g X.toFun Z.toFun y) x (Y.toFun x)) (Z x)
      - g.metricInner x
          ((leviCivitaConnection (I := I) (M := M) g).toFun Z.toFun x
            (VectorField.mlieBracket I X.toFun Y.toFun x)) (Z x)
      = 0
  -- Substitute via hA, hB, hC, hHL.
  -- hB: (1/2) X(Y(f))(x) = g(LC.toFun (∇_Y Z) x (X x), Z) + g(∇_Y Z, LC.toFun Z x (X x))
  -- ⇒ g(LC.toFun (∇_Y Z) x (X x), Z) = (1/2) X(Y(f))(x) - g(∇_Y Z, LC.toFun Z x (X x))
  -- hA: g(LC.toFun (∇_X Z) x (Y x), Z) = (1/2) Y(X(f))(x) - g(∇_X Z, LC.toFun Z x (Y x))
  -- hC: 2 g(LC.toFun Z x ([X,Y] x), Z) = mDirDeriv f x ([X,Y] x)
  -- Substitute and use hHL: X(Y(f)) - Y(X(f)) = mDirDeriv f x ([X,Y] x); h_inner_comm cancel.
  linarith [hA, hB, hC, hHL, h_inner_comm]

/-! ### Metric-skew of Riemann curvature in the (3rd, 4th) slot

Polarisation of `riemannCurvature_inner_self_zero` on $Z + W$ yields the
classical metric-skew identity
$\langle R(X, Y) Z, W\rangle_g + \langle R(X, Y) W, Z\rangle_g = 0$. -/

/-- **Math.** **Additivity of `riemannCurvature HasMetric.metric` in the differentiated (3rd) slot**:
$R(X, Y)(Z_1 + Z_2)(x) = R(X, Y) Z_1(x) + R(X, Y) Z_2(x)$ for $X, Y, Z_i$
smooth vector fields. Direct from `covDeriv_add_field` applied at $x$
(outer) and at every $y$ (inner section sum) plus `funext`.

Public-exposure of formerly `private` helper, needed by the Z-slot
additivity step of the full 3-slot tensoriality chain
(`Riemannian/Curvature/Tensoriality.lean`). -/
theorem riemannCurvature_add_third
    (g : RiemannianMetric I M)
    (X Y Z₁ Z₂ : SmoothVectorField I M) (x : M) :
    riemannCurvature g X.toFun Y.toFun (Z₁ + Z₂).toFun x
      = riemannCurvature g X.toFun Y.toFun Z₁.toFun x
        + riemannCurvature g X.toFun Y.toFun Z₂.toFun x := by
  classical
  have h_pi_add : (Z₁ + Z₂).toFun = Z₁.toFun + Z₂.toFun := by
    funext y; show (Z₁ + Z₂) y = Z₁ y + Z₂ y; rfl
  have h_inner_Y : (fun y => covDeriv g Y.toFun (Z₁ + Z₂).toFun y)
      = (fun y => covDeriv g Y.toFun Z₁.toFun y)
        + (fun y => covDeriv g Y.toFun Z₂.toFun y) := by
    funext y
    rw [h_pi_add]
    exact covDeriv_add_field g Y.toFun Z₁.toFun Z₂.toFun y
      (Z₁.smoothAt y) (Z₂.smoothAt y)
  have h_inner_X : (fun y => covDeriv g X.toFun (Z₁ + Z₂).toFun y)
      = (fun y => covDeriv g X.toFun Z₁.toFun y)
        + (fun y => covDeriv g X.toFun Z₂.toFun y) := by
    funext y
    rw [h_pi_add]
    exact covDeriv_add_field g X.toFun Z₁.toFun Z₂.toFun y
      (Z₁.smoothAt y) (Z₂.smoothAt y)
  show covDeriv g X.toFun (fun y => covDeriv g Y.toFun (Z₁ + Z₂).toFun y) x
      - covDeriv g Y.toFun (fun y => covDeriv g X.toFun (Z₁ + Z₂).toFun y) x
      - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) (Z₁ + Z₂).toFun x
    = (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z₁.toFun y) x
        - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z₁.toFun y) x
        - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z₁.toFun x)
      + (covDeriv g X.toFun (fun y => covDeriv g Y.toFun Z₂.toFun y) x
        - covDeriv g Y.toFun (fun y => covDeriv g X.toFun Z₂.toFun y) x
        - covDeriv g (VectorField.mlieBracket I X.toFun Y.toFun) Z₂.toFun x)
  rw [h_inner_Y, h_inner_X, h_pi_add]
  rw [covDeriv_add_field g X.toFun (fun y => covDeriv g Y.toFun Z₁.toFun y)
        (fun y => covDeriv g Y.toFun Z₂.toFun y) x
        (covDeriv_smoothVF_smoothAt g Y Z₁ x)
        (covDeriv_smoothVF_smoothAt g Y Z₂ x),
      covDeriv_add_field g Y.toFun (fun y => covDeriv g X.toFun Z₁.toFun y)
        (fun y => covDeriv g X.toFun Z₂.toFun y) x
        (covDeriv_smoothVF_smoothAt g X Z₁ x)
        (covDeriv_smoothVF_smoothAt g X Z₂ x),
      covDeriv_add_field g (VectorField.mlieBracket I X.toFun Y.toFun)
        Z₁.toFun Z₂.toFun x (Z₁.smoothAt x) (Z₂.smoothAt x)]
  abel

/-- **Math.** **Metric-skew of the Riemann curvature in the (3rd, 4th) slot**:
$$\langle R(X, Y) Z, W\rangle_g(x) + \langle R(X, Y) W, Z\rangle_g(x) = 0.$$

Derived by polarising `riemannCurvature_inner_self_zero` on $Z + W$:
$$0 = \langle R(X, Y)(Z + W), Z + W\rangle_g
    = \underbrace{\langle R Z, Z\rangle}_{=0} + \langle R Z, W\rangle
      + \langle R W, Z\rangle + \underbrace{\langle R W, W\rangle}_{=0}.$$

Reference: do Carmo §4 Proposition 2.5(iv). -/
theorem riemannCurvature_metric_skew
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (X Y Z W : SmoothVectorField I M) (x : M) :
    g.metricInner x (riemannCurvature g X.toFun Y.toFun Z.toFun x) (W x)
      + g.metricInner x (riemannCurvature g X.toFun Y.toFun W.toFun x) (Z x) = 0 := by
  have h_ZW := riemannCurvature_inner_self_zero g X Y (Z + W) x
  have h_Z := riemannCurvature_inner_self_zero g X Y Z x
  have h_W := riemannCurvature_inner_self_zero g X Y W x
  have h_add := riemannCurvature_add_third g X Y Z W x
  have h_ZW_x : (Z + W) x = Z x + W x := rfl
  rw [h_add, h_ZW_x, g.metricInner_add_left, g.metricInner_add_right,
      g.metricInner_add_right] at h_ZW
  linarith

/-! ### Pair symmetry: $g(R(X,Y)Z, W) = g(R(Z,W)X, Y)$

Standard algebraic corollary of the four-fold Bianchi I sum combined with
$(1,2)$-antisymmetry and $(3,4)$-antisymmetry. After cyclic Bianchi on the
triples $(X,Y,Z),\,(Y,Z,W),\,(Z,W,X),\,(W,X,Y)$ paired against the
respective fourth vector, the antisymmetries cancel 8 of the 12 terms,
leaving the headline identity. -/

/-- **Math.** **Pair symmetry of the Riemann tensor**:
$$g_x(R(X,Y)Z, W) \;=\; g_x(R(Z,W)X, Y).$$

Reference: do Carmo §4 Proposition 2.5 (iv); Petersen Ch. 3. -/
theorem riemannCurvature_pair_symm
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (X Y Z W : SmoothVectorField I M) (x : M) :
    g.metricInner x (riemannCurvature g X Y Z x) (W x)
      = g.metricInner x (riemannCurvature g Z W X x) (Y x) := by
  have bianchi_inner : ∀ (A B C D : SmoothVectorField I M),
      g.metricInner x (riemannCurvature g A B C x) (D x)
        + g.metricInner x (riemannCurvature g B C A x) (D x)
        + g.metricInner x (riemannCurvature g C A B x) (D x) = 0 := by
    intro A B C D
    have h := bianchi_first g A B C x
    have : g.metricInner x
              (riemannCurvature g A B C x + riemannCurvature g B C A x + riemannCurvature g C A B x) (D x)
            = g.metricInner x (0 : TangentSpace I x) (D x) := by rw [h]
    rw [g.metricInner_add_left, g.metricInner_add_left] at this
    rw [g.metricInner_zero_left] at this
    linarith
  have b1 := bianchi_inner X Y Z W
  have b2 := bianchi_inner Y Z W X
  have b3 := bianchi_inner Z W X Y
  have b4 := bianchi_inner W X Y Z
  have antisym12 : ∀ (A B C D : SmoothVectorField I M),
      g.metricInner x (riemannCurvature g A B C x) (D x)
        = -g.metricInner x (riemannCurvature g B A C x) (D x) := by
    intro A B C D
    rw [riemannCurvature_antisymm g A B C x, g.metricInner_neg_left]
  have antisym34 : ∀ (A B C D : SmoothVectorField I M),
      g.metricInner x (riemannCurvature g A B C x) (D x)
        = -g.metricInner x (riemannCurvature g A B D x) (C x) := by
    intro A B C D
    have h := riemannCurvature_metric_skew g A B C D x
    linarith
  -- Combine: sum of b1..b4 with the antisymmetries gives 2·σ(X,Y,Z,W) - 2·σ(Z,W,X,Y) = 0.
  -- Specialise antisym to the 12 σ-instances appearing in b1..b4 and feed to linarith.
  have a1 := antisym12 X Y Z W
  have a2 := antisym12 Y Z X W
  have a3 := antisym12 Z X Y W
  have a4 := antisym12 Y Z W X
  have a5 := antisym12 Z W Y X
  have a6 := antisym12 W Y Z X
  have a7 := antisym12 Z W X Y
  have a8 := antisym12 W X Z Y
  have a9 := antisym12 X Z W Y
  have a10 := antisym12 W X Y Z
  have a11 := antisym12 X Y W Z
  have a12 := antisym12 Y W X Z
  have c1 := antisym34 X Y Z W
  have c2 := antisym34 Y Z X W
  have c3 := antisym34 Z X Y W
  have c4 := antisym34 Y Z W X
  have c5 := antisym34 Z W Y X
  have c6 := antisym34 W Y Z X
  have c7 := antisym34 Z W X Y
  have c8 := antisym34 W X Z Y
  have c9 := antisym34 X Z W Y
  have c10 := antisym34 W X Y Z
  have c11 := antisym34 X Y W Z
  have c12 := antisym34 Y W X Z
  linarith

/-! ### Constant-direction commutator simplification

`R(const v, const w) Z x = ∇_v ∇_w Z - ∇_w ∇_v Z` at $x$ — the
$\nabla_{[X, Y]} Z$ term drops because $[\mathrm{const}\,v, \mathrm{const}\,w] = 0$
as a global section (`mlieBracket_const_const_apply_zero`), so the connection
evaluates `(leviCivitaConnection (I := I) (M := M) HasMetric.metric).toFun Z x` at the zero vector. -/

/-! ### Constant-direction Bianchi swap

Specialisation of `bianchi_first` to the triple $(\mathrm{const}\,v, X, Y)$,
combined with `riemannCurvature_antisymm` on the third Bianchi summand:
$$R(\mathrm{const}\,v, X)\,Y - R(\mathrm{const}\,v, Y)\,X
   = -R(X, Y)(\mathrm{const}\,v).$$
This is the per-basis-vector algebraic identity that drives `ricci_symm`. -/

/-- **Math.** **Constant-direction Bianchi swap**. Bianchi I on $(\mathrm{const}\,v, X, Y)$
together with first-pair antisymmetry of $R$ rearranges to the form needed
for the Ricci-symmetry trace argument. -/
private lemma riemannCurvature_const_first_swap_eq_neg
    [IsManifold I 2 M]
    (g : RiemannianMetric I M)
    (v : E) (X Y : SmoothVectorField I M) (x : M) :
    riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
        - riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x
      = -riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x := by
  classical
  set V : SmoothVectorField I M := SmoothVectorField.const (I := I) (M := M) v with hV_def
  have h_bianchi : riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
        + riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x
        + riemannCurvature g Y.toFun (fun _ : M => v) X.toFun x = 0 :=
    bianchi_first g V X Y x
  have h_antisym :
      riemannCurvature g Y.toFun (fun _ : M => v) X.toFun x
        = -riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x :=
    riemannCurvature_antisymm g Y.toFun (fun _ : M => v) X.toFun x
  rw [h_antisym] at h_bianchi
  apply eq_neg_of_add_eq_zero_left
  rw [show (riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
              - riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x
            + riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x
            : TangentSpace I x)
        = riemannCurvature g (fun _ : M => v) X.toFun Y.toFun x
            + riemannCurvature g X.toFun Y.toFun (fun _ : M => v) x
            + -riemannCurvature g (fun _ : M => v) Y.toFun X.toFun x from by abel]
  exact h_bianchi

/-- **Math.** $\mathrm{Ric}(X, Y) = \mathrm{Ric}(Y, X)$.

Reference: do Carmo §4 ex. 1.

Closure via:
* `LinearMap.trace_eq_sum_inner` on `curvatureEndo X Y x` against
  `stdOrthonormalBasis ℝ (T_xM)` (so each Ricci scalar is a sum of
  $\langle b_i, R(\mathrm{const}\,b_i, X)\,Y\,x\rangle$ pairings),
* `riemannCurvature_const_first_swap_eq_neg` per basis vector (Bianchi I +
  antisym packaging),
* `riemannCurvature_inner_self_zero` on $(X, Y, \mathrm{const}\,b_i)$ to kill
  every summand.

The interior-closure hypothesis previously threaded into
`riemannCurvature_inner_self_zero` is now discharged there internally
from `I.Boundaryless`, so no boundary side-condition is exposed here. -/
theorem ricci_symm
    [IsManifold I 2 M]
    (g : RiemannianMetric I M) (hg : g = HasMetric.metric)
    (X Y : SmoothVectorField I M) (x : M)
    (_h_interior : extChartAt I x x ∈ closure (interior (Set.range I)) := by
      rw [ModelWithCorners.Boundaryless.range_eq_univ, interior_univ, closure_univ]
      exact Set.mem_univ _) :
    ricci g X Y x = ricci g Y X x := by
  subst hg
  classical
  set b := stdOrthonormalBasis ℝ (TangentSpace I x) with hb_def
  have h_RXY : ricci HasMetric.metric X Y x =
      ∑ i, ⟪b i, riemannCurvature HasMetric.metric (fun _ : M => (b i : E)) X.toFun Y.toFun x⟫_ℝ := by
    show LinearMap.trace ℝ (TangentSpace I x)
          (curvatureEndo HasMetric.metric X Y x) = _
    exact LinearMap.trace_eq_sum_inner _ b
  have h_RYX : ricci HasMetric.metric Y X x =
      ∑ i, ⟪b i, riemannCurvature HasMetric.metric (fun _ : M => (b i : E)) Y.toFun X.toFun x⟫_ℝ := by
    show LinearMap.trace ℝ (TangentSpace I x)
          (curvatureEndo HasMetric.metric Y X x) = _
    exact LinearMap.trace_eq_sum_inner _ b
  rw [h_RXY, h_RYX]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← sub_eq_zero, ← inner_sub_right,
      riemannCurvature_const_first_swap_eq_neg (I := I) (M := M) HasMetric.metric (b i : E) X Y x]
  rw [inner_neg_right, neg_eq_zero]
  rw [real_inner_comm]
  exact riemannCurvature_inner_self_zero HasMetric.metric X Y
    (SmoothVectorField.const (I := I) (M := M) (b i : E)) x


end Riemannian
