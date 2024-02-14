From category Require Import
  base
  setoid
  category
  functor
  initial
  colimit.

Section BinSum.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Record BinSum {C : Category} (X Y : C) :=
    {
      bin_sum_obj :> C;
      bin_inj_arr₁ : X [~>] bin_sum_obj;
      bin_inj_arr₂ : Y [~>] bin_sum_obj;
      bin_inj_ump : ∀ (p' : C) (p₁ : X [~>] p') (p₂ : Y [~>] p'),
        Σ! (u : bin_sum_obj [~>] p'),
        p₁ ≡ u ∘ bin_inj_arr₁ ∧ p₂ ≡ u ∘ bin_inj_arr₂;
    }.

  Program Definition BinSumCone {C : Category} {X Y : C} (p : BinSum X Y)
    : CoconeCat (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y))
    :=
    {|
      cocone_obj := p;
      cocone_nat := λₙ A :: ⌊ bool ⌋,
        (if A as b return
                   (DiscreteFun (λ b0 : ⌊ bool ⌋, if b0 then X else Y) b [~>] (Δ p) A)
         then bin_inj_arr₁ X Y p
         else bin_inj_arr₂ X Y p);
    |}.
  Next Obligation.
    intros; simpl.
    destruct f.
    simpl.
    destruct X0.
    + rewrite arrow_comp_id_l.
      rewrite arrow_comp_id_r.
      reflexivity.
    + rewrite arrow_comp_id_l.
      rewrite arrow_comp_id_r.
      reflexivity.
  Qed.

End BinSum.
