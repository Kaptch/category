From category Require Import
                      base
                      setoid
                      category
                      sets
                      terminal
                      functor
                      limit
                      prod
                      classes.limits
                      exp.

Section Exp.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Class hasExp (C : Category) `{!hasBinaryProducts C} :=
    {
      has_exp : ∀ (X Y : C), Exp X Y;
    }.
End Exp.

Notation "X '⇒' Y '@' C" := (@has_exp C _ _ Y X) (at level 50) : cat_scope.

Section Aux.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition Curry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    : (X ×ₒ Y @ C [~>] Z) [→] (X [~>] (Y ⇒ Z @ C))
    := λₛ f, projT1 (exp_ump Z Y (Y ⇒ Z @ C) X f).
  Next Obligation.
    intros; simpl.
    apply (snd (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X a₁))).
    rewrite H1.
    apply (fst (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X a₂))).
  Qed.

  Program Definition Uncurry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    : (X [~>] (Y ⇒ Z @ C)) [→] (X ×ₒ Y @ C [~>] Z)
    := λₛ f, (eval Z Y (Y ⇒ Z @ C) ∘ ⟨ f ×ₐ ı ⟩).
  Next Obligation.
    intros; simpl.
    f_equiv.
    apply (snd (projT2 (bin_prod_ump (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) (X ×ₒ Y @ C)
                          (a₁ ∘ bin_proj_arr₁ X Y (X ×ₒ Y @ C))
                          (ı ∘ bin_proj_arr₂ X Y (X ×ₒ Y @ C))))).
    split.
    - rewrite H1.
      apply (proj1 (fst (projT2 (bin_prod_ump (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) (X ×ₒ Y @ C)
                                   (a₂ ∘ bin_proj_arr₁ X Y (X ×ₒ Y @ C))
                                   (ı ∘ bin_proj_arr₂ X Y (X ×ₒ Y @ C)))))).
    - rewrite <-(proj2 (fst (projT2 (bin_prod_ump (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) (X ×ₒ Y @ C)
                                      (a₂ ∘ bin_proj_arr₁ X Y (X ×ₒ Y @ C))
                                      (ı ∘ bin_proj_arr₂ X Y (X ×ₒ Y @ C)))))).
      now rewrite arrow_comp_id_l.
  Qed.

  Lemma CurryUnique
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    (f : X ×ₒ Y @ C [~>] Z)
    : Σ! (g : (X [~>] (Y ⇒ Z @ C))), f ≡ eval Z Y (Y ⇒ Z @ C) ∘ ⟨ g ×ₐ ı ⟩.
  Proof.
    exists (Curry f).
    split.
    - now rewrite <-(fst (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X f))).
    - intros x' H'.
      simpl.
      apply (snd (projT2 (exp_ump Z Y (Y ⇒ Z @ C) X f))).
      now rewrite H'.
  Defined.

  Lemma CurryUncurry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    (f : X [~>] (Y ⇒ Z @ C))
    : Curry (Uncurry f) ≡ f.
  Proof.
    unfold Curry, Uncurry; simpl.
    rewrite (snd (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) _ _))); [reflexivity |].
    f_equiv.
  Qed.

  Lemma UncurryCurry
    {C : Category}
    `{hasBinaryProducts C}
    `{hasExp C}
    {X Y Z : C}
    (f : X ×ₒ Y @ C [~>] Z)
    : Uncurry (Curry f) ≡ f.
  Proof.
    unfold Curry, Uncurry; simpl.
    rewrite (snd (projT2 (@bin_prod_ump _ (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) _ _ _))).
    - symmetry.
      apply (fst (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) X f))).
    - rewrite arrow_comp_id_l.
      split.
      + rewrite (snd (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) _ _)) (Curry f)).
        * simpl; now rewrite <-(proj1 (fst (projT2 (@bin_prod_ump C (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) _ _ _)))).
        * apply (fst (projT2 (CurryUnique f))).
      + rewrite (snd (projT2 (@exp_ump _ _ Z Y (Y ⇒ Z @ C) _ _)) (Curry f)).
        * simpl; rewrite <-(proj2 (fst (projT2 (@bin_prod_ump C (Y ⇒ Z @ C) Y ((Y ⇒ Z @ C) ×ₒ Y @ C) _ _ _)))).
          now rewrite arrow_comp_id_l.
        * apply (fst (projT2 (CurryUnique f))).
  Qed.

  Program Definition ExpUnique
    {C : Category}
    `{hasBinaryProducts C}
    (X Y : C) (a b : Exp X Y)
    : Isomorphism a b :=
    {|
      iso1 := (projT1 (@exp_ump _ _ X Y b a (@eval _ _ X Y a)));
      iso2 := (projT1 (@exp_ump _ _ X Y a b (@eval _ _ X Y b)));
    |}.
  Next Obligation.
    intros ? ? X Y a b.
    pose proof (fst (projT2 (@exp_ump _ _ X Y b a (@eval _ _ X Y a)))) as H'.
    rewrite (fst (projT2 (@exp_ump _ _ X Y a b (@eval _ _ X Y b)))) in H'.
    rewrite arrow_comp_assoc in H'.
    rewrite ArrBinProdComp in H'.
    rewrite arrow_comp_id_l in H'.
    rewrite <-(snd (projT2 (@exp_ump _ _ X Y a a (@eval _ _ X Y a))) _ H'); clear H'.
    apply (snd (projT2 (@exp_ump _ _ X Y a a (eval X Y a))) ı).
    simpl.
    rewrite (snd (projT2 (@bin_prod_ump C a Y (a ×ₒ Y @ C) _ _ _)));
      [symmetry; apply arrow_comp_id_r |].
    now rewrite !arrow_comp_id_l, !arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros ? ? X Y a b.
    pose proof (fst (projT2 (@exp_ump _ _ X Y a b (@eval _ _ X Y b)))) as H'.
    rewrite (fst (projT2 (@exp_ump _ _ X Y b a (@eval _ _ X Y a)))) in H'.
    rewrite arrow_comp_assoc in H'.
    rewrite ArrBinProdComp in H'.
    rewrite arrow_comp_id_l in H'.
    rewrite <-(snd (projT2 (@exp_ump _ _ X Y b b (@eval _ _ X Y b))) _ H'); clear H'.
    apply (snd (projT2 (@exp_ump _ _ X Y b b (eval X Y b))) ı).
    simpl.
    rewrite (snd (projT2 (@bin_prod_ump C b Y (b ×ₒ Y @ C) _ _ _)));
      [symmetry; apply arrow_comp_id_r |].
    now rewrite !arrow_comp_id_l, !arrow_comp_id_r.
  Qed.

End Aux.

Notation "'λ⟨' f '⟩'" := (Curry f) (at level 50) : cat_scope.
