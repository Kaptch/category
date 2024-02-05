From category Require Import
                      base
                      setoid
                      category
                      sets
                      terminal
                      functor
                      limit
                      prod
                      exp.

Section SetoidInst.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition TerminalSet : Terminal SetoidCat :=
    {|
      terminal_obj := [ unit ] : SetoidCat;
      terminal_proj X := existT _ (λₛ _, tt) _;
    |}.
  Next Obligation.
    now simpl.
  Qed.
  Next Obligation.
    econstructor.
    * constructor.
    * intros; simpl.
      intros ?; unfold const; simpl.
      now destruct (x' a).
  Qed.

  Program Definition constantSetFunc (D : Category) : (D) [⇒] SetoidCat
    := constantFunc (terminal_obj TerminalSet).

  Program Definition Setoid_limit (D : Category) (J : D [⇒] SetoidCat)
    : Cone J :=
    {|
      cone_obj := (@Arr (@FunCat D SetoidCat) (constantSetFunc D) J);
      cone_nat := λₙ X, (λₛ x, x X tt);
    |}.
  Next Obligation.
    intros; simpl.
    apply (H X).
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; unfold compose; simpl.
    rewrite <-(eta_comp a X Y f tt).
    simpl; unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition Setoid_limit_terminal_arr (D : Category)
    (J : D [⇒] SetoidCat) (X : Cone J) : ConeArr J X (Setoid_limit D J) :=
    {|
      cone_arr := (λₛ x, λₙ y, λₛ z, cone_nat X y x)
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros []; unfold compose; simpl.
    rewrite (@eta_comp _ _ _ _ (η cone_nat X) _ _ f x).
    simpl.
    unfold compose; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ? [].
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition Setoid_limit_terminal (D : Category) (J : D [⇒] SetoidCat)
    : Terminal (ConeCat J) :=
    {|
      terminal_obj := Setoid_limit D J;
      terminal_proj X := existT _ (Setoid_limit_terminal_arr D J X) _;
    |}.
  Next Obligation.
    intros; simpl.
    econstructor.
    * constructor.
    * intros; simpl.
      intros ? ? []; simpl.
      rewrite (@cone_comp _ _ J X (Setoid_limit D J) x').
      simpl.
      unfold compose; simpl.
      reflexivity.
  Qed.

  Program Definition Setoid_hasLimits {D : Category} (J : D [⇒] SetoidCat)
    : Limit J :=
  {|
    limit_obj := Setoid_limit_terminal D J;
  |}.

  Program Definition Setoid_hasBinProducts (J : bool -> SetoidCat) : Prod J :=
    {|
      prod_obj := (J true × J false)%setoid;
      proj_arr := λₙ x :: ⌊ bool ⌋,
        (λₛ H :: (J true × J false)%setoid,
          (if x as b return (J b)
           then fst H
           else snd H));
    |}.
  Next Obligation.
    intros ?? [? ?] [? ?] [? ?].
    simpl in *.
    destruct x; assumption.
  Qed.
  Next Obligation.
    intros ? ? ? f.
    destruct f.
    simpl.
    intros [? ?].
    unfold compose; simpl.
    destruct X; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    unshelve eexists (λₛ x, _).
    - apply (H true x, (H false x)).
    - intros; simpl.
      split; now f_equiv.
    - split.
      + intros [|] ?; simpl; unfold compose; simpl; reflexivity.
      + intros ? G; simpl; intros a; split;
          rewrite G; unfold compose; simpl; reflexivity.
  Defined.

  Program Definition SetoidArr_hasEval (X Y : SetoidCat)
    : isEval Setoid_hasBinProducts X Y (SetoidArr Y X) :=
    (λₛ x, fst x (snd x)).
  Next Obligation.
    intros; simpl.
    simpl in *.
    rewrite (fst H).
    now rewrite (snd H).
  Qed.

  Program Definition SetoidArr_ump (X Y : SetoidCat)
    : ∀ (Z' : SetoidCat) (eval' : isEval Setoid_hasBinProducts X Y Z'),
    Σ! f : (Z' [~>] (SetoidArr Y X)),
    eval' ≡
      (SetoidArr_hasEval X Y)
      ∘ ArrProd
      ((λ b : bool, if b then Z' else Y))
      ((λ b : bool, if b then (SetoidArr Y X) else Y))
      (bin_fun_prod Z' (SetoidArr Y X) Y f) _ _ :=
  λ Z' eval',
    existT
      _
      (λₛ z, λₛ y, eval' (z, y))
      _.
  Next Obligation.
    intros; simpl.
    f_equiv.
    split; [reflexivity | assumption].
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; f_equiv.
    split; [assumption | reflexivity].
  Qed.
  Next Obligation.
    intros.
    constructor.
    - simpl.
      intros; simpl.
      unfold compose; simpl.
      destruct a as [a1 a2]; simpl.
      reflexivity.
    - intros; simpl.
      intros ? ?; simpl.
      rewrite H.
      simpl.
      unfold compose; simpl.
      reflexivity.
  Qed.

  Program Definition Setoid_Exp (X Y : SetoidCat)
    : Exp Setoid_hasBinProducts X Y :=
    {|
      exp_obj := SetoidArr Y X;
      eval := SetoidArr_hasEval X Y;
      exp_ump := SetoidArr_ump X Y;
    |}.
End SetoidInst.
