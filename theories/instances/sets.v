From category Require Import
                      base
                      setoid
                      category
                      sets
                      terminal
                      initial
                      functor
                      limit
                      colimit
                      prod
                      exp
                      classes.limits
                      classes.colimits
                      classes.exp.

Section SetoidInst.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Lemma Setoid_mono_inj {X Y : SetoidCat} (f : @Monomorphism SetoidCat X Y)
    : ∀ x y, monic f x ≡ monic f y → x ≡ y.
  Proof.
    intros x y H.
    pose proof (@monic_cancel SetoidCat X Y f).
    pose (Z := [unit] : SetoidCat).
    unshelve epose (x' := (λₛ i :: Z, x) : Z [~>] X).
    { intros; reflexivity. }
    unshelve epose (y' := (λₛ i :: Z, y) : Z [~>] X).
    { intros; reflexivity. }
    simpl in *.
    assert (f ∘ x' ≡ f ∘ y') as H1.
    { intros ?; assumption. }
    pose proof (@monic_cancel SetoidCat X Y f Z x' y' H1) as H2.
    specialize (H2 tt).
    simpl in H2.
    apply H2.
  Qed.

  Program Definition Setoid_inj_mono {X Y : SetoidCat} (f : X [~>] Y)
    (H : (∀ x y, f x ≡ f y → x ≡ y))
    : Monomorphism X Y :=
    {|
      monic := f;
    |}.
  Next Obligation.
    intros ?? f H Z g₁ g₂ G z.
    specialize (G z).
    simpl in G.
    apply (H _ _ G).
  Qed.

  Program Definition TerminalSet : Terminal SetoidCat :=
    {|
      terminal_obj := [ unit ] : SetoidCat;
      terminal_proj X := existT (λₛ _, tt) _;
    |}.
  Next Obligation.
    now simpl.
  Qed.
  Next Obligation.
    econstructor.
    * constructor.
    * intros; simpl.
      intros ?.
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
    intros ?.
    rewrite <-(eta_comp a X Y f tt).
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
    rewrite (eta_comp (η cone_nat X) _ _ f x).
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
    reflexivity.
  Qed.

  Program Definition Setoid_limit_terminal (D : Category) (J : D [⇒] SetoidCat)
    : Terminal (ConeCat J) :=
    {|
      terminal_obj := Setoid_limit D J;
      terminal_proj X := existT (Setoid_limit_terminal_arr D J X) _;
    |}.
  Next Obligation.
    intros; simpl.
    econstructor.
    * constructor.
    * intros; simpl.
      intros ? ? []; simpl.
      rewrite (@cone_comp _ _ J X (Setoid_limit D J) x').
      reflexivity.
  Qed.

  Program Definition Setoid_hasLimits {D : Category} (J : D [⇒] SetoidCat)
    : Limit J :=
  {|
    limit_obj := Setoid_limit_terminal D J;
  |}.

  Program Definition Setoid_hasBinProducts (X Y : SetoidCat) : BinProd X Y :=
    {|
      bin_prod_obj := (X × Y)%setoid;
      bin_proj_arr₁ := (λₛ H :: (X × Y)%setoid, fst H);
      bin_proj_arr₂ := (λₛ H :: (X × Y)%setoid, snd H);
      bin_prod_ump := λ (p' : Setoid) (p₁ : p' [→] X) (p₂ : p' [→] Y),
        existT (λₛ x, ((p₁ x, p₂ x) : SetoidProd _ _)) _;
    |}.
  Next Obligation.
    intros ?? [? ?] [? ?] [? ?].
    simpl in *.
    assumption.
  Qed.
  Next Obligation.
    intros ? ? ? ? f.
    destruct f.
    simpl.
    assumption.
  Qed.
  Next Obligation.
    intros; simpl.
    split; now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    split.
    + split; intros ?; reflexivity.
    + intros ? [G1 G2]; simpl; intros a; split; [rewrite G1 | rewrite G2];
        reflexivity.
  Defined.

  Global Instance Setoid_hasBinProductsInst : hasBinaryProducts SetoidCat.
  Proof.
    constructor.
    intros.
    apply Setoid_hasBinProducts.
  Defined.

  Program Definition SetoidArr_eval (X Y : SetoidCat)
    : ((SetoidArr Y X) ×ₒ Y @ SetoidCat) [~>] X :=
    (λₛ x, fst x (snd x)).
  Next Obligation.
    intros; simpl.
    simpl in *.
    rewrite (fst H).
    now rewrite (snd H).
  Qed.

  Program Definition SetoidArr_ump (X Y : SetoidCat)
    : ∀ (Z' : SetoidCat) (eval' : Z' ×ₒ Y @ SetoidCat [~>] X),
    Σ! f : (Z' [~>] (SetoidArr Y X)),
    eval' ≡
      (SetoidArr_eval X Y)
      ∘ ⟨ f ×ₐ ı ⟩ :=
  λ Z' eval',
    existT
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
      destruct a as [a1 a2]; simpl.
      reflexivity.
    - intros; simpl.
      intros ? ?; simpl.
      rewrite H.
      reflexivity.
  Qed.

  Program Definition Setoid_Exp (X Y : SetoidCat)
    : Exp X Y :=
    {|
      exp_obj := SetoidArr Y X;
      eval := SetoidArr_eval X Y;
      exp_ump := SetoidArr_ump X Y;
    |}.

  Global Instance Setoid_hasExpInst : hasExp SetoidCat.
  Proof.
    constructor.
    intros.
    apply Setoid_Exp.
  Defined.

  Global Instance Setoid_hasLimitsInst : hasLimits SetoidCat.
  Proof.
    constructor.
    intros.
    apply Setoid_hasLimits.
  Defined.

  Definition Setoid_colimit_rel' (D : Category) (J : D [⇒] SetoidCat)
    : (sigT (FO J)) → (sigT (FO J)) → Prop :=
    λ X Y, (exists (ϕ : projT1 X [~>] projT1 Y), fmap J ϕ (projT2 X) ≡ (projT2 Y)).

  Definition Setoid_colimit_rel (D : Category) (J : D [⇒] SetoidCat)
    : (sigT (FO J)) → (sigT (FO J)) → Prop :=
    Relation_Operators.clos_refl_sym_trans _ (Setoid_colimit_rel' D J).

  Lemma Setoid_colimit_rel_equiv (D : Category) (J : D [⇒] SetoidCat)
    : Equivalence (Setoid_colimit_rel D J).
  Proof.
    pose proof (Operators_Properties.clos_rst_is_equiv _ (Setoid_colimit_rel' D J)) as [H1 H2 H3].
    split.
    - apply H1.
    - apply H3.
    - apply H2.
  Qed.

  Program Definition Setoid_colimit_obj (D : Category) (J : D [⇒] SetoidCat) : SetoidCat
    :=
    {|
      setoid_carrier := (sigT (FO J));
      setoid_eq X Y := Setoid_colimit_rel D J X Y;
      setoid_equiv := Setoid_colimit_rel_equiv D J;
    |}.

  Program Definition Setoid_colimit_cocone (D : Category) (J : D [⇒] SetoidCat) : Cocone J
    :=
    {|
      cocone_obj := Setoid_colimit_obj D J;
      cocone_nat := λₙ x, λₛ s, existT x s;
    |}.
  Next Obligation.
    intros; simpl.
    apply Relation_Operators.rst_step.
    unfold Setoid_colimit_rel'.
    simpl.
    exists ı.
    rewrite H.
    apply (@fmap_id _ _ J x).
  Qed.
  Next Obligation.
    intros; simpl.
    intros a.
    unfold compose, id; simpl.
    apply (Setoid_colimit_rel_equiv D J).
    constructor.
    unfold Setoid_colimit_rel'.
    simpl.
    exists f.
    reflexivity.
  Qed.

  Program Definition Setoid_colimit_cocone_initial_arr
    (D : Category) (J : D [⇒] SetoidCat) (X : CoconeCat J) : (@Arr (@CoconeCat D SetoidCat J) (Setoid_colimit_cocone D J) X)
    :=
    {|
      cocone_arr := λₛ x, (@cocone_nat D SetoidCat J X (projT1 x) (projT2 x));
    |}.
  Next Obligation.
    intros D J X a₁ a₂ H.
    simpl in *.
    induction H.
    - destruct x, y.
      destruct H as [ϕ <-].
      simpl in *.
      rewrite ->(eta_comp (cocone_nat X) _ _ ϕ s).
      reflexivity.
    - reflexivity.
    - rewrite IHclos_refl_sym_trans.
      reflexivity.
    - rewrite IHclos_refl_sym_trans1.
      rewrite IHclos_refl_sym_trans2.
      reflexivity.
  Qed.
  Next Obligation.
    intros j; simpl.
    intros a.
    unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition Setoid_colimit_cocone_initial (D : Category) (J : D [⇒] SetoidCat) : Initial (CoconeCat J)
    :=
    {|
      initial_obj := Setoid_colimit_cocone D J;
      initial_proj X := existT (Setoid_colimit_cocone_initial_arr D J X) _;
    |}.
  Next Obligation.
    intros D J X.
    split; [constructor |].
    intros x' _.
    simpl.
    intros [x Jx]; simpl.
    rewrite <-(@cocone_comp D SetoidCat J _ _ x' x Jx).
    simpl; unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition Setoid_hasColimits {D : Category} (J : D [⇒] SetoidCat)
    : Colimit J :=
    {|
      colimit_obj := Setoid_colimit_cocone_initial D J;
    |}.

  Global Instance Setoid_hasColimitsInst : hasColimits SetoidCat.
  Proof.
    constructor.
    intros.
    apply Setoid_hasColimits.
  Defined.

End SetoidInst.
