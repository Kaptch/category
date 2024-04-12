From category Require Import
  base
  setoid
  category
  sets
  initial
  terminal
  functor
  limit
  colimit
  prod
  exp
  hom
  pullback
  subobject
  classes.limits
  classes.colimits
  classes.exp
  classes.subobject
  classes.enrichment
  instances.sets.

Definition PSh (C : Category) : Category := FunCat (C op)%cat SetoidCat.

Section PSh_exp.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {Obj : Category}.

  Class FComp {X Y : PSh Obj} {A} (K : ∀ {B}, (Arr A B : SetoidCat) [~>] X B [~>] Y B) :=
    comp_fmap : ∀ {B C} (δ₂ : Arr B C) (δ₁ : Arr A B) (v : X B),
        K (δ₂ ∘ δ₁) (fmap X δ₂ v) ≡ fmap Y δ₂ (K δ₁ v).

  Record RemFun (X Y : PSh Obj) (A : Obj op) :=
    { arr :> ∀ B, (Arr A B : SetoidCat) [~>] X B [~>] Y B;
      (* arr_ext {B : Obj op} *)
      (* : Proper (setoid_eq ==> setoid_eq ==> setoid_eq) (@arr B); *)
      arr_fmap : FComp (@arr)
    }.
  Arguments arr {X Y A} _ B.

  (* Global Instance RF_prop {X Y : PSh Obj} {A} {RF : RemFun X Y A} {B} : *)
  (*   Proper (setoid_eq ==> setoid_eq ==> setoid_eq) (RF B) := *)
  (*   arr_ext _ _ _ RF. *)

  Global Instance RF_FComp {X Y : PSh Obj} {A} {RF : RemFun X Y A} :
    FComp RF := arr_fmap _ _ _ RF.

  Definition RemFun_eq {X Y : PSh Obj}
    : ∀ {A}, (RemFun X Y A) → (RemFun X Y A) → Prop :=
    λ {A} φ₁ φ₂, ∀ {B} (δ : Arr A B) v, φ₁ _ δ v ≡ φ₂ _ δ v.

  Global Instance RemFun_equiv {X Y : PSh Obj}
    : ∀ {A}, Equivalence (@RemFun_eq X Y A).
  Proof.
    split.
    - intros φ B δ v; reflexivity.
    - intros φ₁ φ₂ EQφ B δ v; symmetry; apply EQφ.
    - intros φ₁ φ₂ φ₃ EQφ₁ EQφ₂ B δ v; etransitivity; [apply EQφ₁ | apply EQφ₂].
  Qed.

  Program Definition RemFun_setoid (X Y : PSh Obj) (A : Obj op) : Setoid :=
    {|
      setoid_carrier := RemFun X Y A;
      setoid_eq := RemFun_eq;
      setoid_equiv := RemFun_equiv;
    |}.

  Program Definition RemFun_fmap {X Y : PSh Obj}
    : ∀ {A B}, (Arr A B) → (RemFun X Y) A → (RemFun X Y) B :=
  λ {A B} δ φ, {| arr C := λₛ δ', λₛ v, φ C (δ' ∘ δ) v |}.
  Next Obligation.
    intros; simpl.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; now rewrite H.
  Qed.
  Next Obligation.
    unfold FComp; intros; simpl; rewrite <-arrow_comp_assoc; apply arr_fmap.
  Qed.

  Program Definition PArr (X Y : PSh Obj) : PSh Obj :=
    {| FO A := RemFun_setoid X Y A;
       fmap A B := (λₛ f, λₛ (x : RemFun_setoid X Y A), RemFun_fmap f x);
    |}.
  Next Obligation.
    intros; simpl.
    intros ? ? ?; simpl.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    intros ? ? ?; simpl.
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    intros ???; simpl.
    rewrite arrow_comp_id_l.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    intros ???; simpl.
    rewrite arrow_comp_assoc.
    reflexivity.
  Qed.
End PSh_exp.

Notation "'λₖ' Γ , e" :=
  {| arr Γ := e;
    (* arr_ext := _; *)
    arr_fmap := _
  |} (at level 120, Γ binder, no associativity)
    : functor_scope.

Section PSh_inst.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Program Definition PSh_hasBinProducts {C} (A B : PSh C) : @BinProd (PSh C) A B :=
    {|
      bin_prod_obj :=
        {|
          FO X := (A X × B X)%setoid;
          fmap A' B' := λₛ f :: @Arr C B' A',
            λₛ g,
            (fmap A f (fst g)
              , fmap B f (snd g));
        |};
      bin_proj_arr₁ := λₙ x, λₛ y, fst y;
      bin_proj_arr₂ := λₙ x, λₛ y, snd y;
    |}.
  Next Obligation.
    intros; simpl.
    split; f_equiv; apply H.
  Defined.
  Next Obligation.
    intros; simpl.
    intros [? ?]; simpl.
    now split; f_equiv; rewrite H.
  Defined.
  Next Obligation.
    intros; simpl.
    intros [? ?]; simpl.
    split.
    - apply (@fmap_id (C op) SetoidCat A A0 s).
    - apply (@fmap_id (C op) SetoidCat B A0 s0).
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?]; simpl.
    split.
    - apply (@fmap_comp (C op) SetoidCat A).
    - apply (@fmap_comp (C op) SetoidCat B).
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros [? ?]; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros [Q1 Q2]; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    unshelve econstructor.
    - unshelve econstructor.
      + intros; simpl.
        unshelve econstructor.
        * intros; simpl.
          apply ((p₁ X X0), (p₂ X X0)).
        * intros; simpl.
          split; now rewrite H.
      + intros; simpl.
        intros; simpl.
        split.
        * apply (eta_comp (η p₁) _ _ f a).
        * apply (eta_comp (η p₂) _ _ f a).
    - split.
      + intros; split; reflexivity.
      + intros; simpl.
        intros; simpl.
        split.
        * rewrite (proj1 H).
          reflexivity.
        * rewrite (proj2 H).
          reflexivity.
  Defined.

  Global Instance PSh_hasBinProductsInst {C} : hasBinaryProducts (PSh C).
  Proof.
    constructor.
    intros.
    apply PSh_hasBinProducts.
  Defined.

  Program Definition PArr_eval {C} (X Y : PSh C)
    : (PArr Y X) ×ₒ Y @ (PSh C) [~>] X  :=
    λₙ x, λₛ y, (fst y x ı (snd y)).
  Next Obligation.
    intros ???? [? ?] [? ?] [? ?]; simpl in *.
    rewrite (s3 x ı).
    now rewrite s4.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?]; unfold compose; simpl.
    rewrite arrow_comp_id_r.
    rewrite <-(@arr_fmap C Y X X0 r X0 Y0 f ı).
    f_equiv; last done.
    now rewrite ->arrow_comp_id_r.
  Qed.

  Program Definition PArr_ump {C} (X Y : PSh C) :
    ∀ (Z' : PSh C) (eval' : Z' ×ₒ Y @ (PSh C) [~>] X),
    Σ! f : (Z' [~>] (PArr Y X)),
    eval' ≡
      (PArr_eval X Y)
      ∘ ⟨ f ×ₐ ı ⟩ :=
  λ Z' eval',
    existT
      (λₙ x, λₛ y, λₖ Γ, λₛ δ, λₛ μ, (eval' Γ ((fmap Z' δ y), μ)))
      _.
  Next Obligation.
    intros; simpl.
    f_equiv.
    now split.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    f_equiv.
    split; simpl; [now rewrite H | reflexivity].
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?????.
    pose proof (eta_comp eval' _ _ δ₂) as H.
    simpl in H.
    unfold compose in H.
    simpl.
    rewrite <-H.
    f_equiv.
    split.
    - apply (@fmap_comp _ _ Z' _ _ _ δ₂ δ₁ y).
    - reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???; simpl.
    f_equiv; split; simpl; [| reflexivity].
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    intros ???; simpl.
    f_equiv.
    split; [| reflexivity].
    symmetry.
    apply (@fmap_comp _ _ Z' _ _ _ δ f a).
  Qed.
  Next Obligation.
    intros; simpl.
    split.
    - intros ? [? ?]; simpl.
      unfold compose; simpl.
      f_equiv.
      split; [| reflexivity].
      simpl.
      rewrite (@fmap_id _ _ Z' X0 s).
      reflexivity.
    - intros; simpl.
      intros ?????; simpl.
      specialize (H B).
      rewrite H.
      rewrite (eta_comp x' X0 B δ a B ı v).
      simpl.
      now rewrite arrow_comp_id_r.
  Qed.

  Program Definition PSh_Exp {C} (X Y : PSh C)
    : Exp X Y :=
    {|
      exp_obj := PArr Y X;
      eval := PArr_eval X Y;
      exp_ump := PArr_ump X Y;
    |}.

  Global Instance PSh_ExpInst {C} : hasExp (PSh C).
  Proof.
    constructor.
    intros.
    apply PSh_Exp.
  Defined.

  Program Definition PSh_limit_pointwise {C} (D : Category)
    (J : D [⇒] (PSh C)) (c : C op) : D [⇒] SetoidCat :=
    {|
      FO d := J d c;
      fmap A B := (λₛ x, (λₛ y, ((η (fmap J x)) c y)));
    |}.
  Next Obligation.
    intros; simpl.
    now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    apply (setoid_arr_eq (Arr A B) (Arr (J A) (J B)) (fmap J) _ _ H c a).
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?; simpl.
    etransitivity; [apply (@fmap_id _ _ J) |].
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    rewrite (@fmap_comp D (PSh C) J _ _ _ f g c a).
    reflexivity.
  Qed.

  Program Definition PSh_colimit {C} (D : Category) (J : D [⇒] (PSh C)) : PSh C :=
    {|
      FO c := colim (PSh_limit_pointwise D J c) @ SetoidCat;
      fmap A B := λₛ f, λₛ g, existT (projT1 g) (fmap (J (projT1 g)) f (projT2 g));
    |}.
  Next Obligation.
    intros; simpl.
    induction H.
    - destruct H as [g H].
      constructor.
      exists g.
      simpl.
      rewrite <-H.
      simpl.
      rewrite <-(eta_comp (fmap J g) _ _ f (projT2 x)).
      reflexivity.
    - constructor.
      exists ı.
      simpl.
      rewrite (@fmap_id _ _ J (projT1 x) B).
      reflexivity.
    - apply Setoid_colimit_rel_equiv.
      apply IHclos_refl_sym_trans.
    - eapply (@Equivalence_Transitive _ _ (Setoid_colimit_rel_equiv D (PSh_limit_pointwise D J B))).
      + apply IHclos_refl_sym_trans1.
      + apply IHclos_refl_sym_trans2.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?].
    simpl.
    constructor.
    unfold Setoid_colimit_rel'.
    simpl.
    exists ı.
    rewrite H.
    rewrite (@fmap_id _ _ J x B).
    simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?].
    simpl.
    constructor.
    unfold Setoid_colimit_rel'.
    simpl.
    exists ı.
    rewrite (@fmap_id _ _ J x A).
    simpl.
    apply (@fmap_id _ _ (J x) A s).
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?].
    simpl.
    constructor.
    unfold Setoid_colimit_rel'.
    simpl.
    exists ı.
    rewrite (@fmap_id _ _ J x C0).
    simpl.
    apply (@fmap_comp _ _ (J x) A).
  Qed.

  Program Definition PSh_colimit_cocone {C} (D : Category) (J : D [⇒] (PSh C))
    : CoconeCat J :=
    {|
      cocone_obj := PSh_colimit D J;
      cocone_nat := λₙ t, λₙ a, λₛ b, existT t b;
    |}.
  Next Obligation.
    intros; simpl.
    constructor.
    unfold Setoid_colimit_rel'; simpl.
    exists ı.
    rewrite (@fmap_id _ _ J t a).
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    apply Setoid_colimit_rel_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    unfold id; simpl.
    apply Setoid_colimit_rel_equiv.
    constructor.
    unfold Setoid_colimit_rel'; simpl.
    exists f.
    reflexivity.
  Qed.

  Program Definition PSh_colimit_cocone_initial_arr' {C} (D : Category)
    (J : D [⇒] (PSh C)) (X : CoconeCat J) : (PSh_colimit D J) [~>] X
    := λₙ x, λₛ s, (cocone_nat X (projT1 s) x (projT2 s)).
  Next Obligation.
    intros; simpl.
    simpl in *.
    induction H.
    - destruct x0, y.
      destruct H as [ϕ H].
      simpl in *.
      rewrite <-H.
      rewrite ->(eta_comp (η cocone_nat X) _ _ ϕ x s).
      reflexivity.
    - reflexivity.
    - rewrite IHclos_refl_sym_trans.
      reflexivity.
    - rewrite IHclos_refl_sym_trans1.
      rewrite IHclos_refl_sym_trans2.
      reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?]; unfold compose; simpl.
    rewrite ->(eta_comp (η (η cocone_nat X) x) _ _ f s).
    reflexivity.
  Qed.

  Program Definition PSh_colimit_cocone_initial_arr {C} (D : Category)
    (J : D [⇒] (PSh C)) (X : CoconeCat J) : (PSh_colimit_cocone D J) [~>] X
    :=
    {|
      cocone_arr := PSh_colimit_cocone_initial_arr' D J X;
    |}.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_colimit_cocone_initial {C} (D : Category)
    (J : D [⇒] (PSh C))
    : Initial (CoconeCat J) :=
    {|
      initial_obj := PSh_colimit_cocone D J;
      initial_proj X := existT (PSh_colimit_cocone_initial_arr D J X) _;
    |}.
  Next Obligation.
    intros; simpl.
    split; [constructor |].
    intros x' _.
    intros; simpl.
    intros ? [x Jx]; simpl.
    rewrite <-(@cocone_comp D (PSh C) J _ _ x' x X0 Jx).
    reflexivity.
  Qed.

  Program Definition PSh_hasColimits {C} {D : Category}
    (J : D [⇒] (PSh C)) : Colimit J :=
    {|
      colimit_obj := PSh_colimit_cocone_initial D J;
    |}.

  Global Instance PSh_hasColimitsInst {C} : hasColimits (PSh C).
  Proof.
    constructor.
    intros.
    apply PSh_hasColimits.
  Defined.

  Program Definition PSh_limit {C} (D : Category) (J : D [⇒] (PSh C)) : PSh C :=
    {|
      FO c := NatTransSetoid _ _ (constantSetFunc D) (PSh_limit_pointwise D J c);
      fmap A B := λₛ x :: @Arr C B A,
        λₛ X :: NatTransSetoid _ _ (constantSetFunc D) (PSh_limit_pointwise D J A),
        λₙ y :: D, (λₛ T, (fmap (J y) x (X y tt)));
      (* wtf??? *)
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros []; unfold compose; simpl.
    epose proof (@eta_comp (C op) SetoidCat _ (J Y) _ A B x) as H'.
    simpl in H'.
    unfold compose in H'.
    simpl in H'.
    rewrite H'.
    f_equiv.
    apply (eta_comp X _ _ f tt).
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    f_equiv.
    apply (H X).
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    f_equiv.
    now rewrite H.
  Qed.
  Next Obligation.
    simpl.
    intros ?; simpl.
    intros ?; simpl.
    intros ? ?; simpl.
    intros ? ? []; simpl.
    rewrite (@fmap_id (C op) SetoidCat (J _) A (_ _ tt)).
    reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros ? ? ? ? ? ? ? ? ? ? []; simpl.
    rewrite (@fmap_comp (C op) SetoidCat (J X) _ _ _ f g (a X tt)).
    reflexivity.
  Qed.

  Program Definition PSh_limit_cone {C} (D : Category) (J : D [⇒] (PSh C))
    : Cone J :=
    {|
      cone_obj := PSh_limit D J;
      cone_nat := λₙ t, λₙ a, λₛ b, (b t tt);
    |}.
  Next Obligation.
    intros; simpl.
    apply (H _).
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    unfold compose; simpl.
    apply (eta_comp a X Y f tt).
  Qed.

  Program Definition PSh_limit_cone_terminal_arr {C} (D : Category)
    (J : D [⇒] (PSh C)) (X : ConeCat J) : X [~>] PSh_limit_cone D J :=
    {|
      cone_arr := λₙ a, λₛ b, λₙ c, λₛ d, cone_nat X c a b
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    simpl in *.
    rewrite (eta_comp (η cone_nat X) _ _ f a b).
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    rewrite H.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; simpl.
    rewrite ->(eta_comp (η (η cone_nat X) X1) _ _ f a).
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros; unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_limit_cone_terminal {C} (D : Category)
    (J : D [⇒] (PSh C))
    : Terminal (ConeCat J) :=
    {|
      terminal_obj := PSh_limit_cone D J;
      terminal_proj X :=
        existT (PSh_limit_cone_terminal_arr D J X) _;
    |}.
  Next Obligation.
    intros; simpl.
    constructor.
    * constructor.
    * intros; simpl.
      intros; simpl.
      rewrite (@cone_comp D (PSh C) J _ _ x' X1 X0 a).
      simpl.
      unfold compose; simpl.
      destruct a0.
      reflexivity.
  Qed.

  Program Definition PSh_hasLimits {C} {D : Category}
    (J : D [⇒] (PSh C)) : Limit J :=
    {|
      limit_obj := PSh_limit_cone_terminal D J;
    |}.

  Global Instance PSh_hasLimitsInst {C} : hasLimits (PSh C).
  Proof.
    constructor.
    intros.
    apply PSh_hasLimits.
  Defined.

  Program Definition Point {C : Category} {i : C}
    : (𝟙 @ (PSh C)) i.
  Proof.
    unshelve econstructor.
    - intros [].
    - intros [].
  Qed.

  Lemma PointUnique {C : Category} {i : C} (γ : (𝟙 @ (PSh C)) i)
    : γ ≡ Point.
  Proof.
    intros [].
  Qed.

  Program Definition PSh_initial {C : Category} :
    Initial (PSh C) :=
    {|
      initial_obj := {|
                      FO _ := [Empty_set];
                      fmap A B := λₛ _, idS
                    |}
    |}.
  Next Obligation.
    intros; simpl; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl; intros [].
  Qed.
  Next Obligation.
    intros; simpl.
    unshelve eexists.
    - unshelve econstructor.
      + intros; simpl.
        unshelve econstructor.
        * intros [].
        * intros [].
      + intros; simpl.
        intros [].
    - split.
      + constructor.
      + intros; simpl.
        intros ? [].
  Qed.

  Global Instance PSh_hasInitial {C : Category} :
    hasInitial (PSh C) := {| has_initial := PSh_initial |}.

End PSh_inst.

Section Sieves.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Context {C : Category}.
  Context (c : C).

  Record Sieve := {
      sieve_arrows :> ∀ {d : C}, Arr d c [→] PropSetoid;
      sieve_closed : ∀ {d e : C} (f : Arr d c) (g : Arr e d),
        sieve_arrows f → sieve_arrows (f ∘ g);
    }.

  Program Definition SieveSetoid : Setoid :=
    {|
      setoid_carrier := Sieve;
      setoid_eq A B := ∀ {d} (f : Arr d c), sieve_arrows A f ≡ sieve_arrows B f;
    |}.
  Next Obligation.
    split.
    - intros ? ??.
      reflexivity.
    - intros ?? H ??.
      symmetry.
      apply H.
    - intros ??? H H' ??.
      etransitivity.
      + apply H.
      + apply H'.
  Qed.

  Program Definition TotalSieve : SieveSetoid :=
    {|
      sieve_arrows d := λₛ f, True;
    |}.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    constructor.
  Qed.

End Sieves.

Arguments Sieve {_}.
Arguments TotalSieve {_ _}.
Arguments SieveSetoid {_}.
Arguments sieve_arrows {_ _ _ _}.
Arguments sieve_closed {_ _ _ _ _}.

Notation "'λᵢ' δ , e" :=
  {|
    sieve_arrows δ := e;
    sieve_closed := _
  |} (at level 120, δ binder, no associativity)
    : cat_scope.

Section SievesPSh.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.

  Lemma PSh_mono_pointwise {X Y : PSh C} (f : X [⤷] Y) :
    ∀ (x : C op) (D : SetoidCat) (y z : D [→] (X x)), (monic f x) ∘ y ≡ (monic f x) ∘ z → y ≡ z.
  Proof.
    intros x D y z H t.
    simpl in H.
    unshelve epose (T := {|
                          FO (i : C op) := (@Arr C i x : SetoidCat);
                          fmap A B := λₛ g :: @Arr C B A, _;
                        |} : PSh C).
    {
      refine (λₛ h :: @Arr C A x, h ∘ g).
      intros; simpl; now do 2 f_equiv.
    }
    {
      intros; simpl.
      intros ?; now f_equiv.
    }
    {
      intros; simpl.
      intros ?; now rewrite arrow_comp_id_r.
    }
    {
      intros; simpl.
      intros ?; unfold compose; simpl.
      symmetry.
      apply arrow_comp_assoc.
    }
    simpl in T.
    unshelve epose (g₁' := (λₙ U :: C op, (λₛ g :: T U, (fmap X g (y t))) : T U [~>] X U) : T [↣] X).
    {
      intros ?? G; simpl.
      now rewrite G.
    }
    {
      intros ? ? h; simpl.
      intros a; unfold compose; simpl.
      apply (@fmap_comp (C op) SetoidCat X _ _ _ h a (y t)).
    }
    unshelve epose (g₂' := (λₙ U :: C op, (λₛ g :: T U, (fmap X g (z t))) : T U [~>] X U) : T [↣] X).
    {
      intros ?? G; simpl.
      now rewrite G.
    }
    {
      intros ? ? h; simpl.
      intros a; unfold compose; simpl.
      apply (@fmap_comp (C op) SetoidCat X _ _ _ h a (z t)).
    }
    pose proof (@monic_cancel (PSh C) X Y f T g₁' g₂') as G.
    subst T g₁' g₂'.
    simpl in *.
    unfold compose in *.
    assert (∀ (X0 : C) (a : X0 [~>] x), (η (monic f)) X0 (fmap X a (y t)) ≡ (η (monic f)) X0 (fmap X a (z t))) as G'.
    {
      intros ? a; simpl.
      rewrite ->(@eta_comp _ _ _ _ (monic f) _ _ a (y t)).
      rewrite ->(@eta_comp _ _ _ _ (monic f) _ _ a (z t)).
      simpl.
      unfold compose; simpl.
      f_equiv.
      apply H.
    }
    specialize (G G' x ı).
    rewrite (@fmap_id _ _ X _ (y t)) in G.
    rewrite (@fmap_id _ _ X _ (z t)) in G.
    apply G.
  Qed.

  Program Definition PSh_sieve : PSh C :=
    {|
      FO x := @SieveSetoid C x;
      fmap A B := λₛ f :: @Arr C B A, λₛ s, λᵢ a, λₛ b, (s _ (f ∘ b));
    |}.
  Next Obligation.
    intros; simpl.
    split.
    - intros.
      simpl in *.
      rewrite <-(setoid_arr_eq _ _ (s a) (f ∘ a₁) (f ∘ a₂)); [assumption |].
      now f_equiv.
    - intros.
      simpl in *.
      rewrite (setoid_arr_eq _ _ (s a) (f ∘ a₁) (f ∘ a₂)); [assumption |].
      now f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    simpl in *.
    rewrite (setoid_arr_eq _ _ (s e) (f ∘ (f0 ∘ g)) (f ∘ f0 ∘ g)).
    - now apply sieve_closed.
    - symmetry; apply arrow_comp_assoc.
  Qed.
  Next Obligation.
    intros; simpl.
    intros d g.
    apply (H d).
  Qed.
  Next Obligation.
    intros; simpl.
    intros a d f.
    now do 3 f_equiv.
  Qed.
  Next Obligation.
    intros; simpl.
    intros a; simpl.
    intros d f.
    unfold id.
    f_equiv.
    apply arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    intros a d h; simpl.
    f_equiv.
    apply arrow_comp_assoc.
  Qed.

  Program Definition PSh_true_arr
    : 𝟙 @ (PSh C) [~>] PSh_sieve
    := λₙ _, λₛ _, TotalSieve.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_true_arr_mono
    : 𝟙 @ (PSh C) [⤷] PSh_sieve :=
    {|
      monic := PSh_true_arr;
    |}.
  Next Obligation.
    intros; simpl.
    intros X ? [] [].
  Qed.

  Program Definition PSh_char {X Y : PSh C} (f : X [⤷] Y) : Y [~>] PSh_sieve :=
    λₙ c, λₛ x, λᵢ d, λₛ α, ∃ u : X d, (monic f d) u ≡ fmap Y α x.
  Next Obligation.
    intros; simpl.
    split; intros [u G]; exists u.
    - now rewrite <-H.
    - now rewrite H.
  Qed.
  Next Obligation.
    intros ??????? h g; simpl.
    intros [u G].
    exists (fmap X g u).
    pose proof (eta_comp (monic f) _ _ g u) as H.
    simpl in H.
    unfold compose in H.
    rewrite H; clear H.
    pose proof (@fmap_comp _ _ Y _ _ _ g h x) as J.
    simpl in J.
    rewrite J; clear J.
    unfold compose; simpl.
    f_equiv.
    apply G.
  Qed.
  Next Obligation.
    intros; simpl in *.
    intros d g.
    split; intros [u G]; exists u.
    - now rewrite <-H.
    - now rewrite H.
  Qed.
  Next Obligation.
    intros ????? h; simpl.
    intros a d g; split; intros [u G].
    - exists u.
      rewrite G.
      symmetry; apply (@fmap_comp _ _ Y _ _ _ g h a).
    - exists u.
      rewrite G.
      apply (@fmap_comp _ _ Y _ _ _ g h a).
  Qed.

  Local Axiom ID_epsilon :
    ∀ T : Type, ConstructiveIndefiniteDescription_on T.

  Lemma char_Pb {X Y : PSh C} (f : X [⤷] Y)
    : isPullback (PSh_char f)
        (PSh_true_arr_mono)
        f
        (! @ (PSh C)).
  Proof.
    unshelve econstructor.
    - unshelve econstructor.
      intros x.
      simpl.
      intros a d f'; simpl.
      split; [constructor |].
      intros _.
      exists (fmap X f' a).
      pose proof (eta_comp (monic f) _ _ f' a) as H.
      simpl in H; unfold compose in H; simpl in H.
      apply H.
    - intros.
      unshelve eexists (λₙ x, _).
      + unshelve eexists.
        * intros w; simpl.
          pose proof (proj2 (CS_comm h j H x w x ı) I) as J.
          simpl in J.
          destruct (ID_epsilon _ _ J) as [J' _].
          apply J'.
        * intros; simpl.
          destruct (ID_epsilon (X x)) as [X1 s].
          destruct (ID_epsilon (X x)) as [X2 s0].
          rewrite (@fmap_id _ _ Y x ((η h) x a₂)) in s0.
          rewrite (@fmap_id _ _ Y x ((η h) x a₁)) in s.
          simpl in *.
          unfold id in *.
          simpl in *.
          assert ((monic f) x X1 ≡ (monic f) x X2) as H1.
          {
            rewrite s s0.
            rewrite H0.
            reflexivity.
          }
          unshelve epose proof (PSh_mono_pointwise f x (𝟙 @ SetoidCat) (λₛ i, X1) (λₛ i, X2)) as H2.
          { intros; reflexivity. }
          { intros; reflexivity. }
          simpl in H2.
          unfold compose in H2.
          apply H2.
          -- intros ?; assumption.
          -- unshelve eapply (λₙ i :: ⌊ Empty_set ⌋, match i with end).
             intros [].
      + intros ?? f'; simpl.
        intros a; simpl.
        unfold compose; simpl.
        destruct (ID_epsilon _) as [X1 s].
        destruct (ID_epsilon _) as [X2 s0].
        rewrite (@fmap_id _ _ Y _ ((η h) _ a)) in s0.
        rewrite (@fmap_id _ _ Y _ ((η h) _ (fmap W f' a))) in s.
        simpl in *.
        unfold id in *.
        simpl in *.
        rewrite ->(@eta_comp _ _ _ _ h _ _ f' a) in s.
        simpl in *.
        unfold compose in *; simpl in *.
        rewrite <-s0 in s; clear s0.
        rewrite <-(@eta_comp _ _ _ _ (monic f) _ _ f' X2) in s.
        simpl in *.
        unfold compose in *; simpl in *.
        unshelve epose proof (PSh_mono_pointwise f _ (𝟙 @ SetoidCat) (λₛ i, X1) (λₛ i, fmap X f' X2)) as H2.
        { intros; reflexivity. }
        { intros; reflexivity. }
        simpl in H2.
        unfold compose in H2.
        apply H2.
        -- intros ?; assumption.
        -- unshelve eapply (λₙ i :: ⌊ Empty_set ⌋, match i with end).
           intros [].
      + split.
        * split.
          -- intros x a; simpl.
             unfold compose; simpl.
             destruct (ID_epsilon (X x)) as [X1 ?].
             rewrite (@fmap_id _ _ Y _ ((η h) x a)) in s.
             simpl in s.
             symmetry.
             apply s.
          -- intros x a; simpl.
             intros [].
        * intros x' [G1 G2].
          simpl.
          intros T a.
          destruct (ID_epsilon (X T)) as [X1 ?].
          rewrite (@fmap_id _ _ Y _ ((η h) T a)) in s.
          simpl in s.
          unfold id in s.
          simpl in s.
          assert ((η (monic f)) T X1 ≡ (η ((monic f) ∘ x')) T a) as H1.
          {
            rewrite s.
            apply G1.
          }
          simpl in H1.
          unfold compose in H1.
          unshelve epose proof (PSh_mono_pointwise f T (𝟙 @ SetoidCat) (λₛ i, X1) (λₛ i, ((η x') T a))) as H2.
          { intros; reflexivity. }
          { intros; reflexivity. }
          simpl in H2.
          apply H2.
          -- intros ?; simpl; unfold compose; simpl; assumption.
          -- unshelve eapply (λₙ i :: ⌊ Empty_set ⌋, match i with end).
             intros [].
  Qed.

  Lemma PSh_char_unique {Q P : PSh C} (g : Q [⤷] P)
    : unique_setoid (λ char : P [~>] PSh_sieve, isPullback char PSh_true_arr_mono g (! @ PSh C)) (PSh_char g).
  Proof.
    split.
    - apply char_Pb.
    - intros Θ H.
      intros d x c f.
      simpl.
      split.
      + intros [H1 H2].
        pose proof (proj2 (CS_comm _ _ (is_pb _ _ _ H) c H1 c ı) I) as KKK.
        simpl in KKK.
        unfold compose in KKK.
        assert (KKK' : (η Θ) c (fmap P f x) c ı).
        {
          assert ((η Θ) c ((η (monic g)) c H1) c ı ≡ (η Θ) c (fmap P f x) c ı) as <-.
          {
            apply (setoid_arr_eq _ _ ((η Θ) c) ((η (monic g)) c H1) (fmap P f x) H2 c).
          }
          apply KKK.
        }
        rewrite ->(eta_comp Θ _ _ f x c ı) in KKK'.
        simpl in KKK'.
        rewrite ->arrow_comp_id_r in KKK'.
        apply KKK'.
      + intros H1.
        simpl.
        unshelve epose proof (is_pb_ump _ _ H (HomL c) _ (! @ PSh C) _) as HH.
        {
          unshelve econstructor.
          - intros c'.
            unshelve econstructor.
            + intros f'.
              simpl in f'.
              apply (fmap P f' (fmap P f x)).
            + intros ?? HEQ; simpl.
              now rewrite HEQ.
          - intros ?? f''; simpl.
            intros a; unfold compose; simpl.
            rewrite (@fmap_comp _ _ P _ _ _ f'' a (fmap P f x)).
            simpl.
            reflexivity.
        }
        {
          constructor.
          intros c' a' d' f'; simpl.
          unfold compose; simpl.
          split; [constructor | intros _].
          rewrite (eta_comp Θ _ _ a' (fmap P f x) d' f').
          rewrite ->(eta_comp Θ _ _ f x d' (a' ∘ f')).
          simpl.
          now apply sieve_closed.
        }
        destruct HH as [R [[HR1 HR2] HR3]].
        exists (R c ı).
        simpl in HR1.
        rewrite <-(HR1 c ı).
        rewrite (@fmap_id _ _ P c (fmap P f x)).
        reflexivity.
  Qed.

  Global Instance PSh_hasSubobjectClassifier : hasSubobjectClassifier (PSh C).
  Proof.
    constructor.
    unshelve econstructor.
    - apply PSh_sieve.
    - apply PSh_true_arr_mono.
    - intros U X f.
      exists (PSh_char f).
      apply PSh_char_unique.
  Defined.

End SievesPSh.

Section Enrichment.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Local Opaque has_terminal.

  Global Program Instance PShSelfEnrichment {C : Category} : SelfEnrichment (PSh C) :=
    {|
      HOM_ID A := λₙ x, λₛ p, λₖ Γ, λₛ f, idS;
      HOM_COMP A B D := λₙ x, λₛ p, λₖ Γ, λₛ f, (fst p Γ f) ∘ (snd p Γ f);
      quote A B f := λ⟨f ∘ π₂⟩;
      unquote A B f := (eval ∘ ⟨f ×ₐ ı⟩ ∘ invπ₂);
    |}.
   Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    unfold FComp.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ????; simpl.
    reflexivity.
  Qed.
    Next Obligation.
    intros; simpl.
    simpl in *.
    destruct p as [p1 p2].
    simpl.
    intros?.
    now rewrite H.
  Qed.
  Next Obligation.
    intros; simpl.
    unfold FComp.
    intros ?????; simpl.
    destruct p as [p1 p2].
    simpl; unfold compose; simpl.
    rewrite <-(arr_fmap _ _ _ p1 B0 C0 δ₂ δ₁).
    f_equiv.
    rewrite <-(arr_fmap _ _ _ p2 B0 C0 δ₂ δ₁).
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???; simpl.
    destruct a₁ as [X1 X2].
    destruct a₂ as [Y1 Y2].
    destruct H as [H1 H2].
    simpl in *; unfold compose; simpl.
    f_equiv.
    - intros ?; apply H1.
    - apply H2.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?] ???; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?????; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?????; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ??; simpl.
    intros ???; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?????; simpl.
    pose proof (eta_comp f _ _ δ a B0 ı v) as H.
    simpl in H.
    rewrite arrow_comp_id_r in H.
    rewrite <-H.
    apply (setoid_arr_eq _ _ ((η f) B0)).
    now rewrite ->PointUnique, (PointUnique (functor.fmap (𝟙 @ PSh C) δ a)).
  Qed.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
End Enrichment.

Section Universe.
  Open Scope setoid.
  Open Scope cat.
  Open Scope functor.

  Definition ElemCatObj {C : Category} (F : PSh C) := sigT (λ a : C, F a).

  Program Definition ElemCatArrSetoid {C : Category} {F : PSh C} (a b : ElemCatObj F) : Setoid :=
    SubsetSetoid (projT1 a [~>] projT1 b) (λ (f : projT1 a [~>] projT1 b), functor.fmap F f (projT2 b) ≡ projT2 a).

  Program Definition ElemCat {C : Category} (F : PSh C) : Category :=
    {|
      Obj := ElemCatObj F;
      Arr a b := ElemCatArrSetoid a b;
      arrow_id a := Specif.exist _ (@arrow_id C (projT1 a)) (@fmap_id _ _ F (projT1 a) (projT2 a));
      arrow_comp a b c := λₛ f :: ElemCatArrSetoid b c, λₛ g :: ElemCatArrSetoid a b,
        Specif.exist _ (proj1_sig f ∘ (proj1_sig g)) _;
    |}.
  Next Obligation.
    intros; simpl.
    pose proof (@fmap_comp _ _ F _ _ _ (proj1_sig g) (proj1_sig f) (projT2 c)) as H.
    simpl in H.
    unfold compose in H.
    rewrite (proj2_sig f) in H.
    rewrite (proj2_sig g) in H.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?].
    do 2 f_equiv.
    apply H.
  Qed.
  Next Obligation.
    intros; simpl.
    now rewrite arrow_comp_id_l.
  Qed.
  Next Obligation.
    intros; simpl.
    now rewrite arrow_comp_id_r.
  Qed.
  Next Obligation.
    intros; simpl.
    now rewrite arrow_comp_assoc.
  Qed.
End Universe.

Notation "'∫' F" := (ElemCat F) (at level 50) : category_scope.

(* Section Regular. *)
(*   Local Open Scope setoid_scope. *)
(*   Local Open Scope cat_scope. *)
(*   Context {C : Category}. *)

(*   Record Regular := { *)
(*       regular_carrier :> ∀ (A B : C), Setoid; *)
(*       regular_mono : ∀ {A B : C}, regular_carrier A B → A [⤷] B; *)
(*       is_regular {A B : C} (f : A [~>] B) := *)
(*         ∃ (g : regular_carrier A B), f ≡ monic (regular_mono g); *)
(*       regular_iso : ∀ {A B : C} (f : Isomorphism A B), *)
(*         is_regular (iso1 f); *)
(*       regular_comp : ∀ {A B D : C} (g : B [~>] D) (f : A [~>] B), *)
(*         is_regular g → is_regular f → is_regular (g ∘ f); *)
(*       regular_pb_stable : ∀ {W X Y Z : C} (a : W [~>] X) (b : X [~>] Z) *)
(*                             (c : W [~>] Y) (d : Y [~>] Z) (pb : isPullback b d a c), *)
(*         is_regular b → is_regular c; *)
(*     }. *)

(* End Regular. *)
