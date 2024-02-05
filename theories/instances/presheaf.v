From category Require Import
                      base
                      setoid
                      category
                      sets
                      terminal
                      functor
                      limit
                      prod
                      exp
                      pullback
                      subobject
                      instances.sets.

Definition PSh (C : Category) : Category := @FunCat (C op)%cat SetoidCat.

Section PSh_exp.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {Obj : Category}.

  Class FComp {X Y : PSh Obj} {A} (K : ∀ {B}, (Arr A B) → X B → Y B) :=
    comp_fmap : ∀ {B C} (δ₂ : Arr B C) (δ₁ : Arr A B) (v : X B),
        K (δ₂ ∘ δ₁) (fmap X δ₂ v) ≡ fmap Y δ₂ (K δ₁ v).

  Record RemFun (X Y : PSh Obj) (A : Obj op) :=
    { arr :> ∀ {B}, (Arr A B) → X B → Y B;
      arr_ext {B : Obj op}
      : Proper (setoid_eq ==> setoid_eq ==> setoid_eq) (@arr B);
      arr_fmap : FComp (@arr)
    }.
  Arguments arr {X Y A} _ {B} _ _.

  Global Instance RF_prop {X Y : PSh Obj} {A} {RF : RemFun X Y A} {B} :
    Proper (setoid_eq ==> setoid_eq ==> setoid_eq) (RF B) :=
    arr_ext _ _ _ RF.

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
    λ {A B} δ φ, {| arr C δ' v := φ C (δ' ∘ δ) v |}.
  Next Obligation.
    intros X Y A B δ φ C.
    intros δ₁ δ₂ EQδ v₁ v₂ EQv; now rewrite EQδ, EQv.
  Qed.
  Next Obligation.
    unfold FComp; intros; rewrite arrow_comp_assoc; apply arr_fmap.
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

Notation "'λₖ' Γ δ μ , e" :=
  {| arr Γ δ μ := e;
    arr_ext := _;
    arr_fmap := _
  |} (at level 120, Γ binder, δ binder, μ binder, no associativity)
    : functor_scope.

Section PSh_inst.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

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
    unfold id; simpl.
    simpl.
    etransitivity; [apply (@fmap_id _ _ J) |].
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    unfold compose; intros; simpl.
    rewrite (@fmap_comp D (PSh C) J _ _ _ f g c a).
    simpl.
    unfold compose; simpl.
    reflexivity.
  Qed.

  Program Definition PSh_limit {C} (D : Category) (J : D [⇒] (PSh C)) : PSh C :=
    {|
      FO c := terminal_obj (limit_obj (Setoid_hasLimits
                                         (PSh_limit_pointwise D J c)));
      fmap A B := λₛ x, λₛ X, λₙ y, λₛ T, (fmap (J y) x (X y tt));
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
    apply (@eta_comp D SetoidCat _ _ X _ _ f tt).
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
    simpl; unfold id; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    simpl.
    intros ? ? ? ? ? ? ? ? ? ? []; simpl.
    rewrite (@fmap_comp (C op) SetoidCat (J X) _ _ _ f g (a X tt)).
    simpl; unfold compose; simpl.
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
    rewrite (@eta_comp _ _ _ _ (η cone_nat X) _ _ f a b).
    simpl.
    unfold compose; simpl.
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
    epose proof (@eta_comp (C op) SetoidCat _ (J X1) _ _ _ f) as H'.
    simpl in H'.
    unfold compose in H'.
    simpl in H'.
    rewrite H'.
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
        existT _ (PSh_limit_cone_terminal_arr D J X) _;
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

  Program Definition PSh_hasBinProducts {C} (J : bool -> PSh C) : Prod J :=
    {|
      prod_obj :=
        {|
          FO X := (J Datatypes.true X × J false X)%setoid;
          fmap A B := λₛ f :: @Arr C B A,
            λₛ g,
            (fmap (J Datatypes.true) f (fst g)
              , fmap (J false) f (snd g));
        |};
      proj_arr := λₙ x, λₙ y, λₛ z, if x as b return (J b y) then fst z else snd z;
    |}.
  Next Obligation.
    intros; simpl.
    split; f_equiv; apply H.
  Defined.
  Next Obligation.
    intros; simpl.
    intros [? ?]; simpl.
    split; do 3 f_equiv; apply H.
  Defined.
  Next Obligation.
    intros; simpl.
    intros [? ?]; simpl.
    split.
    - apply (@fmap_id (C op) SetoidCat (J Datatypes.true) A s).
    - apply (@fmap_id (C op) SetoidCat (J false) A s0).
  Qed.
  Next Obligation.
    intros; simpl.
    intros [? ?]; simpl.
    split.
    - apply (@fmap_comp (C op) SetoidCat (J Datatypes.true)).
    - apply (@fmap_comp (C op) SetoidCat (J false)).
  Qed.
  Next Obligation.
    intros; simpl in *.
    destruct x; apply H.
  Qed.
  Next Obligation.
    intros; simpl in *.
    destruct x; intros [? ?]; simpl;
      unfold compose; simpl; reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    destruct f.
    intros; simpl; unfold compose; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    unshelve econstructor.
    - unshelve econstructor.
      + intros; simpl.
        unshelve econstructor.
        * intros; simpl.
          apply ((H Datatypes.true X X0), (H false X X0)).
        * intros; simpl.
          split; now rewrite H0.
      + intros; simpl.
        intros; simpl.
        split.
        * apply (@eta_comp _ _ _ _ (η (η H) Datatypes.true) _ _ f).
        * apply (@eta_comp _ _ _ _ (η (η H) false) _ _ f).
    - split.
      + intros; simpl; unfold compose; simpl.
        destruct j; reflexivity.
      + intros; simpl.
        intros; simpl.
        split.
        * rewrite H0.
          unfold compose; simpl.
          reflexivity.
        * rewrite H0.
          unfold compose; simpl.
          reflexivity.
  Defined.

  Program Definition PArr_hasEval {C} (X Y : PSh C)
    : isEval PSh_hasBinProducts X Y (PArr Y X) :=
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
    f_equiv.
    now rewrite arrow_comp_id_r.
  Qed.

  Program Definition PArr_ump {C} (X Y : PSh C) :
    ∀ (Z' : PSh C) (eval' : isEval PSh_hasBinProducts X Y Z'),
    Σ! f : (Z' [~>] (PArr Y X)),
    eval' ≡
      (PArr_hasEval X Y)
      ∘ ArrProd
      (λ b : bool, if b then Z' else Y)
      (λ b : bool, if b then (PArr Y X) else Y)
      (bin_fun_prod Z' (PArr Y X) Y f) _ _ :=
  λ Z' eval',
    existT
      _
      (λₙ x, λₛ y, λₖ Γ δ μ, (eval' Γ ((fmap Z' δ y), μ)))
      _.
  Next Obligation.
    intros; simpl.
    intros ??????.
    f_equiv; split; simpl; [now do 2 f_equiv| assumption].
  Qed.
  Next Obligation.
    intros; simpl.
    intros ?????.
    pose proof (@eta_comp (C op) SetoidCat _ _ eval' _ _ δ₂) as H.
    simpl in H.
    unfold compose in H.
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
      rewrite (@eta_comp (C op) SetoidCat Z'
                    (PArr Y X) x' X0 B δ a B ı v).
      simpl.
      now rewrite arrow_comp_id_r.
  Qed.

  Program Definition PSh_Exp {C} (X Y : PSh C)
    : Exp PSh_hasBinProducts X Y :=
    {|
      exp_obj := PArr Y X;
      eval := PArr_hasEval X Y;
      exp_ump := PArr_ump X Y;
    |}.

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
      apply H.
      apply H'.
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

  Local Axiom ID_epsilon :
    ∀ T : Type, ConstructiveIndefiniteDescription_on T.

  Program Definition PSh_sieve : PSh C :=
    {|
      FO x := SieveSetoid x;
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

  Program Definition PSh_Terminal : Terminal (PSh C)
    := EmptyLimit (PSh_hasLimits Empty_diagram).

  Program Definition PSh_true_arr
    : PSh_Terminal [~>] PSh_sieve
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
    : PSh_Terminal [⤷] PSh_sieve :=
    {|
      monic := PSh_true_arr;
    |}.
  Next Obligation.
    intros; simpl.
    intros X ? d f.
    reflexivity.
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

  Lemma char_Pb {X Y : PSh C} (f : X [⤷] Y)
    : isPullback (PSh_char f)
        (PSh_true_arr)
        f
        (projT1 (terminal_proj X)).
  Proof.
    unshelve econstructor.
    - unshelve econstructor.
      intros x.
      simpl.
      intros; simpl.
      split; [constructor |].
      intros _.
      exists (fmap X f0 a).
      pose proof (eta_comp (monic f) _ _ f0 a) as H.
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
          destruct (ID_epsilon (X x)) as [X1 ?].
          destruct (ID_epsilon (X x)) as [X2 ?].
          rewrite (@fmap_id _ _ Y x ((η h) x a₂)) in s0.
          rewrite (@fmap_id _ _ Y x ((η h) x a₁)) in s.
          simpl in *.
          unfold id in *.
          simpl in *.
          (* provable, f is mono *)
          admit.
      + intros; simpl.
        intros; simpl.
        unfold compose; simpl.
        destruct (ID_epsilon (X Y0)) as [X1 ?].
        destruct (ID_epsilon (X X0)) as [X2 ?].
        rewrite (@fmap_id _ _ Y X0 ((η h) X0 a)) in s0.
        rewrite (@fmap_id _ _ Y Y0 ((η h) Y0 (fmap W f0 a))) in s.
        simpl in *.
        unfold id in *.
        simpl in *.
        admit.
  Admitted.

End SievesPSh.
