From category Require Import
  base
  setoid
  category
  functor
  terminal
  limit.

Section ArbitraryProd.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Record Prod {C : Category} {I : Type} `{!EqDecision I} (J : I → C) :=
    {
      prod_obj :> C;
      proj_arr : Δ prod_obj [↣] DiscreteFun J;
      prod_ump : ∀ (p' : C) (H : Δ p' [↣] DiscreteFun J),
        Σ! (u : p' [~>] prod_obj), ∀ j, H j ≡ proj_arr j ∘ u;
    }.

  Program Definition ProdCone {C : Category} {I : Type} `{!EqDecision I}
    {J : I → C} (p : Prod J) : ConeCat (DiscreteFun J) :=
    {|
      cone_obj := p;
      cone_nat := λₙ X, proj_arr J p X;
    |}.
  Next Obligation.
    intros ???????; simpl.
    intros f.
    destruct f.
    now rewrite arrow_comp_id_l, arrow_comp_id_r.
  Qed.

  Program Definition ProdTerminalArr {C : Category} {I : Type} `{!EqDecision I}
    {J : I → C} (p : Prod J) (X : ConeCat (DiscreteFun J))
    : ConeArr (DiscreteFun J) X (ProdCone p) :=
    {|
      cone_arr := projT1 (prod_ump J p X (cone_nat X));
    |}.
  Next Obligation.
    intros; simpl.
    apply (fst (projT2 (prod_ump J p X (cone_nat X))) j).
  Qed.

  Program Definition ProdTerminal {C : Category} {I : Type} `{!EqDecision I}
    {J : I → C} (p : Prod J) : Terminal (ConeCat (DiscreteFun J)) :=
    {|
      terminal_obj := ProdCone p;
    |}.
  Next Obligation.
    intros.
    exists (ProdTerminalArr p X).
    split; [constructor |].
    intros x' _; simpl.
    apply (snd (projT2 (prod_ump J p X (cone_nat X)))).
    intros j.
    apply (@cone_comp (⌊ I ⌋) C (DiscreteFun J) X (ProdCone p)).
  Defined.

  Program Definition ProdDiscreteLimit {C : Category} {I : Type} `{!EqDecision I}
    {J : I → C} (p : Prod J) : Limit (DiscreteFun J) :=
    {|
      limit_obj := ProdTerminal p;
    |}.

  Program Definition DiscreteLimitProd {C : Category} {I : Type} `{!EqDecision I}
    {J : I → C} (p : Limit (DiscreteFun J)) : Prod J :=
    {|
      prod_obj := cone_obj (terminal_obj (limit_obj p));
      proj_arr := λₙ x, (cone_nat (terminal_obj (limit_obj p)) x);
    |}.
  Next Obligation.
    intros; simpl.
    rewrite arrow_comp_id_r.
    destruct f.
    rewrite arrow_comp_id_l.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    pose (pack := {| cone_obj := p'; cone_nat := H |}).
    exists (cone_arr (projT1
                   (@terminal_proj _ (limit_obj p)
                      pack))).
    split.
    - intros i; simpl.
      apply (@cone_comp (⌊ I ⌋) C (DiscreteFun J) pack (terminal_obj (limit_obj p)) _ i).
    - intros G K.
      unshelve epose (pack_arr := _ : ConeArr _ pack
                                        (@terminal_obj
                                           (@ConeCat (DiscreteCat I) C
                                              (DiscreteFun J))
                                           (@limit_obj (DiscreteCat I) C
                                              (DiscreteFun J) p))).
      {
        unshelve econstructor.
        - subst pack; simpl.
          apply G.
        - simpl.
          apply K.
      }
      now apply (snd (projT2 (@terminal_proj _ (limit_obj p)
                                pack)) pack_arr).
  Qed.

End ArbitraryProd.

Section BinProd.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Record BinProd {C : Category} (X Y : C) :=
    {
      bin_prod_obj :> C;
      bin_proj_arr₁ : bin_prod_obj [~>] X;
      bin_proj_arr₂ : bin_prod_obj [~>] Y;
      bin_prod_ump : ∀ (p' : C) (p₁ : p' [~>] X) (p₂ : p' [~>] Y),
        Σ! (u : p' [~>] bin_prod_obj),
        p₁ ≡ bin_proj_arr₁ ∘ u ∧ p₂ ≡ bin_proj_arr₂ ∘ u;
    }.

  Program Definition BinProdCone {C : Category} {X Y : C} (p : BinProd X Y)
    : ConeCat (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y))
    :=
    {|
      cone_obj := p;
      cone_nat := λₙ A :: ⌊ bool ⌋,
        (if A as b return ((Δ p) (b : ⌊ bool ⌋) [~>] DiscreteFun
                             (λ b' : bool, if b' then X else Y) b)
         then bin_proj_arr₁ X Y p
         else bin_proj_arr₂ X (DiscreteFun
                                 (λ b : bool, if b then X else Y) false) p);
    |}.
  Next Obligation.
    intros; simpl.
    destruct f.
    rewrite arrow_comp_id_l.
    rewrite arrow_comp_id_r.
    reflexivity.
  Qed.

  Program Definition BinProdTerminalArr {C : Category} {X Y : C}
    (p : BinProd X Y) (A : ConeCat
                             (@DiscreteFun _
                                EqDecisionBool _
                                (λ b : bool, if b then X else Y)))
    : ConeArr
        (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y))
        A (BinProdCone p) :=
    {|
      cone_arr := projT1 (bin_prod_ump X Y p A
                            (cone_nat A true)
                            (cone_nat A false));
    |}.
  Next Obligation.
    intros; simpl.
    destruct j; simpl.
    - apply (proj1 (fst (projT2 (bin_prod_ump X Y p A
                                   (cone_nat A true)
                                   (cone_nat A false))))).
    - apply (proj2 (fst (projT2 (bin_prod_ump X Y p A
                                   (cone_nat A true)
                                   (cone_nat A false))))).
  Qed.

  Program Definition BinProdTerminal {C : Category} {X Y : C}
    (p : BinProd X Y)
    : Terminal (ConeCat
                  (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y))) :=
    {|
      terminal_obj := BinProdCone p;
    |}.
  Next Obligation.
    intros C X Y p A.
    exists (BinProdTerminalArr p A).
    split; [constructor |].
    intros x' _; simpl.
    apply (snd (projT2 (bin_prod_ump X Y p A
                          (cone_nat A true)
                          (cone_nat A false)))).
    split.
    - apply (@cone_comp (@DiscreteCat _ EqDecisionBool) C
               (DiscreteFun (λ b : bool, if b then X else Y)) A (BinProdCone p) x' true).
    - apply (@cone_comp (@DiscreteCat _ EqDecisionBool) C
               (DiscreteFun (λ b : bool, if b then X else Y)) A (BinProdCone p) x' false).
  Defined.

  Program Definition BinProdProdTerminal {C : Category} {X Y : C} (p : BinProd X Y)
    (p' : @Prod C bool EqDecisionBool
            (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y)))
    : Isomorphism (BinProdTerminal p) (ProdTerminal p').
  Proof.
    apply TerminalUnique.
  Defined.

  Program Definition BinProdProdCone {C : Category} {X Y : C} (p : BinProd X Y)
    (p' : @Prod C bool EqDecisionBool
            (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y)))
    : Isomorphism (BinProdCone p) (ProdCone p').
  Proof.
    apply BinProdProdTerminal.
  Defined.

  Program Definition BinProdProd {C : Category} {X Y : C} (p : BinProd X Y)
    (p' : @Prod C bool EqDecisionBool
            (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y)))
    : Isomorphism p p' :=
    {|
      iso1 := (cone_arr (iso1 (BinProdProdCone p p')));
      iso2 := (cone_arr (iso2 (BinProdProdCone p p')));
      iso12 := (iso12 (BinProdProdCone p p'));
      iso21 := (iso21 (BinProdProdCone p p'));
    |}.

  Program Definition BinProdDiscreteLimit {C : Category} {X Y : C}
    (p : BinProd X Y)
    : Limit (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y)) :=
    {|
      limit_obj := BinProdTerminal p;
    |}.

  Program Definition DiscreteLimitBinProd {C : Category} {X Y : C}
    (p : Limit (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y)))
    : BinProd X Y :=
    {|
      bin_prod_obj := cone_obj (terminal_obj (limit_obj p));
      bin_proj_arr₁ := cone_nat (terminal_obj (limit_obj p)) true;
      bin_proj_arr₂ := cone_nat (terminal_obj (limit_obj p)) false;
    |}.
  Next Obligation.
    intros; simpl.
    unshelve epose (pack :=
                      {|
                        cone_obj := p';
                        cone_nat := λₙ x :: ⌊ bool ⌋, _;
                      |}
                      : ConeCat (@DiscreteFun
                                   _
                                   EqDecisionBool
                                   _
                                   (fun b : bool => if b then X else Y))).
    { destruct x; [apply p₁ | apply p₂]. }
    {
      intros; simpl.
      destruct f.
      rewrite arrow_comp_id_r, arrow_comp_id_l.
      reflexivity.
    }
    exists (cone_arr (projT1
                   (@terminal_proj _ (limit_obj p)
                      pack))).
    split.
    - split.
      + apply (@cone_comp (⌊ bool ⌋) C
                 (@DiscreteFun
                    _
                    EqDecisionBool
                    _
                    (λ b : bool, if b then X else Y))
                 pack (terminal_obj (limit_obj p)) _ true).
      + apply (@cone_comp (⌊ bool ⌋) C
                 (@DiscreteFun
                    _
                    EqDecisionBool
                    _
                    (λ b : bool, if b then X else Y))
                 pack (terminal_obj (limit_obj p)) _ false).
    - intros G K.
      unshelve epose (pack_arr := _ : ConeArr _ pack
                                        (@terminal_obj
                                           (@ConeCat (DiscreteCat bool) C
                                              (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y)))
                                           (@limit_obj (DiscreteCat bool) C
                                              (@DiscreteFun _ EqDecisionBool _ (λ b : bool, if b then X else Y)) p))).
      {
        unshelve econstructor.
        - subst pack; simpl.
          apply G.
        - simpl.
          intros [|]; [apply (proj1 K) | apply (proj2 K)].
      }
      now apply (snd (projT2 (@terminal_proj _ (limit_obj p)
                                pack)) pack_arr).
  Qed.

End BinProd.

Section TerminalLimit.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Global Instance EqDecisionEmpty : EqDecision (Empty_set : Type).
  Proof.
    intros [].
  Qed.

  Global Instance EqDecisionUnit : EqDecision unit.
  Proof.
    intros [] []; left; reflexivity.
  Qed.

  Definition Empty_diagram {C} : @DiscreteCat Empty_set EqDecisionEmpty [⇒] C :=
    DiscreteFun (Empty_set_rect _).

  Program Definition ConeEmpty {C : Category} (c : C)
    : @Cone (⌊ Empty_set ⌋) C Empty_diagram :=
    {|
      cone_obj := c;
      cone_nat := λₙ x :: ⌊ Empty_set ⌋, match x with end;
    |}.
  Next Obligation.
    intros ?? [].
  Qed.

  Program Definition TerminalEmpty {C : Category} (c : Terminal C)
    : @Terminal (ConeCat Empty_diagram) :=
    {|
      terminal_obj := ConeEmpty c;
    |}.
  Next Obligation.
    intros.
    unshelve econstructor.
    - unshelve econstructor.
      + apply terminal_proj.
      + intros [].
    - split; [constructor |].
      intros x' _.
      simpl.
      now apply (snd (projT2 (@terminal_proj C c X)) x').
  Qed.

  Definition LimitEmpty {C : Category} (c : Terminal C)
    : @Limit _ C Empty_diagram :=
    {|
      limit_obj := TerminalEmpty c;
    |}.

  Program Definition EmptyLimit {C : Category} (c : @Limit _ C Empty_diagram)
    : Terminal C :=
    {|
      terminal_obj := terminal_obj (limit_obj c);
    |}.
  Next Obligation.
    intros; simpl.
    exists (cone_arr (projT1
                   (@terminal_proj
                      (@ConeCat _ C Empty_diagram) c (ConeEmpty X)))).
    split; [constructor |].
    intros x _.
    unshelve epose (ttt := _
                      : @Arr (@ConeCat (DiscreteCat Empty_set) C
                                (@Empty_diagram C)) (ConeEmpty X) (terminal_obj _)).
    {
      apply (limit_obj c).
    }
    {
      unshelve econstructor.
      - apply x.
      - intros [].
    }
    pose proof (snd (projT2
                       (@terminal_proj
                          (@ConeCat _ C Empty_diagram) c (ConeEmpty X))) ttt) as H.
    simpl in H.
    now apply H.
  Qed.

End TerminalLimit.
