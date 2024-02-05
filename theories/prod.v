From category Require Import
  base
  setoid
  category
  functor
  terminal
  limit.

Section InternalProd.
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
  Qed.

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

  Program Definition ArrProdCone {D : Type}
    `{!EqDecision D}
    {C : Category}
    (f : D → C)
    (g : D → C)
    (h : DiscreteFun f [↣] DiscreteFun g)
    (Hf : Prod f)
    (Hg : Prod g)
    : ConeArr _ (ConeReindex _ _ h (ProdCone Hf)) (ProdCone Hg) :=
    {|
      cone_arr := (projT1 (prod_ump _ Hg Hf (h ∘ (proj_arr _ Hf))));
    |}.
  Next Obligation.
    intros; simpl.
    rewrite (fst (projT2 (prod_ump _ Hg Hf (h ∘ (proj_arr _ Hf)))) j).
    reflexivity.
  Qed.

  Definition ArrProd {D : Type}
    `{!EqDecision D}
    {C : Category}
    (f : D → C)
    (g : D → C)
    (h : (DiscreteFun f [↣] DiscreteFun g)%functor)
    (Hf : Prod f)
    (Hg : Prod g)
    : (prod_obj f Hf [~>] prod_obj g Hg)%cat
    := (projT1 (prod_ump _ Hg Hf (h ∘ (proj_arr _ Hf)))).
End InternalProd.

Section TerminalLimit.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Global Instance EqDecisionEmpty : EqDecision Empty_set.
  Proof.
    intros [].
  Qed.

  Global Instance EqDecisionUnit : EqDecision unit.
  Proof.
    intros [] []; left; reflexivity.
  Qed.

  Definition Empty_diagram {C} : ⌊ Empty_set ⌋ [⇒] C :=
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
                                (@Empty_diagram C)) (ConeEmpty X) 𝟭).
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
