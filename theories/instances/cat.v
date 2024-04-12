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
                      classes.exp.

Section CatInst.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Inductive hom_eq (C : Category) (X Y : C) (f : X [~>] Y) : ∀ (Z W : C), Z [~>] W -> Prop :=
| hom_eq_const : forall (g : X [~>] Y), f ≡ g -> hom_eq C X Y f _ _ g.
  Arguments hom_eq {_ _ _} _ {_ _}.

  Lemma hom_eq_refl:
    forall (C : Category) (df cf : C)(bf : df [~>] cf),
    hom_eq bf bf.
  Proof.
    intros C df cf bf; apply hom_eq_const; reflexivity.
  Qed.

  Lemma hom_eq_sym:
    forall (C: Category)
      (df cf : C)(bf : df [~>] cf)
      (dg cg : C)(bg : dg [~>] cg),
    hom_eq bf bg -> hom_eq bg bf.
  Proof.
    intros C df cf bf dg cg bg [g Heq].
    apply hom_eq_const; apply symmetry; assumption.
  Qed.

  Lemma hom_eq_trans:
    forall (C : Category)
      (df cf : C)(bf : df [~>] cf)
      (dg cg : C)(bg : dg [~>] cg)
      (dh ch : C)(bh : dh [~>] ch),
    hom_eq bf bg -> hom_eq bg bh -> hom_eq bf bh.
  Proof.
    intros C df cf bf dg cg bg dh ch bh [g Heqg] [h Heqh].
    apply hom_eq_const.
    transitivity g; assumption.
  Qed.

  Program Definition Functor_setoid (C D : Category) : Setoid :=
    {|
      setoid_carrier := Functor C D;
      setoid_eq F G := ∀ (X Y : C) (f : X [~>] Y), hom_eq (fmap F f) (fmap G f);
    |}.
  Next Obligation.
    intros; split.
    - intros ????. apply hom_eq_refl.
    - intros F G Heq X Y f.
      now apply hom_eq_sym, Heq.
    - intros F G H HeqFG HeqGH X Y f.
      eapply hom_eq_trans.
      + now apply HeqFG.
      + now apply HeqGH.
  Qed.

  Program Definition FunctorComposeS {A B C : Category} :
    Functor_setoid B C [→] Functor_setoid A B [→] Functor_setoid A C
    := λₛ f, λₛ g, FunctorCompose f g.
  Next Obligation.
    intros; simpl.
    intros X Y g.
    destruct (H _ _ g) as [? HEQ1].
    destruct ((symmetry H) _ _ g) as [? HEQ2].
    constructor.
    rewrite HEQ1.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ????.
    apply H.
  Qed.

  Program Definition Cat : Category :=
    {|
      Obj := Category;
      Arr C D := Functor_setoid C D;
      arrow_id A := @FunctorId A;
      arrow_comp A B C := @FunctorComposeS A B C;
    |}.
  Next Obligation.
    intros; simpl.
    intros ???. apply hom_eq_refl.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???. apply hom_eq_refl.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ???. apply hom_eq_refl.
  Qed.

End CatInst.
