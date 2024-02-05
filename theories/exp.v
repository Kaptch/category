From category Require Import
                      base
                      setoid
                      category
                      functor
                      terminal
                      limit
                      prod.

Section Exp.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.
  Context (bp : ∀ (J : bool → C), Prod J).

  Program Definition bin_fun_prod (Z Z' Y : C) (f : Z [~>] Z') :
    DiscreteFun (λ b : bool, if b then Z else Y)
      [↣] DiscreteFun (λ b : bool, if b then Z' else Y) :=
    λₙ x, match x with true => f | false => ı end.
  Next Obligation.
    intros ? ? ? ? [|] [|]; simpl.
    - apply (K_dec_type EqDecisionBool).
      rewrite arrow_comp_id_l, arrow_comp_id_r; reflexivity.
    - intros g; inversion g.
    - intros g; inversion g.
    - apply (K_dec_type EqDecisionBool).
      rewrite arrow_comp_id_l; reflexivity.
  Qed.

  Definition isEval (X Y Z : C) : Type :=
    cone_obj
      (terminal_obj
         (limit_obj
            (ProdDiscreteLimit (bp ((λ (b : bool), if b then Z else Y))))))
      [~>] X.

  Record Exp (X Y : C) :=
    {
      exp_obj :> C;
      eval : isEval X Y exp_obj;
      exp_ump : ∀ (Z' : C) (eval' : isEval X Y Z'),
        Σ! f : (Z' [~>] exp_obj),
        eval' ≡
          eval
          ∘ ArrProd
          ((λ b : bool, if b then Z' else Y))
          ((λ b : bool, if b then exp_obj else Y))
          (bin_fun_prod Z' exp_obj Y f) _ _;
    }.

  (* Program Definition ExpUnique (X Y : C) (a b : Exp X Y) : Isomorphism a b := *)
  (*   {| *)
  (*     iso1 := (projT1 (exp_ump X Y b a (eval X Y a))); *)
  (*     iso2 := (projT1 (exp_ump X Y a b (eval X Y b))); *)
  (*   |}. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   rewrite <-(snd (projT2 (exp_ump X Y a a (eval X Y a))) *)
  (*               (projT1 (exp_ump X Y a b (eval X Y b)) *)
  (*                  ∘ projT1 (exp_ump X Y b a (eval X Y a)))). *)
  (*   - rewrite <-(snd (projT2 (exp_ump X Y a a (eval X Y a))) ı). *)
  (*     + reflexivity. *)
  (*     + rewrite (fst (projT2 (exp_ump X Y a a (eval X Y a)))). *)
  (*       do 2 f_equiv. *)
  (*       * apply (fst (projT2 (exp_ump X Y a a (eval X Y a)))). *)
  (*       * admit. *)
  (*   - admit. *)
  (* Admitted. *)
  (* Next Obligation. *)
  (*   rewrite <-(snd (projT2 (exp_ump X Y b b (eval X Y b))) *)
  (*               (projT1 (exp_ump X Y b a (eval X Y a)) *)
  (*                  ∘ projT1 (exp_ump X Y a b (eval X Y b)))). *)
  (*   - rewrite <-(snd (projT2 (exp_ump X Y b b (eval X Y b))) ı). *)
  (*     + reflexivity. *)
  (*     + admit. *)
  (*   - admit. *)
  (* Admitted. *)
End Exp.
