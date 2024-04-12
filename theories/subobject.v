From category Require Import
                      base
                      setoid
                      category
                      terminal
                      functor
                      limit
                      prod
                      pullback
                      classes.limits.

Section SubObjectClassifier.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C : Category}.
  Context `{hasTerminal C}.

  Record SubobjectClassifier := {
      subobject_classifier :> C;
      true : 𝟙 @ C [⤷] subobject_classifier;
      subobject_classifier_ump : ∀ {U X} (f : U [⤷] X),
        Σ! (char : X [~>] subobject_classifier),
        isPullback char true f (! @ C);
    }.

  Program Definition SubobjectClassifierUnique (A B : SubobjectClassifier)
    : Isomorphism A B :=
    {|
      iso1 := (projT1 (@subobject_classifier_ump B (𝟙 @ C) A (true A)));
      iso2 := (projT1 (@subobject_classifier_ump A (𝟙 @ C) B (true B)));
    |}.
  Next Obligation.
    intros A B.
    assert (G : isPullback (true A)
                  (projT1 (subobject_classifier_ump A (true B))
                     ∘ projT1 (subobject_classifier_ump B (true A)))
                  ((! @ C) ∘ (! @ C))
                  (true A)).
    {
      eapply PullbackCompose.
      - apply (PullbackRotate (fst (projT2 (subobject_classifier_ump A (true B))))).
      - apply (PullbackRotate (fst (projT2 (subobject_classifier_ump B (true A))))).
    }
    rewrite <-(snd (projT2 (subobject_classifier_ump A (true A)))
                (projT1 (subobject_classifier_ump A (true B))
                   ∘ projT1 (subobject_classifier_ump B (true A)))).
    - apply (snd (projT2 (subobject_classifier_ump A (true A))) ı).
      constructor.
      + constructor.
        rewrite arrow_comp_id_l.
        rewrite (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ı); [| constructor].
        now rewrite arrow_comp_id_r.
      + intros W h j L.
        exists (! @ C).
        split.
        * split.
          -- rewrite <-arrow_comp_id_l at 1.
             rewrite (CS_comm _ _ L).
             f_equiv.
             now rewrite (snd (projT2 (@terminal_proj C (𝟙 @ C) W)) j).
          -- rewrite <-(snd (projT2 (@terminal_proj C (𝟙 @ C) W)) ((! @ C) ∘ (! @ C))); [| constructor].
             now rewrite (snd (projT2 (@terminal_proj C (𝟙 @ C) W)) j).
        * intros x' X'.
          now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) W)) x').
    - apply PullbackRotate.
      constructor.
      + constructor.
        rewrite <-(CS_comm _ _ (is_pb _ _ _ G)).
        f_equiv.
        now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ((! @ C) ∘ (! @ C))).
      + intros W h j Q.
        exists (projT1 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)).
        split.
        * split.
          -- rewrite ->(proj1 (fst (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)))) at 1.
             do 2 f_equiv.
             symmetry.
             now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ((! @ C) ∘ (! @ C))).
          -- now rewrite ->(proj2 (fst (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)))) at 1.
        * intros x' X'.
          apply (snd (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)) x').
          split; [| apply (proj2 X')].
          rewrite ->(proj1 X') at 1.
          do 2 f_equiv.
          now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ((! @ C) ∘ (! @ C))).
  Qed.
  Next Obligation.
    intros A B.
    assert (G : isPullback (true B)
                  (projT1 (subobject_classifier_ump B (true A))
                     ∘ projT1 (subobject_classifier_ump A (true B)))
                  ((! @ C) ∘ (! @ C))
                  (true B)).
    {
      eapply PullbackCompose.
      - apply (PullbackRotate (fst (projT2 (subobject_classifier_ump B (true A))))).
      - apply (PullbackRotate (fst (projT2 (subobject_classifier_ump A (true B))))).
    }
    rewrite <-(snd (projT2 (subobject_classifier_ump B (true B)))
                (projT1 (subobject_classifier_ump B (true A))
                   ∘ projT1 (subobject_classifier_ump A (true B)))).
    - apply (snd (projT2 (subobject_classifier_ump B (true B))) ı).
      constructor.
      + constructor.
        rewrite arrow_comp_id_l.
        rewrite (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ı); [| constructor].
        now rewrite arrow_comp_id_r.
      + intros W h j L.
        exists (! @ C).
        split.
        * split.
          -- rewrite <-arrow_comp_id_l at 1.
             rewrite (CS_comm _ _ L).
             f_equiv.
             now rewrite (snd (projT2 (@terminal_proj C (𝟙 @ C) W)) j).
          -- rewrite <-(snd (projT2 (@terminal_proj C (𝟙 @ C) W)) ((! @ C) ∘ (! @ C))); [| constructor].
             now rewrite (snd (projT2 (@terminal_proj C (𝟙 @ C) W)) j).
        * intros x' X'.
          now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) W)) x').
    - apply PullbackRotate.
      constructor.
      + constructor.
        rewrite <-(CS_comm _ _ (is_pb _ _ _ G)).
        f_equiv.
        now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ((! @ C) ∘ (! @ C))).
      + intros W h j Q.
        exists (projT1 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)).
        split.
        * split.
          -- rewrite ->(proj1 (fst (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)))) at 1.
             do 2 f_equiv.
             symmetry.
             now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ((! @ C) ∘ (! @ C))).
          -- now rewrite ->(proj2 (fst (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)))) at 1.
        * intros x' X'.
          apply (snd (projT2 (@is_pb_ump _ _ _ _ _ _ _ _ _ G W h j Q)) x').
          split; [| apply (proj2 X')].
          rewrite ->(proj1 X') at 1.
          do 2 f_equiv.
          now apply (snd (projT2 (@terminal_proj C (𝟙 @ C) (𝟙 @ C))) ((! @ C) ∘ (! @ C))).
  Qed.
End SubObjectClassifier.

Arguments subobject_classifier {_ _ _}.
