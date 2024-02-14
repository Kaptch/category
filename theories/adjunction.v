From category Require Import
  base
  setoid
  sets
  category
  functor
  hom.

Program Definition FunctorId {C : Category}
  : Functor C C :=
  {|
    FO x := x;
    fmap A B := (λₛ f, f)%setoid;
  |}.
Next Obligation.
  intros; now simpl.
Qed.
Next Obligation.
  intros; now simpl.
Qed.
Next Obligation.
  intros; now simpl.
Qed.

Program Definition FunctorCompose {A B C : Category} (F : Functor B C)
  (G : Functor A B) : Functor A C :=
  {|
    FO i := F (G i);
    fmap X Y := (λₛ f, fmap F (fmap G f))%setoid;
  |}.
Next Obligation.
  intros; simpl.
  now rewrite H.
Qed.
Next Obligation.
  intros; simpl.
  now rewrite 2 fmap_id.
Qed.
Next Obligation.
  intros; simpl.
  now rewrite 2 fmap_comp.
Qed.

Program Definition FunctorProd {A B C D : Category} (F : Functor A C)
  (G : Functor B D) : Functor (A × B)%cat (C × D)%cat :=
  {|
    FO i := (F (fst i), G (snd i));
    fmap X Y := (λₛ f, (fmap F (fst f), fmap G (snd f)))%setoid;
  |}.
Next Obligation.
  intros ???? ?? [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
  split; now f_equiv.
Qed.
Next Obligation.
  intros ???? ?? [? ?]; simpl in *.
  now split; rewrite fmap_id.
Qed.
Next Obligation.
  intros ???? ?? [? ?] [? ?] [? ?] [? ?] [? ?]; simpl in *.
  now split; rewrite fmap_comp.
Qed.

Section Adjunction.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C D : Category}.
  Context (F : C [⇒] D) (G : D [⇒] C).

  (* Record Adjunction := { *)
  (*     adj_nat1 : FunctorId [↣] (FunctorCompose G F); *)
  (*     adj_nat2 : (FunctorCompose F G) [↣] FunctorId; *)
  (*     adj_iso1 : ∀ x, (adj_nat2 (F x)) ∘ fmap F (adj_nat1 x) ≡ arrow_id (F x); *)
  (*     adj_iso2 : ∀ x, fmap G (adj_nat2 x) ∘ (adj_nat1 (G x)) ≡ arrow_id (G x); *)
  (*   }. *)

End Adjunction.
