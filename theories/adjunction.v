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

Section Adjunction.
  Local Open Scope setoid_scope.
  Local Open Scope cat_scope.
  Local Open Scope functor_scope.

  Context {C D : Category}.
  Context (F : C [⇒] D) (G : D [⇒] C).

  (* Record Adjunction := { *)
  (*     adj_nat1 : (@FunctorId C) [↣] (FunctorCompose G F); *)
  (*     adj_nat2 : (FunctorCompose F G) [↣] (@FunctorId D); *)
  (*     adj_iso1 : ∀ x, (adj_nat2 (F x)) ∘ fmap F (adj_nat1 x) ≡ arrow_id (F x); *)
  (*     adj_iso2 : ∀ x, fmap G (adj_nat2 x) ∘ (adj_nat1 (G x)) ≡ arrow_id (G x); *)
  (*   }. *)

  (* Polymorphic Record Adjunction := { *)
  (*     adj_iso : @Isomorphism (@FunCat (C × D) SetoidCat) *)
  (*                 (FunctorCompose Hom (FunctorProd F FunctorId))                   *)
  (*                 (FunctorCompose Hom (FunctorProd FunctorId G)); *)
  (*   }. *)

  (* Polymorphic Record Adjunction := { *)
  (*     adj_iso : ∀ x, @Isomorphism (@FunCat D SetoidCat) (HomR ((F x))) (FunctorCompose (HomR x) G); *)
  (*   }. *)
End Adjunction.
