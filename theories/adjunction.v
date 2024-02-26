From category Require Import
  base
  setoid
  sets
  category
  functor
  hom.

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
