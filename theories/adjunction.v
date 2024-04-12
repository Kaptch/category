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

(*   Class IsAdjunction *)
(*       (C D: Category)(F: C --> D)(G: D --> C) *)
(*       (lr: forall {c: C}{d: D}, Map (D (F c) d) (C c (G d))) *)
(*       (rl: forall {c: C}{d: D}, Map (C c (G d)) (D (F c) d)) := *)
(*   { *)
(*     adj_iso_lr_rl: *)
(*       forall (c: C)(d: D)(f: D (F c) d), *)
(*         rl (lr f) == f; *)

(*     adj_iso_rl_lr: *)
(*       forall (c: C)(d: D)(g: C c (G d)), *)
(*         lr (rl g) == g; *)

(*     adj_lr_naturality: *)
(*       forall (c c': C)(d d': D)(f : C c' c)(g: D d d')(h: D (F c) d), *)
(*         lr (g \o h \o fmap F f) == fmap G g \o lr h \o f; *)

(*     adj_rl_naturality: *)
(*       forall (c c': C)(d d': D)(f : C c' c)(g: D d d')(h: C c (G d)), *)
(*         rl (fmap G g \o h \o f) == g \o rl h \o fmap F f *)
(*   }. *)

(* Structure Adjunction (C D: Category)(F: C --> D)(G: D --> C) := *)
(*   { *)
(*     adj_lr: forall {c: C}{d: D}, Map (D (F c) d) (C c (G d)); *)
(*     adj_rl: forall {c: C}{d: D}, Map (C c (G d)) (D (F c) d); *)

(*     prf:> IsAdjunction (@adj_lr) (@adj_rl) *)
  (*   }. *)

(*   Program Definition adj_unit *)
(*         (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G) *)
(*   : (Id C) ==> (G \o F) := *)
(*   [ c :=> adj_lr adj (Id (F c))]. *)
(* Next Obligation. *)
(*   rewrite <- cat_comp_id_cod. *)
(*   rewrite <- (fmap_id (F Y)). *)
(*   rewrite <- adj_lr_naturality. *)
(*   rewrite !cat_comp_id_cod. *)
(*   symmetry. *)
(*   rewrite <- cat_comp_id_dom, cat_comp_assoc. *)
(*   rewrite <- adj_lr_naturality. *)
(*   now rewrite cat_comp_id_cod, fmap_id, cat_comp_id_dom. *)
  (* Qed. *)

(*   Program Definition adj_counit *)
(*         (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G): *)
(*   (F \o G) ==> (Id D)  := *)
(*   [d :=> adj_rl adj (Id (G d))]. *)
(* Next Obligation. *)
(*   intros; simpl. *)
(*   rewrite <- cat_comp_id_cod. *)
(*   rewrite <- adj_rl_naturality. *)
(*   rewrite fmap_id, cat_comp_id_cod. *)
(*   symmetry. *)
(*   rewrite <- cat_comp_id_dom, <- fmap_id, cat_comp_assoc. *)
(*   rewrite <- adj_rl_naturality. *)
(*   now rewrite !cat_comp_id_dom, cat_comp_id_cod. *)
(* Qed. *)

(*   Program Definition Natrans_id_dom (C D: Category)(F: C --> D): (F \o Id C) ==> F := *)
(*   [X :=> fmap F (Id X)]. *)
(* Next Obligation. *)
(*   now rewrite !fmap_id, cat_comp_id_dom, cat_comp_id_cod. *)
(* Qed. *)
(* Notation "[ * \o '1' ==> * ]" := (Natrans_id_dom _). *)

(* Program Definition Natrans_id_dom_inv (C D: Category)(F: C --> D): F ==> (F \o Id C) := *)
(*   [X :=> fmap F (Id X)]. *)
(* Next Obligation. *)
(*   now rewrite !fmap_id, cat_comp_id_dom, cat_comp_id_cod. *)
(* Qed. *)
(* Notation "[ * ==> * \o '1' ]" := (Natrans_id_dom_inv _). *)

(* Program Definition Natrans_id_cod (C D: Category)(F: C --> D): (Id D \o F) ==> F := *)
(*   [X :=> Id (F X)]. *)
(* Next Obligation. *)
(*   now rewrite cat_comp_id_dom, cat_comp_id_cod. *)
(* Qed. *)
(* Notation "[ '1' \o * ==> * ]" := (Natrans_id_cod _). *)

(* Program Definition Natrans_id_cod_inv (C D: Category)(F: C --> D): F ==> (Id D \o F) := *)
(*   [X :=> Id (F X)]. *)
(* Next Obligation. *)
(*   now rewrite cat_comp_id_dom, cat_comp_id_cod. *)
(* Qed. *)
(* Notation "[ * ==> '1' \o * ]" := (Natrans_id_cod_inv _). *)

(* Program Definition Natrans_assoc (B C D E: Category)(F: B --> C)(G: C --> D)(H: D --> E): (H \o (G \o F)) ==> ((H \o G) \o F) := *)
(*   [ X in B :=> Id (H (G (F X)))]. *)
(* Next Obligation. *)
(*   now rewrite cat_comp_id_dom, cat_comp_id_cod. *)
(* Qed. *)
(* Notation Nassoc := (Natrans_assoc _ _ _). *)

(* Program Definition Natrans_assoc_inv (B C D E: Category)(F: B --> C)(G: C --> D)(H: D --> E): ((H \o G) \o F) ==> (H \o (G \o F)) := *)
(*   [ X in B :=> Id (H (G (F X)))]. *)
(* Next Obligation. *)
(*   now rewrite cat_comp_id_dom, cat_comp_id_cod. *)
(* Qed. *)
(* Notation Nassoc_inv := (Natrans_assoc_inv _ _ _). *)


(* Definition adj_triangle  *)
(*            (C D: Category) *)
(*            (F: C --> D)(G: D --> C) *)
(*            (au: (Id C) ==> (G \o F)) *)
(*            (ac: (F \o G) ==> (Id D)) := *)
(*   ([1 \o * ==> *] *)
(*      \o (ac o> F) *)
(*      \o Nassoc *)
(*      \o (F <o au) *)
(*      \o [* ==> * \o 1] *)
(*    == Id F *)
(*     in Natrans_setoid _ _)      (* acF \o Fau == Id_F *) *)
(*   /\ *)
(*   ([* \o 1 ==> *] *)
(*      \o (G <o ac) *)
(*      \o Nassoc_inv *)
(*      \o (au o> G) *)
(*      \o [* ==> 1 \o *] *)
(*    == Id G *)
(*     in Natrans_setoid _ _).     (* Gac \o auG == Id_G *) *)

(* Lemma adj_satisfies_triangle: *)
(*   forall (C D: Category)(F: C --> D)(G: D --> C)(adj: F -| G), *)
(*     adj_triangle (adj_unit adj) (adj_counit adj). *)
(* Proof. *)
(*   intros; split; simpl; [intro c | intro d]; *)
(*     rewrite fmap_id, ?cat_comp_id_dom, ?cat_comp_id_cod. *)
(*   - rewrite <- cat_comp_id_cod, <- adj_rl_naturality. *)
(*     rewrite fmap_id, !cat_comp_id_cod. *)
(*     now rewrite adj_iso_lr_rl. *)
(*   - rewrite <- cat_comp_id_dom, cat_comp_assoc, <- adj_lr_naturality. *)
(*     rewrite fmap_id, !cat_comp_id_dom. *)
(*     now rewrite adj_iso_rl_lr. *)
(* Qed. *)

(* Program Definition Adjunction_by_unit_and_counit *)
(*         (C D: Category) *)
(*         (F: C --> D)(G: D --> C) *)
(*         (au: (Id C) ==> (G \o F)) *)
(*         (ac: (F \o G) ==> (Id D)) *)
(*         (Hadj: adj_triangle au ac) *)
(*   : F -| G := *)
(*   [Adj by (fun c d => [g in D (F c) d :-> fmap G g \o au c]), *)
(*           (fun c d => [f in C c (G d) :-> ac d \o fmap F f])]. *)
(* Next Obligation. *)
(*   now intros g g' Heq; rewrite Heq. *)
(* Qed. *)
(* Next Obligation. *)
(*   now intros f f' Heq; rewrite Heq. *)
(* Qed. *)
(* Next Obligation. *)
(*   - rewrite fmap_comp, <- cat_comp_assoc. *)
(*     rewrite (natrans_naturality (IsNatrans:=ac) f); simpl. *)
(*     rewrite cat_comp_assoc. *)
(*     destruct Hadj as [HF HG]. *)
(*     generalize (HF c); simpl. *)
(*     rewrite fmap_id, !cat_comp_id_cod, !cat_comp_id_dom. *)
(*     now intros H; rewrite H, cat_comp_id_dom. *)
(*   - rewrite fmap_comp, cat_comp_assoc. *)
(*     rewrite <- (natrans_naturality (IsNatrans:=au) g); simpl. *)
(*     rewrite <- cat_comp_assoc. *)
(*     destruct Hadj as [HF HG]. *)
(*     generalize (HG d); simpl. *)
(*     rewrite fmap_id, !cat_comp_id_cod, !cat_comp_id_dom. *)
(*     now intros H; rewrite H, cat_comp_id_cod. *)
(*   - rewrite !fmap_comp, !cat_comp_assoc. *)
(*     now rewrite (natrans_naturality (IsNatrans:=au) f). *)
(*   - rewrite !fmap_comp, <- !cat_comp_assoc. *)
(*     now rewrite (natrans_naturality (IsNatrans:=ac) g). *)
(* Qed. *)

End Adjunction.
