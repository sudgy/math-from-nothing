(** This file contains a few tactics that can be useful at times. *)

Require Export logic.

(** Can be used to simplify expressions of the type [If H then a else b] *)
Ltac case_if :=
    let go P := destruct P; try solve [elimtype False] in
    match goal with
    | |- context [if ?P then _ else _] => go P
    | K: context [if ?P then _ else _] |- _ => go P
    end.

Tactic Notation "bring_left" constr(x) constr(comm) constr(assoc) :=
    repeat rewrite assoc;
    repeat rewrite (comm _ x);
    repeat rewrite <- assoc.
Tactic Notation "bring_left" constr(x) constr(comm) constr(assoc)
"in" constr(H) :=
    repeat rewrite assoc in H;
    repeat rewrite (comm _ x) in H;
    repeat rewrite <- assoc in H.
Tactic Notation "bring_right" constr(x) constr(comm) constr(assoc) :=
    repeat rewrite <- assoc;
    repeat rewrite (comm x _);
    repeat rewrite assoc.
Tactic Notation "bring_right" constr(x) constr(comm) constr(assoc)
"in" constr(H) :=
    repeat rewrite <- assoc in H;
    repeat rewrite (comm x _) in H;
    repeat rewrite assoc in H.

Tactic Notation "cancel_left"
constr(x) constr(comm) constr(assoc) constr(cancel) :=
    bring_left x comm assoc;
    apply cancel.
Tactic Notation "cancel_left"
constr(x) constr(comm) constr(assoc) constr(cancel) "in" constr(H) :=
    bring_left x comm assoc in H;
    apply cancel in H.
Tactic Notation "cancel_right"
constr(x) constr(comm) constr(assoc) constr(cancel) :=
    bring_right x comm assoc;
    apply cancel.
Tactic Notation "cancel_right"
constr(x) constr(comm) constr(assoc) constr(cancel) "in" constr(H) :=
    bring_right x comm assoc in H;
    apply cancel in H.

(** Given a hypothesis [H : A → B → C], [prove_parts H] will add the goals [A]
and [B] and will add the hypothesis [C] to the final goal. *)
Ltac prove_parts_base H := let H' := fresh in
    match type of H with
    | ?A → ?B => assert A as H'
    end; [> clear H | specialize (H H'); clear H'].
Ltac prove_parts H := repeat prove_parts_base H.
