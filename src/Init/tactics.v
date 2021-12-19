Require Export logic.

Ltac case_if :=
    let go P := destruct P; try solve [elimtype False] in
    match goal with
    | |- context [if ?P then _ else _] => go P
    | K: context [if ?P then _ else _] |- _ => go P
    end.

(* TODO: USE SETOID_REWRITE *)
Ltac not_simpl :=
    repeat (
        try rewrite not_not;
        try rewrite not_impl;
        try rewrite not_and;
        try rewrite not_or;
        try rewrite not_ex;
        try rewrite not_all
    ).

Tactic Notation "not_simpl" "in" ident(H) :=
    repeat (
        try rewrite not_not in H;
        try rewrite not_impl in H;
        try rewrite not_and in H;
        try rewrite not_or in H;
        try rewrite not_ex in H;
        try rewrite not_all in H
    ).

Ltac exfalso := elimtype False.

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

Ltac prove_parts_base H := let H' := fresh in
    match type of H with
    | ?A → ?B => assert A as H'
    end; [> clear H | specialize (H H'); clear H'].
Ltac prove_parts H := repeat prove_parts_base H.
