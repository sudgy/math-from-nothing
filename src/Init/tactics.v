Require Export logic.
(* TODO: Figure this out *)
(*
Ltac unpack_ex_val a b :=
    match goal with
    | |- context [@ex_val ?A ?B ?P] =>
        pose (a := @ex_val A B P);
        assert (P a) as b by admit
    | K: context [@ex_val ?A ?B ?P] |- _ =>
        pose (a := @ex_val A B P);
        assert (P a) as b by admit
    end;
    fold a in *.
*)
(* begin show *)
(*
Ltac old_unpack_ex_val a b :=
    unfold ex_val, ex_type_val;
    match goal with
    | |- context [@ex_to_type ?A ?B ?P] => destruct (@ex_to_type A B P) as [a b]
    | K: context [@ex_to_type ?A ?B ?P] |- _ => destruct (ex_to_type A B P) as [a b]
    end.
*)
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
(* end show *)

Tactic Notation "not_simpl" "in" ident(H) :=
    repeat (
        try rewrite not_not in H;
        try rewrite not_impl in H;
        try rewrite not_and in H;
        try rewrite not_or in H;
        try rewrite not_ex in H;
        try rewrite not_all in H
    ).

(* begin show *)
Ltac exfalso := elimtype False.
(* end show *)

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
