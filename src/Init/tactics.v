(** This file contains a few tactics that can be useful at times. *)

Require Export logic.

(** Can be used to simplify expressions of the type [If H then a else b] *)
Ltac case_if :=
    let go P := destruct P; try solve [exfalso] in
    match goal with
    | |- context [if ?P then _ else _] => go P
    | K: context [if ?P then _ else _] |- _ => go P
    end.
Tactic Notation "case_if"
    "[" simple_intropattern(A) "|" simple_intropattern(B) "]" :=
    let go P := destruct P as [A|B]; try solve [exfalso] in
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
(*
Ltac prove_parts_base H := let H' := fresh in
    match type of H with
    | ?A → ?B => assert A as H'
    end; [> clear H | specialize (H H'); clear H'].
Ltac prove_parts H := repeat prove_parts_base H.
*)
Ltac prove_parts_specialize H A := let H' := fresh in
    pose (H' := H A);
    unfold H in H' + clearbody H';
    clear H;
    try clear A;
    rename H' into H.
Ltac prove_parts_base H := let H' := fresh in
    match type of H with
    | ?A → ?B => assert A as H'
    end; [> clear H | prove_parts_specialize H H'].
Ltac prove_parts H := repeat prove_parts_base H.

(** This is meant to be like [rewrite] but will actually use [change] rather
than [rewrite].  It can be useful when working with dependent types.  However,
it's not as powerful as rewrite because it can't handle theorems with
parameters. *)
Ltac def_rewrite H := match type of H with | ?a = ?b => change a with b end.

Tactic Notation "functional_intro" simple_intropattern(a)
    := try apply functional_ext; intros a.
Tactic Notation "functional_intros" simple_intropattern(a)
    := functional_intro a.
Tactic Notation "functional_intros" simple_intropattern(a)
                                    simple_intropattern(b)
    := functional_intro a; functional_intro b.
Tactic Notation "functional_intros" simple_intropattern(a)
                                    simple_intropattern(b)
                                    simple_intropattern(c)
    := functional_intro a; functional_intro b; functional_intro c.
Tactic Notation "functional_intros" simple_intropattern(a)
                                    simple_intropattern(b)
                                    simple_intropattern(c)
                                    simple_intropattern(d)
    := functional_intro a; functional_intro b;
       functional_intro c; functional_intro d.
Tactic Notation "functional_intros" simple_intropattern(a)
                                    simple_intropattern(b)
                                    simple_intropattern(c)
                                    simple_intropattern(d)
                                    simple_intropattern(e)
    := functional_intro a; functional_intro b;
       functional_intro c; functional_intro d; functional_intro e.
Tactic Notation "functional_intros" simple_intropattern(a)
                                    simple_intropattern(b)
                                    simple_intropattern(c)
                                    simple_intropattern(d)
                                    simple_intropattern(e)
                                    simple_intropattern(f)
    := functional_intro a; functional_intro b; functional_intro c;
       functional_intro d; functional_intro e; functional_intro f.
