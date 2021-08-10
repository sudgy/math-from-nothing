Require Import init.

Require Import list.

Inductive ga_sign : Set :=
    | ga_pos
    | ga_neg
    | ga_null.
Definition ga_sign_mult (a b : ga_sign) :=
    match a, b with
    | ga_pos, ga_pos => ga_pos
    | ga_pos, ga_neg => ga_neg
    | ga_pos, ga_null => ga_null
    | ga_neg, ga_pos => ga_neg
    | ga_neg, ga_neg => ga_pos
    | ga_neg, ga_null => ga_null
    | ga_null, ga_pos => ga_null
    | ga_null, ga_neg => ga_null
    | ga_null, ga_null => ga_null
    end.

Theorem ga_sign_mult_assoc : ∀ a b c,
        ga_sign_mult a (ga_sign_mult b c) = ga_sign_mult (ga_sign_mult a b) c.
    intros a b c.
    destruct a, b, c; reflexivity.
Qed.
Theorem ga_sign_mult_comm : ∀ a b, ga_sign_mult a b = ga_sign_mult b a.
    intros a b.
    destruct a, b; reflexivity.
Qed.

Declare Scope ga_scope.
Delimit Scope ga_scope with ga.

Definition ga_metric (V : Type) := V → ga_sign.

Definition ga1 V := prod ga_sign (list V).

Definition ga1_mult {V} a b : (ga1 V) :=
    (ga_sign_mult (fst a) (fst b), snd a ++ snd b).
