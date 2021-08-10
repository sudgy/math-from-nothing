Require Import init.

Require Import order_mult.

Definition min {U} `{Order U} x y :=
    If (x <= y) then x else y.
Definition max {U} `{Order U} x y :=
    If (x <= y) then y else x.

(* begin hide *)
Section MinMax.

Context {U} `{P : Plus U,
                 @PlusAssoc U P,
                 @PlusComm U P,
              Z : Zero U,
                 @PlusLid U P Z,
                 @PlusRid U P Z,
              N : Neg U,
                 @PlusLinv U P Z N,
                 @PlusRinv U P Z N,
              M : Mult U,
                 @MultAssoc U M,
                 @MultComm U M,
                 @Ldist U P M,
                 @Rdist U P M,
              O : One U,
                 @MultLid U M O,
                 @MultRid U M O,
                 @NotTrivial U Z O,
              R : Order U,
                 @Antisymmetric U le,
                 @Transitive U le,
                 @Connex U le,
                 @OrderLplus U P R,
                 @OrderRplus U P R,
                 @OrderPlusLcancel U P R,
                 @OrderPlusRcancel U P R,
                 @OrderMult U Z M R,
                 @OrderLmult U Z M R,
                 @OrderRmult U Z M R,
                 @OrderMultLcancel U Z M R,
                 @OrderMultRcancel U Z M R
             }.
(* end hide *)

Theorem min_comm : ∀ a b, min a b = min b a.
    intros a b.
    unfold min; do 2 case_if; try reflexivity.
    -   apply antisym; auto.
    -   rewrite nle_lt in n.
        rewrite nle_lt in n0.
        apply antisym.
        +   apply n.
        +   apply n0.
Qed.

Theorem max_comm : ∀ a b, max a b = max b a.
    intros a b.
    unfold max; do 2 case_if; try reflexivity.
    -   apply antisym; auto.
    -   rewrite nle_lt in n.
        rewrite nle_lt in n0.
        apply antisym.
        +   apply n0.
        +   apply n.
Qed.

Theorem lmin : ∀ a b, min a b <= a.
    intros a b.
    unfold min; case_if.
    -   apply refl.
    -   rewrite nle_lt in n.
        apply n.
Qed.
Theorem rmin : ∀ a b, min a b <= b.
    intros a b.
    rewrite min_comm.
    apply lmin.
Qed.

Theorem lmax : ∀ a b, a <= max a b.
    intros a b.
    unfold max; case_if; auto.
    apply refl.
Qed.
Theorem rmax : ∀ a b, b <= max a b.
    intros a b.
    rewrite max_comm.
    apply lmax.
Qed.

End MinMax.
