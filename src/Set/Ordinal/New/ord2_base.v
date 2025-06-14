Require Import init.

Require Export set.
Require Export set_order.

Declare Scope ord_scope.
Delimit Scope ord_scope with ord.

Record ord_type := make_ord_type {
    ord_U :> Type;
    ord_le : Order ord_U;
    ord_antisym : Antisymmetric le;
    ord_wo : WellOrdered le;
}.

Global Existing Instances ord_le ord_antisym ord_wo.

Record ord_iso (A B : ord_type) := make_ord_iso {
    ord_iso_f :> A → B;
    ord_iso_bij : Bijective ord_iso_f;
    ord_iso_le : HomomorphismLe ord_iso_f;
}.

Global Existing Instances ord_iso_bij ord_iso_le.

Section OrdEquiv.

Let ord_eq A B := inhabited (ord_iso A B).
Local Notation "A ~ B" := (ord_eq A B).

Global Instance ord_eq_reflexive_class : Reflexive ord_eq.
Proof.
    split.
    intros A.
    split.
    exists identity.
    -   exact identity_bijective.
    -   split.
        intros a b ab.
        exact ab.
Qed.

Global Instance ord_eq_symmetric_class : Symmetric ord_eq.
Proof.
    split.
    intros A B [f].
    split.
    exists (bij_inv f).
    -   apply bij_inv_bij.
    -   split.
        intros a b ab.
        rewrite (homo_le2 (f := f)).
        do 2 rewrite bij_inv_eq2.
        exact ab.
Qed.

Global Instance ord_eq_transitive_class : Transitive ord_eq.
Proof.
    split.
    intros A B C [f] [g].
    split.
    exists (λ x, g (f x)).
    -   apply bij_comp; apply f + apply g.
    -   apply homo_le_compose; apply f + apply g.
Qed.

End OrdEquiv.
(* end hide *)
Definition ord_equiv := make_equiv _
    ord_eq_reflexive_class ord_eq_symmetric_class ord_eq_transitive_class.
Notation "a ~ b" := (eq_equal ord_equiv a b) : ord_scope.

Notation "'ord'" := (equiv_type ord_equiv).
Notation "'to_ord' A" := (to_equiv ord_equiv A) (at level 10).

Program Definition sub_ord_type {A : ord_type} (S : A → Prop) : ord_type := {|
    ord_U := set_type S;
|}.
