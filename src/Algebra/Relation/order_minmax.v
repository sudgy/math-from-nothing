Require Import init.

Require Import order_mult.

Definition min {U} `{Order U} x y :=
    If (x ≤ y) then x else y.
Definition max {U} `{Order U} x y :=
    If (x ≤ y) then y else x.

(* begin hide *)
Section MinMax.

Context {U} `{OrderedField U}.
(* end hide *)
Theorem min_comm : ∀ a b, min a b = min b a.
Proof.
    intros a b.
    unfold min.
    case_if [leq1|leq1]; case_if [leq2|leq2]; try reflexivity.
    -   apply antisym; assumption.
    -   rewrite nle_lt in leq1, leq2.
        destruct (trans leq1 leq2); contradiction.
Qed.

Theorem max_comm : ∀ a b, max a b = max b a.
Proof.
    intros a b.
    unfold max; case_if [leq1|leq1]; case_if [leq2|leq2]; try reflexivity.
    -   apply antisym; auto.
    -   rewrite nle_lt in leq1, leq2.
        destruct (trans leq1 leq2); contradiction.
Qed.

Theorem rmin : ∀ a b, min a b ≤ b.
Proof.
    intros a b.
    unfold min; case_if [leq|leq].
    -   exact leq.
    -   apply refl.
Qed.
Theorem lmin : ∀ a b, min a b ≤ a.
Proof.
    intros a b.
    rewrite min_comm.
    apply rmin.
Qed.

Theorem lmax : ∀ a b, a ≤ max a b.
Proof.
    intros a b.
    unfold max; case_if [leq|leq].
    -   apply leq.
    -   apply refl.
Qed.
Theorem rmax : ∀ a b, b ≤ max a b.
Proof.
    intros a b.
    rewrite max_comm.
    apply lmax.
Qed.

Theorem min_max_plus : ∀ a b, min a b + max a b = a + b.
Proof.
    intros a b.
    unfold min, max; case_if [leq|leq].
    -   reflexivity.
    -   apply plus_comm.
Qed.
(* begin hide *)
End MinMax.
(* end hide *)
