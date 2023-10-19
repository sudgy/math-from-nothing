Require Import init.

Require Import order_mult.

Definition min {U} `{Order U} x y :=
    If (x ≤ y) then x else y.
Definition max {U} `{Order U} x y :=
    If (x ≤ y) then y else x.

(* begin hide *)
Section MinMax.

Context {U} `{OrderedFieldClass U}.
(* end hide *)
Theorem min_leq : ∀ a b, a ≤ b → min a b = a.
Proof.
    intros a b leq.
    unfold min; case_if [leq'|leq'].
    -   reflexivity.
    -   contradiction.
Qed.
Theorem min_req : ∀ a b, b ≤ a → min a b = b.
Proof.
    intros a b leq.
    unfold min; case_if [leq'|leq'].
    -   exact (antisym leq' leq).
    -   reflexivity.
Qed.
Theorem max_leq : ∀ a b, b ≤ a → max a b = a.
Proof.
    intros a b leq.
    unfold max; case_if [leq'|leq'].
    -   exact (antisym leq leq').
    -   reflexivity.
Qed.
Theorem max_req : ∀ a b, a ≤ b → max a b = b.
Proof.
    intros a b leq.
    unfold max; case_if [leq'|leq'].
    -   reflexivity.
    -   contradiction.
Qed.

Theorem min_comm : ∀ a b, min a b = min b a.
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite min_leq, min_req by exact leq.
        reflexivity.
    -   rewrite min_req, min_leq by exact leq.
        reflexivity.
Qed.

Theorem max_comm : ∀ a b, max a b = max b a.
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite max_req, max_leq by exact leq.
        reflexivity.
    -   rewrite max_leq, max_req by exact leq.
        reflexivity.
Qed.

Theorem min_assoc : ∀ a b c, min a (min b c) = min (min a b) c.
Proof.
    intros a b c.
    destruct (connex a b) as [ab|ab].
    -   rewrite (min_leq a b ab).
        destruct (connex b c) as [bc|bc].
        +   rewrite (min_leq b c bc).
            rewrite (min_leq a b ab).
            rewrite (min_leq a c (trans ab bc)).
            reflexivity.
        +   rewrite (min_req b c bc).
            reflexivity.
    -   rewrite (min_req a b ab).
        destruct (connex b c) as [bc|bc].
        +   rewrite (min_leq b c bc).
            exact (min_req a b ab).
        +   rewrite (min_req b c bc).
            exact (min_req a c (trans bc ab)).
Qed.

Theorem max_assoc : ∀ a b c, max a (max b c) = max (max a b) c.
Proof.
    intros a b c.
    destruct (connex a b) as [ab|ab].
    -   rewrite (max_req a b ab).
        destruct (connex b c) as [bc|bc].
        +   rewrite (max_req b c bc).
            exact (max_req a c (trans ab bc)).
        +   rewrite (max_leq b c bc).
            exact (max_req a b ab).
    -   rewrite (max_leq a b ab).
        destruct (connex b c) as [bc|bc].
        +   rewrite (max_req b c bc).
            reflexivity.
        +   rewrite (max_leq b c bc).
            rewrite (max_leq a c (trans bc ab)).
            exact (max_leq a b ab).
Qed.

Theorem rmin : ∀ a b, min a b ≤ b.
Proof.
    intros a b.
    destruct (connex a b) as [ab|ab].
    -   rewrite (min_leq a b ab).
        exact ab.
    -   rewrite (min_req a b ab).
        apply refl.
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
    destruct (connex a b) as [ab|ab].
    -   rewrite (max_req a b ab).
        exact ab.
    -   rewrite (max_leq a b ab).
        apply refl.
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
    destruct (connex a b) as [ab|ab].
    -   rewrite (min_leq a b ab), (max_req a b ab).
        reflexivity.
    -   rewrite (min_req a b ab), (max_leq a b ab).
        apply plus_comm.
Qed.
(* begin hide *)
End MinMax.
(* end hide *)

Section MinMaxHomo.

Context {U V} `{TotalOrder U, TotalOrder V}.
Context (f : U → V) `{@HomomorphismLe2 U V UO UO0 f}.

Theorem homo_min : ∀ a b, f (min a b) = min (f a) (f b).
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite (min_leq _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (min_leq _ _ leq).
        reflexivity.
    -   rewrite (min_req _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (min_req _ _ leq).
        reflexivity.
Qed.

Theorem homo_max : ∀ a b, f (max a b) = max (f a) (f b).
Proof.
    intros a b.
    destruct (connex a b) as [leq|leq].
    -   rewrite (max_req _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (max_req _ _ leq).
        reflexivity.
    -   rewrite (max_leq _ _ leq).
        rewrite homo_le2 in leq.
        rewrite (max_leq _ _ leq).
        reflexivity.
Qed.

End MinMaxHomo.
