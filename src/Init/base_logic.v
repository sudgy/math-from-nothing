(** This file contains the three logical axioms and the direct consequences of
those axioms. *)

Require Export rocq_logic.
Require Export Setoid.

Set Implicit Arguments.

Axiom functional_ext : ∀ (A : Type) (B : A → Type) (f g : ∀ x, B x),
    (∀ x, f x = g x) → f = g.
Axiom propositional_ext : ∀ (P Q : Prop), P ↔ Q → P = Q.
Axiom indefinite_description : ∀ {A : Type}, inhabited A → A.

Global Instance iff_rewrite : subrelation iff equal.
Proof.
    intros A B Hequiv.
    apply propositional_ext.
    exact Hequiv.
Qed.

Theorem ex_to_type : ∀ {A : Type} {P : A → Prop}, ex P → ex_type P.
Proof.
    intros A P P_ex.
    apply indefinite_description.
    destruct P_ex as [y Py].
    split.
    exists y.
    exact Py.
Qed.

Theorem proof_irrelevance : ∀ {P : Prop} (a b : P), a = b.
Proof.
    intros P a b.
    assert (P = True) as P_eq.
    {
        apply propositional_ext.
        split.
        -   intro; exact true.
        -   intro; exact a.
    }
    subst P.
    destruct a, b.
    reflexivity.
Qed.

Theorem predicate_ext : ∀ {U : Type} (P Q : U → Prop),
    (∀ x, P x ↔ Q x) → P = Q.
Proof.
    intros U P Q H.
    apply functional_ext.
    intros x.
    specialize (H x).
    apply propositional_ext.
    exact H.
Qed.

Definition ex_type_val {A : Type} {P : A → Prop} (e : ex_type P) :
    A                 := match e with ex_type_constr _ a _ => a end.
Definition ex_type_proof {A : Type} {P : A → Prop} (e : ex_type P) :
    P (ex_type_val e) := match e with ex_type_constr _ _ b => b end.

Definition ex_val {A : Type} {P : A → Prop} (e : ex P) :=
    ex_type_val (ex_to_type e).
Definition ex_proof {A : Type} {P : A → Prop} (e : ex P) :=
    ex_type_proof (ex_to_type e).

Theorem unpack_ex_val {A : Type} {P : A → Prop} : ∀ H : ex P,
    ∃ a, ex_val H = a ∧ P a.
Proof.
    intros H.
    exists (ex_val H).
    split.
    -   reflexivity.
    -   unfold ex_val.
        destruct (ex_to_type H) as [y Py].
        cbn.
        exact Py.
Qed.

Tactic Notation "unpack_ex_val_with"
    constr(H) simple_intropattern(a) ident(b) simple_intropattern(c)
    :=
    destruct (unpack_ex_val H) as [a [b c]].

Tactic Notation "unpack_ex_val"
    simple_intropattern(a) ident(b) simple_intropattern(c)
    :=
    match goal with
    | |- context [ex_val ?H] => unpack_ex_val_with H a b c
    | K: context [ex_val ?H] |- _ => unpack_ex_val_with H a b c
    end.

Tactic Notation "rewrite_ex_val_with"
    constr(H) simple_intropattern(a) simple_intropattern(c)
    :=
    let b := fresh in
    unpack_ex_val_with H a b c;
    rewrite b in *;
    clear b.

Tactic Notation "rewrite_ex_val" simple_intropattern(a) simple_intropattern(c)
    :=
    let b := fresh in
    unpack_ex_val a b c;
    rewrite b in *;
    clear b.

Definition ex_val1 {A B : Type} {P : A → B → Prop} (e : ∃ a b, P a b) : A
    := ex_val e.
Definition ex_val2 {A B : Type} {P : A → B → Prop} (e : ∃ a b, P a b) : B
    := ex_val (ex_proof e).
Definition ex_proof2 {A B : Type} {P : A → B → Prop} (e : ∃ a b, P a b)
    : P (ex_val1 e) (ex_val2 e) := ex_proof (ex_proof e).

Theorem unpack_ex_val2 {A B : Type} {P : A → B → Prop} (e : ∃ a b, P a b) :
    ∃ a b, ex_val1 e = a ∧ ex_val2 e = b ∧ P a b.
Proof.
    exists (ex_val1 e), (ex_val2 e).
    split; [>|split]; [>reflexivity|reflexivity|].
    unfold ex_val1, ex_val2.
    unfold ex_val, ex_proof.
    destruct (ex_to_type e) as [a e']; cbn.
    destruct (ex_to_type e') as [b Pab]; cbn.
    exact Pab.
Qed.

Tactic Notation "rewrite_ex_val2" simple_intropattern(a) simple_intropattern(b)
    simple_intropattern(H)
    := let eq1 := fresh in let eq2 := fresh in
    let go P :=
        pose proof (unpack_ex_val2 P) as [a [b [eq1 [eq2 H]]]];
        rewrite eq1 in *;
        rewrite eq2 in *;
        clear eq1 eq2
    in
    match goal with
    | |- context [ex_val1 ?P] => go P
    | |- context [ex_val2 ?P] => go P
    | K: context [ex_val1 ?P] |- _ => go P
    | K: context [ex_val2 ?P] |- _ => go P
    end.

Module ExcludedMiddle.
    Inductive bool : Set :=
        | true : bool
        | false : bool.
    Theorem em : ∀ (P : Prop), P ∨ ¬P.
    Proof.
        intros P.
        pose (B1 b := b = true ∨ P).
        pose (B2 b := b = false ∨ P).
        assert (∃ x, B1 x) as H1 by (exists true; left; reflexivity).
        assert (∃ x, B2 x) as H2 by (exists false; left; reflexivity).
        destruct (ex_proof H1) as [HA|]; [>|left; assumption].
        destruct (ex_proof H2) as [HB|]; [>|left; assumption].
        right; intros HP.
        assert (B1 = B2) as EB.
        {
            apply predicate_ext.
            intros b.
            split; intros; right; exact HP.
        }
        destruct EB.
        rewrite (proof_irrelevance H2 H1) in HB.
        rewrite HB in HA.
        inversion HA.
    Qed.
End ExcludedMiddle.
Export ExcludedMiddle (em).

Theorem sem : ∀ P, {P} + {¬P}.
Proof.
    intros P.
    apply indefinite_description.
    destruct (em P) as [PH|PH].
    -   split; left; exact PH.
    -   split; right; exact PH.
Qed.

Tactic Notation "classic_case" constr(P) := destruct (sem P).
Tactic Notation "classic_case" constr(P)
    "as" "[" simple_intropattern(H1) "|" simple_intropattern(H2) "]"
    := destruct (sem P) as [H1|H2].

Notation "'If' P 'then' v1 'else' v2" :=
    (if (sem P) then v1 else v2)
    (at level 200, right associativity).

Notation "'IfH' P 'then' v1 'else' v2" :=
    match (sem P) with
    | strong_or_left H => v1 H
    | strong_or_right H => v2 H
    end
    (at level 200, right associativity).

Theorem if_true {U} : ∀ {H : Prop} {a b : U}, H → (If H then a else b) = a.
Proof.
    intros H a b P.
    destruct (sem H).
    -   reflexivity.
    -   contradiction.
Qed.

Theorem if_false {U} : ∀ {H : Prop} {a b : U}, ¬H → (If H then a else b) = b.
Proof.
    intros H a b P.
    destruct (sem H).
    -   contradiction.
    -   reflexivity.
Qed.

Theorem ifH_true {U} : ∀ {H : Prop} {v1 : H → U} {v2 : ¬H → U} (a : H),
    (IfH H then v1 else v2) = v1 a.
Proof.
    intros H v1 v2 a.
    destruct (sem H).
    -   rewrite (proof_irrelevance _ a).
        reflexivity.
    -   contradiction.
Qed.

Theorem ifH_false {U} : ∀ {H : Prop} {v1 : H → U} {v2 : ¬H → U} (a : ¬H),
    (IfH H then v1 else v2) = v2 a.
Proof.
    intros H v1 v2 a.
    destruct (sem H).
    -   contradiction.
    -   rewrite (proof_irrelevance _ a).
        reflexivity.
Qed.
