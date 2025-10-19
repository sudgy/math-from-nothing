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

(* begin hide *)
(* This proof is not my own *)
Module ProofIrrelevance.
    Lemma prop_eq_self_impl_when_true : ∀ {P : Prop}, P → P = (P → P).
    Proof.
        intros P H.
        apply propositional_ext.
        split; intros; exact H.
    Qed.
    Record has_fixpoint (P : Prop) : Prop := has_fixpoint_make {
        has_fixpoint_F : (P → P) → P;
        has_fixpoint_fix : ∀ f, has_fixpoint_F f = f (has_fixpoint_F f)
    }.
    Lemma prop_has_fixpoint_when_true : ∀ P : Prop, P → has_fixpoint P.
    Proof.
        intros P H.
        set (P' := P).
        assert (P' = P) as P_eq by (unfold P'; reflexivity).
        pose (g1 (a : P') := a).
        pose (g2 (a : P') := a).
        assert (∀ x, g1 (g2 x) = x) as Fix by reflexivity.
        clearbody g1 g2.
        unfold P' in g1 at 2.
        unfold P' in g2 at 1.
        unfold P' in Fix.
        generalize dependent g2.
        generalize dependent g1.
        rewrite (prop_eq_self_impl_when_true H).
        subst P'.
        intros.
        set (Y := λ f, (λ x, f (g1 x x)) (g2 (λ x, f (g1 x x)))).
        apply (@has_fixpoint_make P Y).
        intros f.
        unfold Y at 1.
        rewrite Fix.
        reflexivity.
    Qed.
    Inductive boolP : Prop :=
        | trueP : boolP
        | falseP : boolP.
    Lemma trueP_eq_falseP : trueP = falseP.
    Proof.
        pose proof (@prop_has_fixpoint_when_true boolP trueP) as [Y Yfix].
        set (neg := λ b, match b with | trueP => falseP | falseP => trueP end).
        pose proof (Yfix neg) as F.
        set (b := Y neg).
        assert (b = Y neg) as E by reflexivity.
        destruct b.
        {
            change (trueP = neg trueP).
            rewrite E, <- F.
            reflexivity.
        }
        {
            change (neg falseP = falseP).
            rewrite E, <- F.
            reflexivity.
        }
    Qed.
    Theorem proof_irrelevance : ∀ {P : Prop} (a b : P), a = b.
    Proof.
        intros P a b.
        set (f := λ c, match c with trueP => a | falseP => b end).
        change a with (f trueP).
        change b with (f falseP).
        rewrite trueP_eq_falseP.
        reflexivity.
    Qed.
End ProofIrrelevance.
(* end hide *)
Export ProofIrrelevance (proof_irrelevance).

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

(* begin hide *)
(* This proof is not my own *)
Module ExcludedMiddle.
    Inductive bool : Set :=
        | true : bool
        | false : bool.
    Theorem em : ∀ (P : Prop), P ∨ ¬P.
    Proof.
        intros P.
        set (B1 b := b = true ∨ P).
        set (B2 b := b = false ∨ P).
        assert (ex B1) as H1 by (exists true; left; reflexivity).
        assert (ex B2) as H2 by (exists false; left; reflexivity).
        destruct (ex_proof H1) as [HA|]; try (left; assumption).
        destruct (ex_proof H2) as [HB|]; try (left; assumption).
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
    Theorem sem : ∀ P, {P} + {¬P}.
    Proof.
        intros P.
        apply indefinite_description.
        destruct (em P) as [PH|PH].
        -   split; left; exact PH.
        -   split; right; exact PH.
    Qed.
End ExcludedMiddle.
(* end hide *)
Export ExcludedMiddle (em).
Export ExcludedMiddle (sem).

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
