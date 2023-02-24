(** Basic types, like sum and product types.  While these are in the Coq
standard library, I prefer defining as much as I can on my own. *)

Require Import base_logic.

Inductive dand (A : Prop) (B : A → Prop) : Prop :=
    make_dand : ∀ a : A, B a → dand A B.
Arguments make_dand {A B}.
Notation "A ⋏ B" := (dand A B).
Definition ldand {A : Prop} {B : A → Prop} (H : A ⋏ B) : A :=
    match H with
    | make_dand a b => a
    end.
Definition rdand {A : Prop} {B : A → Prop} (H : A ⋏ B) : B (ldand H) :=
    match H with
    | make_dand a b => b
    end.

Theorem rdand_all {A : Prop} {B : A → Prop} : ∀ H : A ⋏ B, ∀ a, B a.
Proof.
    intros [a b] a'.
    rewrite (proof_irrelevance a' a).
    exact b.
Qed.

Tactic Notation "dand_split" simple_intropattern(H) :=
    match goal with | [ |- ?A ⋏ ?B ] => assert (A) as H; [>|split with H] end.
Tactic Notation "dand_split" := let H := fresh in dand_split H.

Set Implicit Arguments.

#[universes(template)]
Inductive singleton_type : Type := Single.

Theorem singleton_type_eq : ∀ a b : singleton_type, a = b.
Proof.
    intros [] [].
    reflexivity.
Qed.

#[universes(template)]
Inductive prod_type (A B:Type) : Type := pair : A → B → A * B
where "x * y" := (prod_type x y) : type_scope.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z).
Arguments pair {A B} _ _.

(* begin hide *)
Section Projections.

Context {A : Type} {B : Type}.
(* end hide *)
Definition fst (p : A * B) := match p with (x, y) => x end.
Definition snd (p : A * B) := match p with (x, y) => y end.

(* begin hide *)
End Projections.

Section Prod.

Context {A B : Type}.
(* end hide *)
Theorem prod_combine : ∀ a b : A * B, fst a = fst b → snd a = snd b → a = b.
Proof.
    intros [a1 b1] [a2 b2] eq1 eq2.
    cbn in *.
    subst.
    reflexivity.
Qed.

(* begin hide *)
End Prod.
(* end hide *)
#[universes(template)]
Inductive sum_type (A B:Type) : Type :=
  | inl : A → sum_type A B
  | inr : B → sum_type A B.

Notation "x + y" := (sum_type x y) : type_scope.
Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* begin hide *)
Section Sum.

Context {A B : Type}.
(* end hide *)
Theorem inl_eq : ∀ a b : A, (inl (B := B) a = inl b) ↔ (a = b).
Proof.
    intros a b.
    split; intro eq.
    -   inversion eq.
        reflexivity.
    -   rewrite eq.
        reflexivity.
Qed.

Theorem inr_eq : ∀ a b : B, (inr (A := A) a = inr b) ↔ (a = b).
Proof.
    intros a b.
    split; intro eq.
    -   inversion eq.
        reflexivity.
    -   rewrite eq.
        reflexivity.
Qed.

Theorem inl_neq : ∀ a b : A, (inl (B := B) a ≠ inl b) ↔ (a ≠ b).
Proof.
    intros a b.
    split; intros neq eq.
    -   rewrite eq in neq.
        contradiction.
    -   inversion eq.
        rewrite H0 in neq.
        contradiction.
Qed.

Theorem inr_neq : ∀ a b : B, (inr (A := A) a ≠ inr b) ↔ (a ≠ b).
Proof.
    intros a b.
    split; intros neq eq.
    -   rewrite eq in neq.
        contradiction.
    -   inversion eq.
        rewrite H0 in neq.
        contradiction.
Qed.
(* begin hide *)
End Sum.
(* end hide *)

#[universes(template)]
Inductive optional (A : Type) : Type :=
  | opt_val : A → optional A
  | opt_nil : optional A.

(** This doesn't really fit in Algebra so I'm putting it here.  It's an
incredibly basic concept.
*)
#[universes(template)]
Class NotTrivial U := {
    not_trivial_a : U;
    not_trivial_b : U;
    not_trivial : not_trivial_a ≠ not_trivial_b;
}.

Theorem not_trivial2 {U} `{NotTrivial U} : ∀ a : U, ∃ b, a ≠ b.
Proof.
    intros a.
    classic_case (a = not_trivial_a) as [eq|neq].
    -   exists not_trivial_b.
        rewrite eq.
        apply not_trivial.
    -   exists not_trivial_a.
        exact neq.
Qed.

Class Singleton U := {
    singleton_unique : ∃ x : U, ∀ a, a = x
}.

Theorem singleton_unique2 {U} `{Singleton U} : ∀ a b : U, a = b.
Proof.
    intros a b.
    destruct singleton_unique as [x x_uni].
    rewrite (x_uni b).
    apply x_uni.
Qed.

Theorem singleton_ex {U} : inhabited U → (∀ a b : U, a = b) → Singleton U.
Proof.
    intros [x] unique.
    split.
    exists x.
    intros a.
    apply unique.
Qed.

Theorem ex_singleton {U} : Singleton U → U.
Proof.
    intros S.
    apply indefinite_description.
    destruct singleton_unique as [x x_uni].
    exact (inhabits x).
Qed.

Declare Scope algebra_scope.
Delimit Scope algebra_scope with alg.
Open Scope algebra_scope.
