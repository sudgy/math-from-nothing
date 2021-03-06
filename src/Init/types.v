Require Import base_logic.

Set Implicit Arguments.

#[universes(template)]
Inductive singleton_type : Type := Single.

Theorem singleton_eq : ∀ a b : singleton_type, a = b.
    intros [] [].
    reflexivity.
Qed.

#[universes(template)]
Inductive prod (A B:Type) : Type := pair : A → B → A * B
where "x * y" := (prod x y) : type_scope.

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
Theorem prod_combine : ∀ a b : prod A B, fst a = fst b → snd a = snd b → a = b.
    intros [a1 b1] [a2 b2] eq1 eq2.
    cbn in *.
    subst.
    reflexivity.
Qed.

(* begin hide *)
End Prod.
(* end hide *)
#[universes(template)]
Inductive sum (A B:Type) : Type :=
  | inl : A → sum A B
  | inr : B → sum A B.

Notation "x + y" := (sum x y) : type_scope.
Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(* begin hide *)
Section Sum.

Context {A B : Type}.
(* end hide *)
Theorem inl_eq : ∀ a b : A, (inl (B := B) a = inl b) = (a = b).
    intros a b.
    apply propositional_ext.
    split; intro eq.
    -   inversion eq.
        reflexivity.
    -   rewrite eq.
        reflexivity.
Qed.

Theorem inr_eq : ∀ a b : B, (inr (A := A) a = inr b) = (a = b).
    intros a b.
    apply propositional_ext.
    split; intro eq.
    -   inversion eq.
        reflexivity.
    -   rewrite eq.
        reflexivity.
Qed.

Theorem inl_neq : ∀ a b : A, (inl (B := B) a ≠ inl b) = (a ≠ b).
    intros a b.
    apply propositional_ext.
    split; intros neq eq.
    -   rewrite eq in neq.
        contradiction.
    -   inversion eq.
        rewrite H0 in neq.
        contradiction.
Qed.

Theorem inr_neq : ∀ a b : B, (inr (A := A) a ≠ inr b) = (a ≠ b).
    intros a b.
    apply propositional_ext.
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
    intros a.
    classic_case (a = not_trivial_a) as [eq|neq].
    -   exists not_trivial_b.
        rewrite eq.
        apply not_trivial.
    -   exists not_trivial_a.
        exact neq.
Qed.
