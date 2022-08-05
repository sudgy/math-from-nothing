(** This file contains all of Coq's default logical types and a few basic things
related to them.  Because we pass -nois to the compiler, we need to explicitly
export these things to be able to use them.  However, I don't like a lot of the
names that Coq made for them, so I give a bunch of new names here. *)

Require Coq.Init.Logic.
Require Export Coq.Init.Ltac.
Require Export Coq.Init.Notations.
(* Even though we never use it, not requiring this makes things break? *)
Require Utf8.

Require Export notations.

Set Implicit Arguments.

Notation "x → y" := (forall (_ : x), y)
  (at level 99, y at level 200, right associativity): type_scope.

Notation "'equal'" := Coq.Init.Logic.eq.
Export Coq.Init.Logic (ex).
Export Coq.Init.Logic (ex_intro).
Export Coq.Init.Logic (iff).
Export Coq.Init.Logic (not).
Export Coq.Init.Logic (inhabited).
Export Coq.Init.Logic (all).
Export Coq.Init.Logic (f_equal).
Export Coq.Init.Logic (f_equal2).
Export Coq.Init.Logic (f_equal3).
Export Coq.Init.Logic (f_equal4).

Export Coq.Init.Logic (True).
Definition true := Coq.Init.Logic.I.
Export Coq.Init.Logic (False).
Export Coq.Init.Logic (False_rect).

Export Coq.Init.Logic (and).
Notation "'make_and'" := Coq.Init.Logic.conj.
Notation "A ∧ B" := (and A B).

Section Conjunction.

  Variables A B : Prop.

  Theorem land : A ∧ B → A.
  Proof.
    destruct 1; trivial.
  Qed.

  Theorem rand : A ∧ B → B.
  Proof.
    destruct 1; trivial.
  Qed.

End Conjunction.

Export Coq.Init.Logic (or).
Notation "'make_lor'" := Coq.Init.Logic.or_introl.
Notation "'make_ror'" := Coq.Init.Logic.or_intror.
Notation "A ∨ B" := (or A B) : type_scope.

Notation "A ↔ B" := (iff A B) : type_scope.
Notation "¬ x" := (not x) : type_scope.
Notation "x = y" := (equal x y) : type_scope.
Notation "x ≠ y" := (¬ (x = y)) : type_scope.

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

(* Logic *)
Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∀  x  ..  y ']' ,  '/' P ']'") : type_scope.
Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' ∃  x  ..  y ']' ,  '/' P ']'") : type_scope.


(* Abstraction *)
Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[  ' '[  ' 'λ'  x  ..  y ']' ,  '/' t ']'").

#[universes(template)]
Inductive ex_type (A : Type) (P : A → Prop) : Type :=
    ex_type_constr : ∀ x : A, P x → ex_type P.

Inductive strong_or (A B : Prop) : Set :=
    | strong_or_left : A → {A} + {B}
    | strong_or_right : B → {A} + {B}
where "{ A } + { B }" := (strong_or A B).

Arguments strong_or_left {A B} _, [A] B _.
Arguments strong_or_right {A B} _ , A [B] _.

#[universes(template)]
Inductive semi_or (A:Type) (B:Prop) : Type :=
  | semi_or_left : A → A + {B}
  | semi_or_right : B → A + {B}
 where "A + { B }" := (semi_or A B).

Arguments semi_or_left {A B} _ , [A] B _.
Arguments semi_or_right {A B} _ , A [B] _.
