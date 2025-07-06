Require Import init.

Require Import real.

Declare Scope complex_scope.
Delimit Scope complex_scope with complex.

Definition complex := (real * real)%type.

Definition real_to_complex a := (a, 0) : complex.
