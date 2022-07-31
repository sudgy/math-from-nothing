Require Import init.

Require Export mult_ring.

(** Alright, I lied, these are just records and not categories.  I'll make
categories later (maybe).
*)

Record RngObj := make_rng {
    rng_U : Type;
    rng_plus : Plus rng_U;
    rng_zero : Zero rng_U;
    rng_neg : Neg rng_U;
    rng_mult : Mult rng_U;
    rng_plus_assoc : @PlusAssoc rng_U rng_plus;
    rng_plus_comm : @PlusComm rng_U rng_plus;
    rng_plus_lid : @PlusLid rng_U rng_plus rng_zero;
    rng_plus_linv : @PlusLinv rng_U rng_plus rng_zero rng_neg;
    rng_mult_assoc : @MultAssoc rng_U rng_mult;
    rng_ldist : @Ldist rng_U rng_plus rng_mult;
    rng_rdist : @Rdist rng_U rng_plus rng_mult;
}.

Record RingObj := make_ring {
    ring_rng : RngObj;
    ring_one : One (rng_U ring_rng);
    ring_mult_lid : @MultLid (rng_U ring_rng) (rng_mult ring_rng) ring_one;
    ring_mult_rid : @MultRid (rng_U ring_rng) (rng_mult ring_rng) ring_one;
}.
Definition ring_U R := rng_U (ring_rng R).
Definition ring_plus R := rng_plus (ring_rng R).
Definition ring_zero R := rng_zero (ring_rng R).
Definition ring_neg R := rng_neg (ring_rng R).
Definition ring_mult R := rng_mult (ring_rng R).
Definition ring_plus_assoc R := rng_plus_assoc (ring_rng R).
Definition ring_plus_comm R := rng_plus_comm (ring_rng R).
Definition ring_plus_lid R := rng_plus_lid (ring_rng R).
Definition ring_plus_linv R := rng_plus_linv (ring_rng R).
Definition ring_mult_assoc R := rng_mult_assoc (ring_rng R).
Definition ring_ldist R := rng_ldist (ring_rng R).
Definition ring_rdist R := rng_rdist (ring_rng R).

Record CRingObj := make_cring {
    cring_ring : RingObj;
    cring_mult_comm : @MultComm (ring_U cring_ring) (ring_mult cring_ring);
}.
Definition cring_U R := ring_U (cring_ring R).
Definition cring_plus R := ring_plus (cring_ring R).
Definition cring_zero R := ring_zero (cring_ring R).
Definition cring_neg R := ring_neg (cring_ring R).
Definition cring_mult R := ring_mult (cring_ring R).
Definition cring_plus_assoc R := ring_plus_assoc (cring_ring R).
Definition cring_plus_comm R := ring_plus_comm (cring_ring R).
Definition cring_plus_lid R := ring_plus_lid (cring_ring R).
Definition cring_plus_linv R := ring_plus_linv (cring_ring R).
Definition cring_mult_assoc R := ring_mult_assoc (cring_ring R).
Definition cring_ldist R := ring_ldist (cring_ring R).
Definition cring_one R := ring_one (cring_ring R).
Definition cring_mult_lid R := ring_mult_lid (cring_ring R).
