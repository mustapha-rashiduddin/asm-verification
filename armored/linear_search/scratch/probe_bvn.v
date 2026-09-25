From stdpp.bitvector Require Import definitions.
Open Scope bv_scope.

(* Can lazy unfold bvn_val/bvn_n on a bv_to_bvn constructor? *)
Eval lazy in (bvn_val (bv_to_bvn (BV 64 0))).
Eval lazy in (bvn_n (bv_to_bvn (BV 64 0))).
Axiom t : bv 64.
Eval lazy in (bvn_val (bv_to_bvn t)).
Eval cbv in (bvn_val (bv_to_bvn (BV 64 0))).