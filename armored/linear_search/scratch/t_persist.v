Require Import isla.aarch64.aarch64.

Section t.
Context `{!islaG Σ} `{!threadG}.
Variable P : iProp Σ.

Lemma instr_pre_pers : Persistent (instr_pre 0 P).
Proof. apply _. Qed.
End t.
