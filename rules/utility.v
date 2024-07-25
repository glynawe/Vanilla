Require Import Coq.Lists.List.

Lemma Forall2_refl X R l : 
  (forall x : X, In x l -> R x x) -> Forall2 R l l.
Proof.
  rewrite <- Forall_forall.
  induction 1; auto.
Qed.

Lemma same_either_way : forall {T: Type} (c: bool) (a: T),
  (if c then a else a) = a.
Proof.
  intros. destruct c; reflexivity.
Qed.

