Require Import Logic List ListSet Arith Peano_dec Omega Ensembles.
Require Import Finite_sets_facts Finite_sets Relation_Definitions.
Require Import Relation_Operators.
Require Import strictorder set_rep_equiv util.
Require Import finite_set_builder strandlib.
Require Import LibTactics.

Require Import strandspace.

Module NSLSpace.

Open Scope list_scope.
Import ListNotations.
Open Scope ss_scope.

(* Names and Nonces *)
Variable A B Na Nb : Text.
  Hypothesis neqANa : A <> Na.
  Hypothesis neqANb : A <> Nb.
  Hypothesis neqBNa : B <> Na.
  Hypothesis neqBNb : B <> Nb.
(* "Public" and "Private" keys *)
Variable Ka Kb Ka' Kb' : Key.
  Hypothesis keyinj : Ka = Kb -> A = B.
  Hypothesis Ka_inv : Inv Ka Ka'.
  Hypothesis Kb_inv : Inv Kb Kb'.

(* Self-communication in this protocol is nonsensical *)
Hypothesis neqAB : A <> B. 

Lemma neqKaKb : Ka <> Kb.
Proof.
  intros contra. 
  apply keyinj in contra.
  apply neqAB. auto.
Qed.

Definition NSLInitiator : Strand :=  
  [(+ {(!Na) * (!A)}^[Kb]) ; 
   (- {(!Na) * (!Nb) * (!B)}^[Ka]) ;
   (+ {(!Nb)}^[Kb])].

Definition NSLResponder : Strand :=  
  [(- {(!Na) * (!A)}^[Kb]) ; 
   (+ {(!Na) * (!Nb) * (!B)}^[Ka]) ;
   (- {(!Nb)}^[Kb])].

Hypothesis NSLProtocol : 
  Protocol = [NSLInitiator ; NSLResponder].

Hypothesis neqNaNb : Na <> Nb.

Hypothesis uqNb: UniqOrigin (!Nb).

Variable Kp : set Key.

Hypothesis Ka_inv_not_in_Kp : ~(exists Ka_1, set_In Ka_1 Kp /\ Inv Ka Ka_1).

Definition s1:Strand := cons (+ (! Na)) nil.
Check s1.

Definition xp := snd (s1, 0) < length (fst (s1,0)).
Check xp.
Check sig.

Definition P (n:Strand*nat) : Prop := snd n < length (fst n).

(*Definition n1 := exist (fun n: (Strand*nat) => snd n < length (fst n))
                            (s1, 0) (snd (s1, 0) < length (fst (s1,0))).


Lemma Nb_originates_at_n0 : Origin (!Nb) .
*)

End NSLSpace.

Export NSLSpace.