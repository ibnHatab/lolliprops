(*** ******************** ***)
(*** BLOCKS WORLD EXAMPLE ***)
(*** ******************** ***)

(* James Power * James.Power@May.ie * http://www.cs.may.ie/~jpower/ *)
(* Dept. of Computer Science, NUI Maynooth, Co. Kildare, Ireland.   *)


(* Need at least the following before this file: ILL.v, extraLL.v *)


Variable Block:Set.

(* Five predicates desribing the state:
 *   (on x y)  - true if block x is on block y
 *   (table x) - true if block x is on the table (no block beneath it)
 *   (clear x) - true if there's nothing on top of block x
 *   (holds x) - true if the robot arm holds block x
 *   empty     - true if the robot arm is empty
 *)

Variable on    : Block -> Block -> ILinProp.
Variable table : Block -> ILinProp.
Variable clear : Block -> ILinProp.
Variable holds : Block -> ILinProp.
Variable empty : ILinProp.



(* The two basic actions:
 *   get - picks up a block (from the table, or from another block)
 *   put - drops a block (on the table, or on another block)
 *)

Axiom get :
  (x,y:Block)
  (`(empty ** (clear x))
|- (holds x) ** (((table x) -o One) && ((on x y) -o (clear y)))).

Axiom put :
  (x,y:Block)
  (`(holds x)
|- empty ** (clear x) **  ((table x) && ((clear y) -o (on x y)))).


(* Now four special cases of these two actions *)

(* 1. Get a block x which is currently on some block y *)
Lemma geton :
  (x,y:Block)
  (`(empty ** (clear x) ** (on x y))  |- (holds x) ** (clear y)).
Proof.
Intros.
LeftApply TimesAssocR. LeftApply TimesComm. LeftApply TimesLeft.
LinCut (holds x)**((table x)-oOne)&&((on x y)-o(clear y)).
Apply get.
LeftApply TimesLeft.
LeftApply ExchList.
Apply TimesRight.
Apply Identity.
LeftApply WithLeft2.
Apply AddNilFront. LeftApply ExchList.
LeftApply ImpliesLeft.
Apply Identity.
(Simpl; Apply Identity).
Qed.

(* 2. Get block x which is currently on the table *)
Lemma gettb :
  (x:Block)
  (`(empty ** (clear x) ** (table x))  |- (holds x)).
Proof.
Intros.
LeftApply TimesAssocR. LeftApply TimesComm. LeftApply TimesLeft.
Cut Block; [Intros y | Auto]. (* Introduces y *)
LinCut (holds x)**((table x)-oOne)&&((on x y)-o(clear y)).
Apply get.
LeftApply TimesLeft.
Rewrite ass_app. LeftApply WithLeft1.
Rewrite app_ass. LeftApply ImpliesLeft.
Apply Identity.
LeftApply OneLeft.
Apply Identity.
Qed.

(* 3. Put block x (which the arm is holding) onto block y *)
Lemma puton :
  (x,y:Block)
  (`((holds x) ** (clear y)) |- empty ** (clear x) ** (on x y)).
Proof.
Intros.
LeftApply TimesComm. LeftApply TimesLeft.
LinCut (empty**(clear x)**(table x)&&((clear y)-o(on x y))).
Apply put.
LeftApply TimesLeft.
Rewrite ass_app. LeftApply TimesLeft.
Rewrite ass_app. LeftApply WithLeft2.
ChangeTo (`(clear y) ^ (`empty ^ `(clear x)) ^ `((clear y)-o(on x y)) |- empty ** (clear x) ** (on x y)).
LeftApply ImpliesLeft.
Apply Identity.
Rewrite app_ass.
Apply TimesRight; [ Apply Identity | (Apply TimesRight; Apply Identity)].
Qed.

(* 4. Put block x (which the arm is holding) onto the table *)
Lemma puttb :
  (x:Block)
  (`(holds x)  |- empty ** (clear x) ** (table x)).
Proof.
Intros.
Cut Block; [Intros y | Auto]. (* Introduces y *)
LinCut (empty**(clear x)**(table x)&&((clear y)-o(on x y))).
Apply put.
LeftApply TimesLeft.
Apply TimesRight.
Apply Identity.
LeftApply TimesLeft.
Apply TimesRight.
Apply Identity.
LeftApply WithLeft1.
Apply Identity.
Qed.



(*** The example: swapping the order of a and b
 *
 *          +---+                   +---+
 *          | b |                   | a |
 *          +---+                   +---+
 *          +---+  +---+            +---+  +---+
 *          | a |  | c |            | b |  | c |
 *          +---+  +---+            +---+  +---+
 *          Before State            After State
 *)


Section BlocksExample.

Variable a,b,c:Block.

(* Six auxiliary lemmas, then the main theorem SwapAB *)

(* 1. Get rid of the info relating to block C (into Top) *)
Lemma IgnoreC :
  (`(empty**(clear b)**(on b a)**(table a)**(table c)**(clear c))
 |- empty**(clear b)**(on b a)**(table a)**Top).
Proof.
Do 3 (LeftApply TimesAssocR).
Do 3 (Apply RTimesAssocR).
LinSplit.  Apply TopRight.
Qed.

(* 2. Pick up block b *)
Lemma PickUpB :
  (`(empty**(clear b)**(on b a)**(table a)**Top)
 |- (holds b)**(clear a)**(table a)**Top).
Proof.
Do 2 (LeftApply TimesAssocR).  (Apply RTimesAssocR).
LinSplit .
LeftApply TimesAssocL; Apply geton.
Qed.

(* 3. Drop block b onto the table *)
Lemma DropB :
  (`((holds b)**(clear a)**(table a)**Top)
 |- empty**(table b)**(clear b)**(clear a)**(table a)**Top).
Proof.
Do 2 (Apply RTimesAssocR).
LinSplit.
LinCut empty**(clear b)**(table b).
Apply puttb.
Apply RTimesAssocL; LinSplit.
LeftApply TimesComm; Apply Identity.
Qed.

(* 4. Pick up block a *)
Lemma PickUpA :
  (`(empty**(table b)**(clear b)**(clear a)**(table a)**Top)
 |- (table b)**(clear b)**(holds a)**Top).
Proof.
LeftApply TimesComm.
LeftApply TimesAssocL. LinSplit.
LeftApply TimesAssocL. LinSplit.
LeftApply TimesComm. Do 2 (LeftApply TimesAssocR). LinSplit.
LeftApply TimesAssocL.
Apply gettb.
Qed.

(* 5. Drop block a onto block b *)
Lemma DropA :
  (`((table b)**(clear b)**(holds a)**Top)
|- (table b)**empty**(on a b)**(clear a)**Top).
Proof.
LinSplit.
LeftApply TimesAssocR. Do 2 (Apply RTimesAssocR). LinSplit.
LinCut (empty ** (clear a) ** (on a b)).
LeftApply TimesComm; Apply puton.
Apply RTimesAssocL.
LinSplit.
Apply RTimesComm.
Apply Identity.
Qed.

(* 6. Get rid of extra info into Top *)
Lemma TidyUp :
  (`((table b)**empty**(on a b)**(clear a)**Top)
 |- (on a b)**Top).
Proof.
Do 2 (LeftApply TimesAssocR). LeftApply TimesComm.
LeftApply TimesAssocR. LeftApply TimesComm.
LeftApply TimesLeft.
LinSplit.
Apply TopRight.
Qed.


(* The theorem: cut-and-apply _forwards_ through the states *)

Theorem SwapAB :
  (`(empty ** (clear b) ** (on b a) ** (table a) ** (table c) ** (clear c))
|-
  (on a b) ** Top).
Proof.
LinCut ((empty)**(clear b)**(on b a)**(table a)**Top).
Apply IgnoreC.
LinCut ((holds b)**(clear a)**(table a)**Top).
Apply PickUpB.
LinCut (empty**(table b)**(clear b)**(clear a)**(table a)**Top).
Apply DropB.
LinCut ((table b)**(clear b)**(holds a)**Top).
Apply PickUpA.
LinCut ((table b)**empty**(on a b)**(clear a)**Top).
Apply DropA.
Apply TidyUp.
Qed.

End BlocksExample.
