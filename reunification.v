(******************************************************************************)
(*                                                                            *)
(*                  Reunification: Doctrinal Dispute Resolution               *)
(*                                                                            *)
(*     Formalizes the theological divergences between Catholic and            *)
(*     Protestant doctrine that Leibniz sought to reconcile: Filioque         *)
(*     clause, transubstantiation vs. consubstantiation, justification        *)
(*     by faith, Marian dogmas, and papal authority. Encodes the Council      *)
(*     of Trent and the Augsburg Confession as formal objects.                *)
(*                                                                            *)
(*     "Quo facto, quando orientur controversiae, non magis disputatione      *)
(*     opus erit inter duos philosophos, quam inter duos Computistas.         *)
(*     Sufficiet enim calamos in manus sumere sedereque ad abacos, et         *)
(*     sibi mutuo dicere: Calculemus."                                        *)
(*     -- Gottfried Wilhelm Leibniz, 1685                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 2026                                                     *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

