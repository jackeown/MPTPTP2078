%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:36 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :  101 ( 101 expanded)
%              Number of leaves         :  101 ( 101 expanded)
%              Depth                    :    0
%              Number of atoms          :  174 ( 174 expanded)
%              Number of equality atoms :   32 (  32 expanded)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u134,negated_conjecture,
    ( r1_tarski(sK1,k3_tarski(k1_xboole_0)) )).

cnf(u128,negated_conjecture,
    ( r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u57,axiom,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2)) )).

cnf(u56,axiom,
    ( r1_tarski(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X1,X1,X1,X1,X2)) )).

cnf(u55,axiom,
    ( r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2)) )).

cnf(u113,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u58,axiom,
    ( r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X2)) )).

cnf(u67,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u96,axiom,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )).

cnf(u48,axiom,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )).

cnf(u303,negated_conjecture,
    ( ~ r1_tarski(X6,k1_xboole_0)
    | k1_xboole_0 = X6 )).

cnf(u54,axiom,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k3_enumset1(X2,X2,X2,X2,X2) = X0
    | k3_enumset1(X1,X1,X1,X1,X2) = X0
    | k1_xboole_0 = X0 )).

cnf(u34,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u118,axiom,
    ( r1_xboole_0(k1_xboole_0,X2) )).

cnf(u78,axiom,
    ( r1_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X1)) )).

cnf(u24,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u169,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK1)
    | r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) )).

cnf(u166,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0)))
    | r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) )).

cnf(u162,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_tarski(k3_enumset1(X8,X8,X8,X8,sK1)))
    | r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) )).

cnf(u140,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_tarski(k1_xboole_0))
    | ~ r2_hidden(X0,sK1) )).

cnf(u180,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_tarski(k1_xboole_0))
    | k1_xboole_0 = sK1 )).

cnf(u209,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_tarski(k1_xboole_0))
    | r1_xboole_0(sK1,sK1) )).

cnf(u281,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_tarski(k1_xboole_0))
    | r1_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X6))) )).

cnf(u309,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k3_tarski(k1_xboole_0))
    | r1_xboole_0(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,sK1))) )).

cnf(u165,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK0)
    | r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u163,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X0)))
    | r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u161,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_tarski(k3_enumset1(X7,X7,X7,X7,sK0)))
    | r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u133,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | ~ r2_hidden(X0,sK0) )).

cnf(u216,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | k1_xboole_0 = sK0 )).

cnf(u223,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | r1_xboole_0(sK0,sK0) )).

cnf(u282,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | r1_xboole_0(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X7))) )).

cnf(u310,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | r1_xboole_0(sK0,k3_tarski(k3_enumset1(X7,X7,X7,X7,sK0))) )).

cnf(u428,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X15,X15,X15,X15,X15),k3_tarski(k3_enumset1(k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X15,X15,X15,X15,X15),X17)))
    | r1_xboole_0(k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X16,X16,X16,X16,X15)) )).

cnf(u429,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X18,X18,X18,X18,X18),k3_tarski(k3_enumset1(k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X18),X20)))
    | r1_xboole_0(k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X19)) )).

cnf(u338,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X3,X3,X3,X3,X3))))
    | r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X4,X4,X4,X4,X3)) )).

cnf(u350,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_tarski(k3_enumset1(X6,X6,X6,X6,k3_enumset1(X4,X4,X4,X4,X4))))
    | r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X5)) )).

cnf(u337,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1))
    | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1)) )).

cnf(u349,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X2))
    | r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X3)) )).

cnf(u386,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))
    | k1_xboole_0 = k3_enumset1(X0,X0,X0,X0,X0) )).

cnf(u399,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X2))
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0)) )).

cnf(u387,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X3))
    | r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X2)) )).

cnf(u389,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X7,X7,X7,X7,X8))
    | r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_tarski(k3_enumset1(X9,X9,X9,X9,k3_enumset1(X7,X7,X7,X7,X7)))) )).

cnf(u503,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X2))
    | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) )).

cnf(u388,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X5))
    | r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_tarski(k3_enumset1(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),X6))) )).

cnf(u380,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0))
    | k1_xboole_0 = k3_enumset1(X0,X0,X0,X0,X0) )).

cnf(u400,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X5,X5,X5,X5,X3))
    | r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X4,X4,X4,X4,X3)) )).

cnf(u381,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X3,X3,X3,X3,X2))
    | r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X2)) )).

cnf(u383,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X8,X8,X8,X8,X7))
    | r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_tarski(k3_enumset1(X9,X9,X9,X9,k3_enumset1(X7,X7,X7,X7,X7)))) )).

cnf(u504,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X5,X5,X5,X5,X3))
    | r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X3,X3,X3,X3,X4)) )).

cnf(u382,axiom,
    ( ~ r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X5,X5,X5,X5,X4))
    | r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_tarski(k3_enumset1(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),X6))) )).

cnf(u265,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u263,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k3_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X0)))
    | r1_xboole_0(X1,X2) )).

cnf(u159,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_tarski(k3_enumset1(X4,X4,X4,X4,k3_xboole_0(X2,X3))))
    | r1_xboole_0(X2,X3) )).

cnf(u158,axiom,
    ( ~ r1_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
    | k1_xboole_0 = X0 )).

cnf(u160,axiom,
    ( ~ r1_xboole_0(X5,k3_tarski(k3_enumset1(X6,X6,X6,X6,X5)))
    | r1_xboole_0(X5,X5) )).

cnf(u257,axiom,
    ( ~ r1_xboole_0(X4,k3_tarski(k3_enumset1(X6,X6,X6,X6,X4)))
    | r1_xboole_0(X4,k3_tarski(k3_enumset1(X4,X4,X4,X4,X5))) )).

cnf(u258,axiom,
    ( ~ r1_xboole_0(X7,k3_tarski(k3_enumset1(X9,X9,X9,X9,X7)))
    | r1_xboole_0(X7,k3_tarski(k3_enumset1(X8,X8,X8,X8,X7))) )).

cnf(u93,axiom,
    ( ~ r1_xboole_0(X2,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))
    | ~ r2_hidden(X4,X2) )).

cnf(u178,axiom,
    ( ~ r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
    | k1_xboole_0 = X1 )).

cnf(u207,axiom,
    ( ~ r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
    | r1_xboole_0(X1,X1) )).

cnf(u279,axiom,
    ( ~ r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
    | r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))) )).

cnf(u307,axiom,
    ( ~ r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
    | r1_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) )).

cnf(u69,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | ~ r2_hidden(X1,X0) )).

cnf(u182,axiom,
    ( ~ r1_xboole_0(X1,X1)
    | k1_xboole_0 = X1 )).

cnf(u268,axiom,
    ( ~ r1_xboole_0(X2,X2)
    | r1_xboole_0(X2,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) )).

cnf(u269,axiom,
    ( ~ r1_xboole_0(X4,X4)
    | r1_xboole_0(X4,k3_tarski(k3_enumset1(X5,X5,X5,X5,X4))) )).

cnf(u60,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u74,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) )).

cnf(u364,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k3_enumset1(X2,X2,X2,X2,k3_xboole_0(X0,X1)))) )).

cnf(u354,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X2))) )).

cnf(u139,negated_conjecture,
    ( r2_hidden(sK4(sK1,k3_tarski(k1_xboole_0)),sK1)
    | r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) )).

cnf(u137,negated_conjecture,
    ( r2_hidden(sK4(sK0,k3_tarski(k1_xboole_0)),sK0)
    | r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u351,axiom,
    ( r2_hidden(sK4(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X7,X7,X7,X7,X8)),k3_enumset1(X7,X7,X7,X7,X7))
    | r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X7,X7,X7,X7,X8)) )).

cnf(u339,axiom,
    ( r2_hidden(sK4(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X7,X7,X7,X7,X6)),k3_enumset1(X6,X6,X6,X6,X6))
    | r1_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X7,X7,X7,X7,X6)) )).

cnf(u156,axiom,
    ( r2_hidden(sK4(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))),X1)
    | r1_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) )).

cnf(u92,axiom,
    ( r2_hidden(sK4(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),X0)
    | r1_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )).

cnf(u73,axiom,
    ( r2_hidden(sK4(X1,X1),X1)
    | r1_xboole_0(X1,X1) )).

cnf(u33,axiom,
    ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u27,axiom,
    ( r2_hidden(sK3(X0),X0)
    | k1_xboole_0 = X0 )).

cnf(u340,axiom,
    ( ~ r2_hidden(X10,k3_enumset1(X8,X8,X8,X8,X8))
    | ~ r1_xboole_0(k3_enumset1(X8,X8,X8,X8,X8),k3_enumset1(X9,X9,X9,X9,X8)) )).

cnf(u352,axiom,
    ( ~ r2_hidden(X11,k3_enumset1(X9,X9,X9,X9,X9))
    | ~ r1_xboole_0(k3_enumset1(X9,X9,X9,X9,X9),k3_enumset1(X9,X9,X9,X9,X10)) )).

cnf(u64,axiom,
    ( ~ r2_hidden(X1,k1_xboole_0) )).

cnf(u32,axiom,
    ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
    | ~ r1_xboole_0(X0,X1) )).

cnf(u101,axiom,
    ( ~ r2_hidden(X12,X10)
    | ~ r1_xboole_0(X10,k3_tarski(k3_enumset1(X11,X11,X11,X11,X10))) )).

cnf(u136,negated_conjecture,
    ( sK1 = k3_xboole_0(sK1,k3_tarski(k1_xboole_0)) )).

cnf(u131,negated_conjecture,
    ( sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u102,axiom,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X13)) = X13 )).

cnf(u47,axiom,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 )).

cnf(u227,axiom,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) )).

cnf(u185,axiom,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0)) )).

cnf(u49,axiom,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) )).

cnf(u234,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) )).

cnf(u190,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) )).

cnf(u125,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1) )).

cnf(u86,negated_conjecture,
    ( k1_xboole_0 = sK2 )).

cnf(u115,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X1)) )).

cnf(u62,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u99,axiom,
    ( k3_xboole_0(X6,k3_tarski(k3_enumset1(X7,X7,X7,X7,X6))) = X6 )).

cnf(u66,axiom,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 )).

cnf(u68,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (6919)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.46  % (6927)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.47  % (6927)Refutation not found, incomplete strategy% (6927)------------------------------
% 0.20/0.47  % (6927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6919)Refutation not found, incomplete strategy% (6919)------------------------------
% 0.20/0.47  % (6919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (6919)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (6919)Memory used [KB]: 10618
% 0.20/0.47  % (6919)Time elapsed: 0.065 s
% 0.20/0.47  % (6919)------------------------------
% 0.20/0.47  % (6919)------------------------------
% 0.20/0.47  % (6927)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (6927)Memory used [KB]: 11001
% 0.20/0.47  % (6927)Time elapsed: 0.057 s
% 0.20/0.47  % (6927)------------------------------
% 0.20/0.47  % (6927)------------------------------
% 0.20/0.51  % (6917)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (6916)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (6917)Refutation not found, incomplete strategy% (6917)------------------------------
% 0.20/0.51  % (6917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (6917)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (6917)Memory used [KB]: 10618
% 0.20/0.51  % (6917)Time elapsed: 0.109 s
% 0.20/0.51  % (6917)------------------------------
% 0.20/0.51  % (6917)------------------------------
% 0.20/0.51  % (6913)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (6930)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (6933)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (6908)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (6908)Refutation not found, incomplete strategy% (6908)------------------------------
% 0.20/0.52  % (6908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6908)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (6908)Memory used [KB]: 1663
% 0.20/0.52  % (6908)Time elapsed: 0.116 s
% 0.20/0.52  % (6908)------------------------------
% 0.20/0.52  % (6908)------------------------------
% 0.20/0.52  % (6915)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (6922)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (6911)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (6925)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (6912)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (6910)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (6912)Refutation not found, incomplete strategy% (6912)------------------------------
% 0.20/0.53  % (6912)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6912)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6912)Memory used [KB]: 6140
% 0.20/0.53  % (6912)Time elapsed: 0.120 s
% 0.20/0.53  % (6912)------------------------------
% 0.20/0.53  % (6912)------------------------------
% 0.20/0.53  % (6916)Refutation not found, incomplete strategy% (6916)------------------------------
% 0.20/0.53  % (6916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6916)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6916)Memory used [KB]: 10618
% 0.20/0.53  % (6916)Time elapsed: 0.117 s
% 0.20/0.53  % (6916)------------------------------
% 0.20/0.53  % (6916)------------------------------
% 0.20/0.53  % (6913)Refutation not found, incomplete strategy% (6913)------------------------------
% 0.20/0.53  % (6913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6909)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (6910)Refutation not found, incomplete strategy% (6910)------------------------------
% 0.20/0.53  % (6910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6910)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6910)Memory used [KB]: 10746
% 0.20/0.53  % (6910)Time elapsed: 0.118 s
% 0.20/0.53  % (6910)------------------------------
% 0.20/0.53  % (6910)------------------------------
% 0.20/0.53  % (6934)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (6930)Refutation not found, incomplete strategy% (6930)------------------------------
% 0.20/0.53  % (6930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6926)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (6937)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (6914)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (6923)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (6936)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (6924)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (6931)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (6929)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (6925)Refutation not found, incomplete strategy% (6925)------------------------------
% 0.20/0.53  % (6925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6935)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (6930)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6930)Memory used [KB]: 10746
% 0.20/0.53  % (6930)Time elapsed: 0.104 s
% 0.20/0.53  % (6930)------------------------------
% 0.20/0.53  % (6930)------------------------------
% 0.20/0.54  % (6933)Refutation not found, incomplete strategy% (6933)------------------------------
% 0.20/0.54  % (6933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6925)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6925)Memory used [KB]: 10618
% 0.20/0.54  % (6925)Time elapsed: 0.136 s
% 0.20/0.54  % (6925)------------------------------
% 0.20/0.54  % (6925)------------------------------
% 0.20/0.54  % (6932)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (6933)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6933)Memory used [KB]: 6268
% 0.20/0.54  % (6933)Time elapsed: 0.136 s
% 0.20/0.54  % (6933)------------------------------
% 0.20/0.54  % (6933)------------------------------
% 0.20/0.54  % (6937)Refutation not found, incomplete strategy% (6937)------------------------------
% 0.20/0.54  % (6937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6923)Refutation not found, incomplete strategy% (6923)------------------------------
% 0.20/0.54  % (6923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6923)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6923)Memory used [KB]: 6140
% 0.20/0.54  % (6923)Time elapsed: 0.003 s
% 0.20/0.54  % (6923)------------------------------
% 0.20/0.54  % (6923)------------------------------
% 0.20/0.54  % (6921)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (6920)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (6913)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6913)Memory used [KB]: 6268
% 0.20/0.54  % (6913)Time elapsed: 0.111 s
% 0.20/0.55  % (6913)------------------------------
% 0.20/0.55  % (6913)------------------------------
% 0.20/0.55  % (6915)Refutation not found, incomplete strategy% (6915)------------------------------
% 0.20/0.55  % (6915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6918)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (6929)Refutation not found, incomplete strategy% (6929)------------------------------
% 0.20/0.55  % (6929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6929)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6929)Memory used [KB]: 1663
% 0.20/0.55  % (6929)Time elapsed: 0.140 s
% 0.20/0.55  % (6929)------------------------------
% 0.20/0.55  % (6929)------------------------------
% 0.20/0.55  % (6918)Refutation not found, incomplete strategy% (6918)------------------------------
% 0.20/0.55  % (6918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6918)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6918)Memory used [KB]: 10618
% 0.20/0.55  % (6918)Time elapsed: 0.141 s
% 0.20/0.55  % (6918)------------------------------
% 0.20/0.55  % (6918)------------------------------
% 0.20/0.55  % (6911)Refutation not found, incomplete strategy% (6911)------------------------------
% 0.20/0.55  % (6911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6911)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6911)Memory used [KB]: 10874
% 0.20/0.55  % (6911)Time elapsed: 0.124 s
% 0.20/0.55  % (6911)------------------------------
% 0.20/0.55  % (6911)------------------------------
% 0.20/0.55  % (6928)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (6937)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6937)Memory used [KB]: 1918
% 0.20/0.55  % (6937)Time elapsed: 0.137 s
% 0.20/0.55  % (6937)------------------------------
% 0.20/0.55  % (6937)------------------------------
% 0.20/0.55  % (6928)Refutation not found, incomplete strategy% (6928)------------------------------
% 0.20/0.55  % (6928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (6928)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (6928)Memory used [KB]: 10746
% 0.20/0.55  % (6928)Time elapsed: 0.148 s
% 0.20/0.55  % (6928)------------------------------
% 0.20/0.55  % (6928)------------------------------
% 0.20/0.56  % (6920)Refutation not found, incomplete strategy% (6920)------------------------------
% 0.20/0.56  % (6920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (6915)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (6915)Memory used [KB]: 6524
% 0.20/0.56  % (6915)Time elapsed: 0.128 s
% 0.20/0.56  % (6915)------------------------------
% 0.20/0.56  % (6915)------------------------------
% 0.20/0.57  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.57  % (6938)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.20/0.57  % (6914)# SZS output start Saturation.
% 0.20/0.57  cnf(u134,negated_conjecture,
% 0.20/0.57      r1_tarski(sK1,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u128,negated_conjecture,
% 0.20/0.57      r1_tarski(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u57,axiom,
% 0.20/0.57      r1_tarski(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u56,axiom,
% 0.20/0.57      r1_tarski(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X1,X1,X1,X1,X2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u55,axiom,
% 0.20/0.57      r1_tarski(k3_enumset1(X1,X1,X1,X1,X2),k3_enumset1(X1,X1,X1,X1,X2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u113,axiom,
% 0.20/0.57      r1_tarski(k1_xboole_0,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u58,axiom,
% 0.20/0.57      r1_tarski(k1_xboole_0,k3_enumset1(X1,X1,X1,X1,X2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u67,axiom,
% 0.20/0.57      r1_tarski(X0,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u96,axiom,
% 0.20/0.57      r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u48,axiom,
% 0.20/0.57      r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u303,negated_conjecture,
% 0.20/0.57      ~r1_tarski(X6,k1_xboole_0) | k1_xboole_0 = X6).
% 0.20/0.57  
% 0.20/0.57  cnf(u54,axiom,
% 0.20/0.57      ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X2)) | k3_enumset1(X1,X1,X1,X1,X1) = X0 | k3_enumset1(X2,X2,X2,X2,X2) = X0 | k3_enumset1(X1,X1,X1,X1,X2) = X0 | k1_xboole_0 = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u34,axiom,
% 0.20/0.57      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u118,axiom,
% 0.20/0.57      r1_xboole_0(k1_xboole_0,X2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u78,axiom,
% 0.20/0.57      r1_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u24,axiom,
% 0.20/0.57      r1_xboole_0(X0,k1_xboole_0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u169,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,sK1) | r1_xboole_0(sK1,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u166,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X0))) | r1_xboole_0(sK1,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u162,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,k3_tarski(k3_enumset1(X8,X8,X8,X8,sK1))) | r1_xboole_0(sK1,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u140,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) | ~r2_hidden(X0,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u180,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) | k1_xboole_0 = sK1).
% 0.20/0.57  
% 0.20/0.57  cnf(u209,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) | r1_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u281,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) | r1_xboole_0(sK1,k3_tarski(k3_enumset1(sK1,sK1,sK1,sK1,X6)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u309,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK1,k3_tarski(k1_xboole_0)) | r1_xboole_0(sK1,k3_tarski(k3_enumset1(X6,X6,X6,X6,sK1)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u165,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,sK0) | r1_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u163,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X0))) | r1_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u161,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,k3_tarski(k3_enumset1(X7,X7,X7,X7,sK0))) | r1_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u133,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) | ~r2_hidden(X0,sK0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u216,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) | k1_xboole_0 = sK0).
% 0.20/0.57  
% 0.20/0.57  cnf(u223,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) | r1_xboole_0(sK0,sK0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u282,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) | r1_xboole_0(sK0,k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X7)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u310,negated_conjecture,
% 0.20/0.57      ~r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) | r1_xboole_0(sK0,k3_tarski(k3_enumset1(X7,X7,X7,X7,sK0)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u428,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X15,X15,X15,X15,X15),k3_tarski(k3_enumset1(k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X15,X15,X15,X15,X15),X17))) | r1_xboole_0(k3_enumset1(X15,X15,X15,X15,X15),k3_enumset1(X16,X16,X16,X16,X15))).
% 0.20/0.57  
% 0.20/0.57  cnf(u429,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X18,X18,X18,X18,X18),k3_tarski(k3_enumset1(k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X18),X20))) | r1_xboole_0(k3_enumset1(X18,X18,X18,X18,X18),k3_enumset1(X18,X18,X18,X18,X19))).
% 0.20/0.57  
% 0.20/0.57  cnf(u338,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_tarski(k3_enumset1(X5,X5,X5,X5,k3_enumset1(X3,X3,X3,X3,X3)))) | r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X4,X4,X4,X4,X3))).
% 0.20/0.57  
% 0.20/0.57  cnf(u350,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_tarski(k3_enumset1(X6,X6,X6,X6,k3_enumset1(X4,X4,X4,X4,X4)))) | r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X5))).
% 0.20/0.57  
% 0.20/0.57  cnf(u337,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)) | r1_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X2,X2,X2,X2,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u349,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X2)) | r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X3))).
% 0.20/0.57  
% 0.20/0.57  cnf(u386,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1)) | k1_xboole_0 = k3_enumset1(X0,X0,X0,X0,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u399,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X2)) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u387,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X3)) | r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u389,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X7,X7,X7,X7,X8)) | r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_tarski(k3_enumset1(X9,X9,X9,X9,k3_enumset1(X7,X7,X7,X7,X7))))).
% 0.20/0.57  
% 0.20/0.57  cnf(u503,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X2)) | r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u388,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X5)) | r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_tarski(k3_enumset1(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),X6)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u380,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0)) | k1_xboole_0 = k3_enumset1(X0,X0,X0,X0,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u400,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X5,X5,X5,X5,X3)) | r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X4,X4,X4,X4,X3))).
% 0.20/0.57  
% 0.20/0.57  cnf(u381,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X3,X3,X3,X3,X2)) | r1_xboole_0(k3_enumset1(X2,X2,X2,X2,X2),k3_enumset1(X2,X2,X2,X2,X2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u383,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X8,X8,X8,X8,X7)) | r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_tarski(k3_enumset1(X9,X9,X9,X9,k3_enumset1(X7,X7,X7,X7,X7))))).
% 0.20/0.57  
% 0.20/0.57  cnf(u504,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X5,X5,X5,X5,X3)) | r1_xboole_0(k3_enumset1(X3,X3,X3,X3,X3),k3_enumset1(X3,X3,X3,X3,X4))).
% 0.20/0.57  
% 0.20/0.57  cnf(u382,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X5,X5,X5,X5,X4)) | r1_xboole_0(k3_enumset1(X4,X4,X4,X4,X4),k3_tarski(k3_enumset1(k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),k3_enumset1(X4,X4,X4,X4,X4),X6)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u265,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u263,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k3_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X0))) | r1_xboole_0(X1,X2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u159,axiom,
% 0.20/0.57      ~r1_xboole_0(k3_xboole_0(X2,X3),k3_tarski(k3_enumset1(X4,X4,X4,X4,k3_xboole_0(X2,X3)))) | r1_xboole_0(X2,X3)).
% 0.20/0.57  
% 0.20/0.57  cnf(u158,axiom,
% 0.20/0.57      ~r1_xboole_0(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | k1_xboole_0 = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u160,axiom,
% 0.20/0.57      ~r1_xboole_0(X5,k3_tarski(k3_enumset1(X6,X6,X6,X6,X5))) | r1_xboole_0(X5,X5)).
% 0.20/0.57  
% 0.20/0.57  cnf(u257,axiom,
% 0.20/0.57      ~r1_xboole_0(X4,k3_tarski(k3_enumset1(X6,X6,X6,X6,X4))) | r1_xboole_0(X4,k3_tarski(k3_enumset1(X4,X4,X4,X4,X5)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u258,axiom,
% 0.20/0.57      ~r1_xboole_0(X7,k3_tarski(k3_enumset1(X9,X9,X9,X9,X7))) | r1_xboole_0(X7,k3_tarski(k3_enumset1(X8,X8,X8,X8,X7)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u93,axiom,
% 0.20/0.57      ~r1_xboole_0(X2,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3))) | ~r2_hidden(X4,X2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u178,axiom,
% 0.20/0.57      ~r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | k1_xboole_0 = X1).
% 0.20/0.57  
% 0.20/0.57  cnf(u207,axiom,
% 0.20/0.57      ~r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | r1_xboole_0(X1,X1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u279,axiom,
% 0.20/0.57      ~r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u307,axiom,
% 0.20/0.57      ~r1_xboole_0(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | r1_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u69,axiom,
% 0.20/0.57      ~r1_xboole_0(X0,X0) | ~r2_hidden(X1,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u182,axiom,
% 0.20/0.57      ~r1_xboole_0(X1,X1) | k1_xboole_0 = X1).
% 0.20/0.57  
% 0.20/0.57  cnf(u268,axiom,
% 0.20/0.57      ~r1_xboole_0(X2,X2) | r1_xboole_0(X2,k3_tarski(k3_enumset1(X2,X2,X2,X2,X3)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u269,axiom,
% 0.20/0.57      ~r1_xboole_0(X4,X4) | r1_xboole_0(X4,k3_tarski(k3_enumset1(X5,X5,X5,X5,X4)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u60,axiom,
% 0.20/0.57      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.20/0.57  
% 0.20/0.57  cnf(u74,axiom,
% 0.20/0.57      ~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u364,axiom,
% 0.20/0.57      ~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k3_enumset1(X2,X2,X2,X2,k3_xboole_0(X0,X1))))).
% 0.20/0.57  
% 0.20/0.57  cnf(u354,axiom,
% 0.20/0.57      ~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k3_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X2)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u139,negated_conjecture,
% 0.20/0.57      r2_hidden(sK4(sK1,k3_tarski(k1_xboole_0)),sK1) | r1_xboole_0(sK1,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u137,negated_conjecture,
% 0.20/0.57      r2_hidden(sK4(sK0,k3_tarski(k1_xboole_0)),sK0) | r1_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u351,axiom,
% 0.20/0.57      r2_hidden(sK4(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X7,X7,X7,X7,X8)),k3_enumset1(X7,X7,X7,X7,X7)) | r1_xboole_0(k3_enumset1(X7,X7,X7,X7,X7),k3_enumset1(X7,X7,X7,X7,X8))).
% 0.20/0.57  
% 0.20/0.57  cnf(u339,axiom,
% 0.20/0.57      r2_hidden(sK4(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X7,X7,X7,X7,X6)),k3_enumset1(X6,X6,X6,X6,X6)) | r1_xboole_0(k3_enumset1(X6,X6,X6,X6,X6),k3_enumset1(X7,X7,X7,X7,X6))).
% 0.20/0.57  
% 0.20/0.57  cnf(u156,axiom,
% 0.20/0.57      r2_hidden(sK4(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))),X1) | r1_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u92,axiom,
% 0.20/0.57      r2_hidden(sK4(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))),X0) | r1_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u73,axiom,
% 0.20/0.57      r2_hidden(sK4(X1,X1),X1) | r1_xboole_0(X1,X1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u33,axiom,
% 0.20/0.57      r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u27,axiom,
% 0.20/0.57      r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u340,axiom,
% 0.20/0.57      ~r2_hidden(X10,k3_enumset1(X8,X8,X8,X8,X8)) | ~r1_xboole_0(k3_enumset1(X8,X8,X8,X8,X8),k3_enumset1(X9,X9,X9,X9,X8))).
% 0.20/0.57  
% 0.20/0.57  cnf(u352,axiom,
% 0.20/0.57      ~r2_hidden(X11,k3_enumset1(X9,X9,X9,X9,X9)) | ~r1_xboole_0(k3_enumset1(X9,X9,X9,X9,X9),k3_enumset1(X9,X9,X9,X9,X10))).
% 0.20/0.57  
% 0.20/0.57  cnf(u64,axiom,
% 0.20/0.57      ~r2_hidden(X1,k1_xboole_0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u32,axiom,
% 0.20/0.57      ~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u101,axiom,
% 0.20/0.57      ~r2_hidden(X12,X10) | ~r1_xboole_0(X10,k3_tarski(k3_enumset1(X11,X11,X11,X11,X10)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u136,negated_conjecture,
% 0.20/0.57      sK1 = k3_xboole_0(sK1,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u131,negated_conjecture,
% 0.20/0.57      sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u102,axiom,
% 0.20/0.57      k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X13)) = X13).
% 0.20/0.57  
% 0.20/0.57  cnf(u47,axiom,
% 0.20/0.57      k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u227,axiom,
% 0.20/0.57      k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u185,axiom,
% 0.20/0.57      k3_enumset1(X0,X0,X0,X0,X0) = k3_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u49,axiom,
% 0.20/0.57      k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u234,negated_conjecture,
% 0.20/0.57      k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u190,negated_conjecture,
% 0.20/0.57      k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u125,negated_conjecture,
% 0.20/0.57      k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u86,negated_conjecture,
% 0.20/0.57      k1_xboole_0 = sK2).
% 0.20/0.57  
% 0.20/0.57  cnf(u115,axiom,
% 0.20/0.57      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u61,axiom,
% 0.20/0.57      k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_enumset1(X0,X0,X0,X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u62,axiom,
% 0.20/0.57      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u99,axiom,
% 0.20/0.57      k3_xboole_0(X6,k3_tarski(k3_enumset1(X7,X7,X7,X7,X6))) = X6).
% 0.20/0.57  
% 0.20/0.57  cnf(u66,axiom,
% 0.20/0.57      k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u68,axiom,
% 0.20/0.57      k3_xboole_0(X0,X0) = X0).
% 0.20/0.57  
% 0.20/0.57  % (6914)# SZS output end Saturation.
% 0.20/0.57  % (6914)------------------------------
% 0.20/0.57  % (6914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (6914)Termination reason: Satisfiable
% 0.20/0.57  
% 0.20/0.57  % (6914)Memory used [KB]: 6524
% 0.20/0.57  % (6914)Time elapsed: 0.144 s
% 0.20/0.57  % (6914)------------------------------
% 0.20/0.57  % (6914)------------------------------
% 0.20/0.58  % (6907)Success in time 0.209 s
%------------------------------------------------------------------------------
