%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:07 EST 2020

% Result     : CounterSatisfiable 3.19s
% Output     : Saturation 3.19s
% Verified   : 
% Statistics : Number of clauses        :  148 ( 148 expanded)
%              Number of leaves         :  148 ( 148 expanded)
%              Depth                    :    0
%              Number of atoms          :  238 ( 238 expanded)
%              Number of equality atoms :   72 (  72 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u1351,axiom,
    ( r1_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X13),k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14)) )).

cnf(u1345,axiom,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )).

cnf(u92,axiom,
    ( r1_tarski(k1_xboole_0,X6) )).

cnf(u176,axiom,
    ( r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) )).

cnf(u59,axiom,
    ( r1_tarski(k3_xboole_0(X1,X0),X0) )).

cnf(u30,axiom,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) )).

cnf(u39,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u3171,axiom,
    ( r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k3_xboole_0(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44)))
    | X44 = X45 )).

cnf(u2892,axiom,
    ( r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45)))
    | X44 = X45 )).

cnf(u1352,axiom,
    ( r1_xboole_0(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X15),k5_xboole_0(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16),k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X15))) )).

cnf(u1348,axiom,
    ( r1_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) )).

cnf(u56,axiom,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 )).

cnf(u1360,axiom,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X33),k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32)),k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32)) )).

cnf(u1359,axiom,
    ( r1_xboole_0(k5_xboole_0(k6_enumset1(X30,X30,X30,X30,X30,X30,X30,X30),k6_enumset1(X30,X30,X30,X30,X30,X30,X30,X31)),k6_enumset1(X30,X30,X30,X30,X30,X30,X30,X30)) )).

cnf(u451,axiom,
    ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10)),k3_xboole_0(X9,X10)) )).

cnf(u234,axiom,
    ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X25,X26),X26),k3_xboole_0(X25,X26)) )).

cnf(u185,axiom,
    ( r1_xboole_0(k5_xboole_0(k3_xboole_0(X20,X21),X20),k3_xboole_0(X20,X21)) )).

cnf(u235,axiom,
    ( r1_xboole_0(k5_xboole_0(X28,k3_xboole_0(X27,X28)),k3_xboole_0(X27,X28)) )).

cnf(u186,axiom,
    ( r1_xboole_0(k5_xboole_0(X22,k3_xboole_0(X22,X23)),k3_xboole_0(X22,X23)) )).

cnf(u146,axiom,
    ( r1_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X3,X2)) )).

cnf(u145,axiom,
    ( r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) )).

cnf(u98,axiom,
    ( r1_xboole_0(k1_xboole_0,X0) )).

cnf(u3388,axiom,
    ( r1_xboole_0(k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45)),k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45)))
    | X44 = X45 )).

cnf(u2752,axiom,
    ( r1_xboole_0(k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45)),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45))
    | X44 = X45 )).

cnf(u1776,axiom,
    ( r1_xboole_0(k3_xboole_0(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34),k6_enumset1(X35,X35,X35,X35,X35,X35,X35,X35)),k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34))
    | X34 = X35 )).

cnf(u293,axiom,
    ( r1_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X8,X9))) )).

cnf(u226,axiom,
    ( r1_xboole_0(k3_xboole_0(X7,X8),k5_xboole_0(k3_xboole_0(X7,X8),X8)) )).

cnf(u179,axiom,
    ( r1_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(k3_xboole_0(X6,X7),X6)) )).

cnf(u230,axiom,
    ( r1_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X17,k3_xboole_0(X16,X17))) )).

cnf(u63,axiom,
    ( r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1)) )).

cnf(u183,axiom,
    ( r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,k3_xboole_0(X15,X16))) )).

cnf(u32,axiom,
    ( r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) )).

cnf(u1942,axiom,
    ( r1_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X8,X7))
    | k1_xboole_0 != k3_xboole_0(X7,X8) )).

cnf(u1986,axiom,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
    | k3_xboole_0(X1,X0) != k1_xboole_0 )).

cnf(u1759,axiom,
    ( r1_xboole_0(k3_xboole_0(X2,X3),X2)
    | k1_xboole_0 != k3_xboole_0(X3,X2) )).

cnf(u2074,axiom,
    ( r1_xboole_0(X13,k3_xboole_0(X14,X13))
    | k1_xboole_0 != k3_xboole_0(X13,X14) )).

cnf(u1915,axiom,
    ( r1_xboole_0(X12,k3_xboole_0(X12,X11))
    | k1_xboole_0 != k3_xboole_0(X11,X12) )).

cnf(u138,axiom,
    ( r1_xboole_0(X6,k1_xboole_0) )).

cnf(u40,axiom,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 )).

cnf(u147,axiom,
    ( r1_xboole_0(X4,X5)
    | k1_xboole_0 != k3_xboole_0(X5,X4) )).

cnf(u4441,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )).

cnf(u1868,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44))
    | r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44)) )).

cnf(u5262,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
    | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )).

cnf(u1389,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94),k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94))
    | r1_xboole_0(k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94),k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X95)) )).

cnf(u1390,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X96),k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X96))
    | r1_xboole_0(k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X97),k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X96)) )).

cnf(u4442,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5))
    | r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) )).

cnf(u1901,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45))
    | r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44)) )).

cnf(u5263,axiom,
    ( ~ r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5))
    | r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) )).

cnf(u524,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X15))
    | ~ r2_hidden(X16,k3_xboole_0(X14,X15)) )).

cnf(u539,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10))
    | r1_xboole_0(k3_xboole_0(X9,X10),X9) )).

cnf(u542,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X16))
    | r1_xboole_0(k3_xboole_0(X15,X16),X16) )).

cnf(u557,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10))
    | r1_xboole_0(X9,k3_xboole_0(X9,X10)) )).

cnf(u560,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X16))
    | r1_xboole_0(X16,k3_xboole_0(X15,X16)) )).

cnf(u534,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X1,X0),X0)
    | r1_xboole_0(X0,X1) )).

cnf(u552,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X1,X0),X0)
    | r1_xboole_0(X1,X0) )).

cnf(u1729,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X2,X3),X3)
    | r1_xboole_0(k3_xboole_0(X2,X3),X2) )).

cnf(u1884,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X11,X12),X12)
    | r1_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12)) )).

cnf(u2842,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X8,X9),X9)
    | r1_xboole_0(X8,k3_xboole_0(X8,X9)) )).

cnf(u517,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X0)
    | r1_xboole_0(X0,X1) )).

cnf(u518,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X2,X3),X2)
    | r1_xboole_0(X3,X2) )).

cnf(u1878,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X1,X0),X1)
    | r1_xboole_0(k3_xboole_0(X1,X0),X0) )).

cnf(u1883,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X9,X10),X9)
    | r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10)) )).

cnf(u2982,axiom,
    ( ~ r1_xboole_0(k3_xboole_0(X1,X0),X1)
    | r1_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u620,axiom,
    ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X0))
    | r1_xboole_0(X0,X1) )).

cnf(u638,axiom,
    ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X0))
    | r1_xboole_0(X1,X0) )).

cnf(u1728,axiom,
    ( ~ r1_xboole_0(X1,k3_xboole_0(X0,X1))
    | r1_xboole_0(k3_xboole_0(X0,X1),X0) )).

cnf(u1851,axiom,
    ( ~ r1_xboole_0(X12,k3_xboole_0(X11,X12))
    | r1_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12)) )).

cnf(u2843,axiom,
    ( ~ r1_xboole_0(X11,k3_xboole_0(X10,X11))
    | r1_xboole_0(X10,k3_xboole_0(X10,X11)) )).

cnf(u603,axiom,
    ( ~ r1_xboole_0(X0,k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u604,axiom,
    ( ~ r1_xboole_0(X2,k3_xboole_0(X2,X3))
    | r1_xboole_0(X3,X2) )).

cnf(u1845,axiom,
    ( ~ r1_xboole_0(X1,k3_xboole_0(X1,X0))
    | r1_xboole_0(k3_xboole_0(X1,X0),X0) )).

cnf(u1850,axiom,
    ( ~ r1_xboole_0(X9,k3_xboole_0(X9,X10))
    | r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10)) )).

cnf(u3017,axiom,
    ( ~ r1_xboole_0(X1,k3_xboole_0(X1,X0))
    | r1_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u3335,axiom,
    ( ~ r1_xboole_0(X3,X2)
    | r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) )).

cnf(u3334,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) )).

cnf(u3118,axiom,
    ( ~ r1_xboole_0(X2,X3)
    | r1_xboole_0(X2,k3_xboole_0(X3,X2)) )).

cnf(u3117,axiom,
    ( ~ r1_xboole_0(X1,X0)
    | r1_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u2839,axiom,
    ( ~ r1_xboole_0(X3,X2)
    | r1_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u2838,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u2699,axiom,
    ( ~ r1_xboole_0(X3,X2)
    | r1_xboole_0(k3_xboole_0(X2,X3),X3) )).

cnf(u2698,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X1) )).

cnf(u1733,axiom,
    ( ~ r1_xboole_0(X10,X11)
    | r1_xboole_0(k3_xboole_0(X10,X11),X10) )).

cnf(u1732,axiom,
    ( ~ r1_xboole_0(X9,X8)
    | r1_xboole_0(k3_xboole_0(X8,X9),X8) )).

cnf(u140,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u41,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u1358,axiom,
    ( r2_hidden(sK2(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29),k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X28)),k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X28))
    | r1_xboole_0(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29),k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X28)) )).

cnf(u1350,axiom,
    ( r2_hidden(sK2(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11))
    | r1_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)) )).

cnf(u755,axiom,
    ( r2_hidden(sK2(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12)),k3_xboole_0(X11,X12))
    | r1_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12)) )).

cnf(u228,axiom,
    ( r2_hidden(sK2(k3_xboole_0(X12,X13),X13),k3_xboole_0(X12,X13))
    | r1_xboole_0(k3_xboole_0(X12,X13),X13) )).

cnf(u181,axiom,
    ( r2_hidden(sK2(k3_xboole_0(X11,X12),X11),k3_xboole_0(X11,X12))
    | r1_xboole_0(k3_xboole_0(X11,X12),X11) )).

cnf(u324,axiom,
    ( r2_hidden(sK2(X12,k3_xboole_0(X13,X12)),k3_xboole_0(X13,X12))
    | r1_xboole_0(X12,k3_xboole_0(X13,X12)) )).

cnf(u274,axiom,
    ( r2_hidden(sK2(X11,k3_xboole_0(X11,X12)),k3_xboole_0(X11,X12))
    | r1_xboole_0(X11,k3_xboole_0(X11,X12)) )).

cnf(u125,axiom,
    ( r2_hidden(sK2(X0,X1),k3_xboole_0(X1,X0))
    | r1_xboole_0(X0,X1) )).

cnf(u37,axiom,
    ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u1349,axiom,
    ( ~ r2_hidden(X10,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8))
    | ~ r1_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)) )).

cnf(u1353,axiom,
    ( ~ r2_hidden(X19,k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17))
    | ~ r1_xboole_0(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)) )).

cnf(u95,axiom,
    ( ~ r2_hidden(X5,k1_xboole_0) )).

cnf(u5100,axiom,
    ( ~ r2_hidden(X10,k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)))
    | X8 = X9 )).

cnf(u2379,axiom,
    ( ~ r2_hidden(X10,k3_xboole_0(X9,X8))
    | k1_xboole_0 != k3_xboole_0(X8,X9) )).

cnf(u231,axiom,
    ( ~ r2_hidden(X20,k3_xboole_0(X18,X19))
    | ~ r1_xboole_0(X19,k3_xboole_0(X18,X19)) )).

cnf(u227,axiom,
    ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
    | ~ r1_xboole_0(k3_xboole_0(X9,X10),X10) )).

cnf(u184,axiom,
    ( ~ r2_hidden(X19,k3_xboole_0(X17,X18))
    | ~ r1_xboole_0(X17,k3_xboole_0(X17,X18)) )).

cnf(u180,axiom,
    ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
    | ~ r1_xboole_0(k3_xboole_0(X8,X9),X8) )).

cnf(u73,axiom,
    ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
    | ~ r1_xboole_0(X0,X1) )).

cnf(u36,axiom,
    ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
    | ~ r1_xboole_0(X0,X1) )).

cnf(u3576,negated_conjecture,
    ( sK0 = sK1 )).

cnf(u1343,axiom,
    ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )).

cnf(u55,axiom,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )).

cnf(u28,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u3618,negated_conjecture,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

cnf(u3570,axiom,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(X170,X170,X170,X170,X170,X170,X170,X170),k3_xboole_0(k6_enumset1(X171,X171,X171,X171,X171,X171,X171,X171),k6_enumset1(X170,X170,X170,X170,X170,X170,X170,X170)))
    | X170 = X171 )).

cnf(u3572,axiom,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(X165,X165,X165,X165,X165,X165,X165,X165),k3_xboole_0(k6_enumset1(X165,X165,X165,X165,X165,X165,X165,X165),k6_enumset1(X164,X164,X164,X164,X164,X164,X164,X164)))
    | X164 = X165 )).

cnf(u1357,axiom,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X26),k5_xboole_0(k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X27),k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X26))) )).

cnf(u1356,axiom,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X24),k5_xboole_0(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X24),k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25))) )).

cnf(u340,axiom,
    ( k1_xboole_0 = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | X2 = X3 )).

cnf(u1362,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37),k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X36)),k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X36)) )).

cnf(u1361,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34),k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)),k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34)) )).

cnf(u766,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k3_xboole_0(X34,X35),k3_xboole_0(X34,X35)),k3_xboole_0(X34,X35)) )).

cnf(u376,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k3_xboole_0(X15,X16),X16),k3_xboole_0(X15,X16)) )).

cnf(u373,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(k3_xboole_0(X9,X10),X9),k3_xboole_0(X9,X10)) )).

cnf(u372,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,k3_xboole_0(X8,X7)),k3_xboole_0(X8,X7)) )).

cnf(u371,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(X5,k3_xboole_0(X5,X6)),k3_xboole_0(X5,X6)) )).

cnf(u159,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X3,X2)) )).

cnf(u151,axiom,
    ( k1_xboole_0 = k3_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3)) )).

cnf(u96,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u3569,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k6_enumset1(X176,X176,X176,X176,X176,X176,X176,X176),k6_enumset1(X175,X175,X175,X175,X175,X175,X175,X175)),k3_xboole_0(k6_enumset1(X176,X176,X176,X176,X176,X176,X176,X176),k6_enumset1(X175,X175,X175,X175,X175,X175,X175,X175)))
    | X175 = X176 )).

cnf(u3571,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k6_enumset1(X169,X169,X169,X169,X169,X169,X169,X169),k6_enumset1(X168,X168,X168,X168,X168,X168,X168,X168)),k6_enumset1(X168,X168,X168,X168,X168,X168,X168,X168))
    | X168 = X169 )).

cnf(u3573,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(k6_enumset1(X159,X159,X159,X159,X159,X159,X159,X159),k6_enumset1(X158,X158,X158,X158,X158,X158,X158,X158)),k6_enumset1(X159,X159,X159,X159,X159,X159,X159,X159))
    | X158 = X159 )).

cnf(u761,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X24,X25),k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X24,X25))) )).

cnf(u233,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X23,X24),k5_xboole_0(k3_xboole_0(X23,X24),X24)) )).

cnf(u198,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(k3_xboole_0(X6,X7),X6)) )).

cnf(u245,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X13,k3_xboole_0(X12,X13))) )).

cnf(u78,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2)) )).

cnf(u242,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X6,k3_xboole_0(X6,X7))) )).

cnf(u77,axiom,
    ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) )).

cnf(u106,axiom,
    ( k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) )).

cnf(u172,axiom,
    ( k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) )).

cnf(u220,axiom,
    ( k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) )).

cnf(u173,axiom,
    ( k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u76,axiom,
    ( k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) )).

cnf(u75,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0) )).

cnf(u31,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u167,axiom,
    ( k1_xboole_0 != k3_xboole_0(X2,X3)
    | k1_xboole_0 = k3_xboole_0(X3,X2) )).

cnf(u1916,axiom,
    ( k1_xboole_0 != k3_xboole_0(X13,X14)
    | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X14,X13),X14) )).

cnf(u2029,axiom,
    ( k1_xboole_0 != k3_xboole_0(X15,X16)
    | k1_xboole_0 = k3_xboole_0(X16,k3_xboole_0(X16,X15)) )).

cnf(u2075,axiom,
    ( k1_xboole_0 != k3_xboole_0(X15,X16)
    | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X16,X15),X15) )).

cnf(u2121,axiom,
    ( k1_xboole_0 != k3_xboole_0(X15,X16)
    | k1_xboole_0 = k3_xboole_0(X15,k3_xboole_0(X16,X15)) )).

cnf(u2383,axiom,
    ( k1_xboole_0 != k3_xboole_0(X17,X18)
    | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X18,X17),k3_xboole_0(X18,X17)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:41:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (29075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (29067)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (29067)Refutation not found, incomplete strategy% (29067)------------------------------
% 0.21/0.50  % (29067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29075)Refutation not found, incomplete strategy% (29075)------------------------------
% 0.21/0.50  % (29075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29075)Memory used [KB]: 1663
% 0.21/0.50  % (29075)Time elapsed: 0.057 s
% 0.21/0.50  % (29075)------------------------------
% 0.21/0.50  % (29075)------------------------------
% 0.21/0.51  % (29067)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29067)Memory used [KB]: 6140
% 0.21/0.51  % (29067)Time elapsed: 0.005 s
% 0.21/0.51  % (29067)------------------------------
% 0.21/0.51  % (29067)------------------------------
% 0.21/0.51  % (29059)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (29058)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (29057)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (29081)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (29056)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (29063)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (29074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (29052)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (29052)Refutation not found, incomplete strategy% (29052)------------------------------
% 0.21/0.53  % (29052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29052)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29052)Memory used [KB]: 1663
% 0.21/0.53  % (29052)Time elapsed: 0.114 s
% 0.21/0.53  % (29052)------------------------------
% 0.21/0.53  % (29052)------------------------------
% 0.21/0.53  % (29073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (29073)Refutation not found, incomplete strategy% (29073)------------------------------
% 0.21/0.53  % (29073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29073)Memory used [KB]: 1663
% 0.21/0.53  % (29073)Time elapsed: 0.124 s
% 0.21/0.53  % (29073)------------------------------
% 0.21/0.53  % (29073)------------------------------
% 0.21/0.53  % (29068)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29065)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (29053)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (29077)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (29055)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29080)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (29066)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (29060)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (29061)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (29060)Refutation not found, incomplete strategy% (29060)------------------------------
% 0.21/0.54  % (29060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29060)Memory used [KB]: 10618
% 0.21/0.54  % (29060)Time elapsed: 0.139 s
% 0.21/0.54  % (29060)------------------------------
% 0.21/0.54  % (29060)------------------------------
% 0.21/0.54  % (29063)Refutation not found, incomplete strategy% (29063)------------------------------
% 0.21/0.54  % (29063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29063)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29063)Memory used [KB]: 10618
% 0.21/0.54  % (29063)Time elapsed: 0.136 s
% 0.21/0.54  % (29063)------------------------------
% 0.21/0.54  % (29063)------------------------------
% 0.21/0.54  % (29061)Refutation not found, incomplete strategy% (29061)------------------------------
% 0.21/0.54  % (29061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29061)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29061)Memory used [KB]: 10618
% 0.21/0.54  % (29061)Time elapsed: 0.139 s
% 0.21/0.54  % (29061)------------------------------
% 0.21/0.54  % (29061)------------------------------
% 0.21/0.54  % (29074)Refutation not found, incomplete strategy% (29074)------------------------------
% 0.21/0.54  % (29074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29074)Memory used [KB]: 10746
% 0.21/0.54  % (29074)Time elapsed: 0.139 s
% 0.21/0.54  % (29074)------------------------------
% 0.21/0.54  % (29074)------------------------------
% 0.21/0.54  % (29079)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (29069)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (29076)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (29069)Refutation not found, incomplete strategy% (29069)------------------------------
% 0.21/0.55  % (29069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29069)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29069)Memory used [KB]: 10618
% 0.21/0.55  % (29069)Time elapsed: 0.139 s
% 0.21/0.55  % (29069)------------------------------
% 0.21/0.55  % (29069)------------------------------
% 0.21/0.55  % (29078)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (29062)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (29071)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (29072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (29072)Refutation not found, incomplete strategy% (29072)------------------------------
% 0.21/0.55  % (29072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29072)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29072)Memory used [KB]: 10746
% 0.21/0.55  % (29072)Time elapsed: 0.150 s
% 0.21/0.55  % (29072)------------------------------
% 0.21/0.55  % (29072)------------------------------
% 0.21/0.55  % (29064)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (29054)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (29054)Refutation not found, incomplete strategy% (29054)------------------------------
% 0.21/0.56  % (29054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29062)Refutation not found, incomplete strategy% (29062)------------------------------
% 0.21/0.56  % (29062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29062)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29062)Memory used [KB]: 10618
% 0.21/0.56  % (29062)Time elapsed: 0.132 s
% 0.21/0.56  % (29062)------------------------------
% 0.21/0.56  % (29062)------------------------------
% 0.21/0.56  % (29054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29054)Memory used [KB]: 10618
% 0.21/0.56  % (29054)Time elapsed: 0.134 s
% 0.21/0.56  % (29054)------------------------------
% 0.21/0.56  % (29054)------------------------------
% 0.21/0.57  % (29070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.96/0.61  % (29064)Refutation not found, incomplete strategy% (29064)------------------------------
% 1.96/0.61  % (29064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.61  % (29064)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.61  
% 1.96/0.61  % (29064)Memory used [KB]: 6908
% 1.96/0.61  % (29064)Time elapsed: 0.193 s
% 1.96/0.61  % (29064)------------------------------
% 1.96/0.61  % (29064)------------------------------
% 2.01/0.63  % (29081)Refutation not found, incomplete strategy% (29081)------------------------------
% 2.01/0.63  % (29081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (29081)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.63  
% 2.01/0.63  % (29081)Memory used [KB]: 2046
% 2.01/0.63  % (29081)Time elapsed: 0.234 s
% 2.01/0.63  % (29081)------------------------------
% 2.01/0.63  % (29081)------------------------------
% 2.01/0.63  % (29088)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.01/0.64  % (29087)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.01/0.64  % (29087)Refutation not found, incomplete strategy% (29087)------------------------------
% 2.01/0.64  % (29087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (29087)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.64  
% 2.01/0.64  % (29087)Memory used [KB]: 6140
% 2.01/0.64  % (29087)Time elapsed: 0.080 s
% 2.01/0.64  % (29087)------------------------------
% 2.01/0.64  % (29087)------------------------------
% 2.01/0.65  % (29090)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.01/0.66  % (29089)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.01/0.66  % (29104)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.01/0.67  % (29099)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.01/0.67  % (29053)Refutation not found, incomplete strategy% (29053)------------------------------
% 2.01/0.67  % (29053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.67  % (29053)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.67  
% 2.01/0.67  % (29053)Memory used [KB]: 6140
% 2.01/0.67  % (29053)Time elapsed: 0.260 s
% 2.01/0.67  % (29053)------------------------------
% 2.01/0.67  % (29053)------------------------------
% 2.01/0.67  % (29098)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.01/0.68  % (29097)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.01/0.68  % (29100)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.01/0.68  % (29101)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.01/0.68  % (29101)Refutation not found, incomplete strategy% (29101)------------------------------
% 2.01/0.68  % (29101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.68  % (29101)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.68  
% 2.01/0.68  % (29101)Memory used [KB]: 1663
% 2.01/0.68  % (29101)Time elapsed: 0.115 s
% 2.01/0.68  % (29101)------------------------------
% 2.01/0.68  % (29101)------------------------------
% 2.01/0.69  % (29079)Refutation not found, incomplete strategy% (29079)------------------------------
% 2.01/0.69  % (29079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.69  % (29102)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.01/0.70  % (29103)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.01/0.71  % (29079)Termination reason: Refutation not found, incomplete strategy
% 2.01/0.71  
% 2.01/0.71  % (29079)Memory used [KB]: 6780
% 2.01/0.71  % (29079)Time elapsed: 0.288 s
% 2.01/0.71  % (29079)------------------------------
% 2.01/0.71  % (29079)------------------------------
% 2.68/0.72  % (29071)Refutation not found, incomplete strategy% (29071)------------------------------
% 2.68/0.72  % (29071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.73  % (29106)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.68/0.74  % (29071)Termination reason: Refutation not found, incomplete strategy
% 2.68/0.74  
% 2.68/0.74  % (29071)Memory used [KB]: 12025
% 2.68/0.74  % (29071)Time elapsed: 0.303 s
% 2.68/0.74  % (29071)------------------------------
% 2.68/0.74  % (29071)------------------------------
% 2.68/0.75  % (29107)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.68/0.75  % (29107)Refutation not found, incomplete strategy% (29107)------------------------------
% 2.68/0.75  % (29107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.76  % (29107)Termination reason: Refutation not found, incomplete strategy
% 2.68/0.76  
% 2.68/0.76  % (29107)Memory used [KB]: 1663
% 2.68/0.76  % (29107)Time elapsed: 0.100 s
% 2.68/0.76  % (29107)------------------------------
% 2.68/0.76  % (29107)------------------------------
% 2.68/0.78  % (29088)Refutation not found, incomplete strategy% (29088)------------------------------
% 2.68/0.78  % (29088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.68/0.78  % (29088)Termination reason: Refutation not found, incomplete strategy
% 2.68/0.78  
% 2.68/0.78  % (29088)Memory used [KB]: 6140
% 2.68/0.78  % (29088)Time elapsed: 0.225 s
% 2.68/0.78  % (29088)------------------------------
% 2.68/0.78  % (29088)------------------------------
% 2.68/0.78  % (29108)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.19/0.80  % (29097)Refutation not found, incomplete strategy% (29097)------------------------------
% 3.19/0.80  % (29097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.80  % (29097)Termination reason: Refutation not found, incomplete strategy
% 3.19/0.80  
% 3.19/0.80  % (29097)Memory used [KB]: 11513
% 3.19/0.80  % (29097)Time elapsed: 0.228 s
% 3.19/0.80  % (29097)------------------------------
% 3.19/0.80  % (29097)------------------------------
% 3.19/0.81  % (29109)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.19/0.81  % (29057)Time limit reached!
% 3.19/0.81  % (29057)------------------------------
% 3.19/0.81  % (29057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.81  % (29057)Termination reason: Time limit
% 3.19/0.81  
% 3.19/0.81  % (29057)Memory used [KB]: 9466
% 3.19/0.81  % (29057)Time elapsed: 0.411 s
% 3.19/0.81  % (29057)------------------------------
% 3.19/0.81  % (29057)------------------------------
% 3.19/0.81  % (29055)Refutation not found, incomplete strategy% (29055)------------------------------
% 3.19/0.81  % (29055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.81  % (29055)Termination reason: Refutation not found, incomplete strategy
% 3.19/0.81  
% 3.19/0.81  % (29055)Memory used [KB]: 12281
% 3.19/0.81  % (29055)Time elapsed: 0.411 s
% 3.19/0.81  % (29055)------------------------------
% 3.19/0.81  % (29055)------------------------------
% 3.19/0.82  % SZS status CounterSatisfiable for theBenchmark
% 3.19/0.82  % (29058)# SZS output start Saturation.
% 3.19/0.82  cnf(u1351,axiom,
% 3.19/0.82      r1_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X13),k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1345,axiom,
% 3.19/0.82      r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))).
% 3.19/0.82  
% 3.19/0.82  cnf(u92,axiom,
% 3.19/0.82      r1_tarski(k1_xboole_0,X6)).
% 3.19/0.82  
% 3.19/0.82  cnf(u176,axiom,
% 3.19/0.82      r1_tarski(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u59,axiom,
% 3.19/0.82      r1_tarski(k3_xboole_0(X1,X0),X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u30,axiom,
% 3.19/0.82      r1_tarski(k3_xboole_0(X0,X1),X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u39,axiom,
% 3.19/0.82      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 3.19/0.82  
% 3.19/0.82  cnf(u3171,axiom,
% 3.19/0.82      r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k3_xboole_0(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44))) | X44 = X45).
% 3.19/0.82  
% 3.19/0.82  cnf(u2892,axiom,
% 3.19/0.82      r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45))) | X44 = X45).
% 3.19/0.82  
% 3.19/0.82  cnf(u1352,axiom,
% 3.19/0.82      r1_xboole_0(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X15),k5_xboole_0(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16),k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X15)))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1348,axiom,
% 3.19/0.82      r1_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))).
% 3.19/0.82  
% 3.19/0.82  cnf(u56,axiom,
% 3.19/0.82      r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1).
% 3.19/0.82  
% 3.19/0.82  cnf(u1360,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X33),k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32)),k6_enumset1(X32,X32,X32,X32,X32,X32,X32,X32))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1359,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(k6_enumset1(X30,X30,X30,X30,X30,X30,X30,X30),k6_enumset1(X30,X30,X30,X30,X30,X30,X30,X31)),k6_enumset1(X30,X30,X30,X30,X30,X30,X30,X30))).
% 3.19/0.82  
% 3.19/0.82  cnf(u451,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10)),k3_xboole_0(X9,X10))).
% 3.19/0.82  
% 3.19/0.82  cnf(u234,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(k3_xboole_0(X25,X26),X26),k3_xboole_0(X25,X26))).
% 3.19/0.82  
% 3.19/0.82  cnf(u185,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(k3_xboole_0(X20,X21),X20),k3_xboole_0(X20,X21))).
% 3.19/0.82  
% 3.19/0.82  cnf(u235,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(X28,k3_xboole_0(X27,X28)),k3_xboole_0(X27,X28))).
% 3.19/0.82  
% 3.19/0.82  cnf(u186,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(X22,k3_xboole_0(X22,X23)),k3_xboole_0(X22,X23))).
% 3.19/0.82  
% 3.19/0.82  cnf(u146,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X3,X2))).
% 3.19/0.82  
% 3.19/0.82  cnf(u145,axiom,
% 3.19/0.82      r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u98,axiom,
% 3.19/0.82      r1_xboole_0(k1_xboole_0,X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u3388,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45)),k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45))) | X44 = X45).
% 3.19/0.82  
% 3.19/0.82  cnf(u2752,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45)),k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X45)) | X44 = X45).
% 3.19/0.82  
% 3.19/0.82  cnf(u1776,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34),k6_enumset1(X35,X35,X35,X35,X35,X35,X35,X35)),k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34)) | X34 = X35).
% 3.19/0.82  
% 3.19/0.82  cnf(u293,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X8,X9),k5_xboole_0(k3_xboole_0(X8,X9),k3_xboole_0(X8,X9)))).
% 3.19/0.82  
% 3.19/0.82  cnf(u226,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X7,X8),k5_xboole_0(k3_xboole_0(X7,X8),X8))).
% 3.19/0.82  
% 3.19/0.82  cnf(u179,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(k3_xboole_0(X6,X7),X6))).
% 3.19/0.82  
% 3.19/0.82  cnf(u230,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X16,X17),k5_xboole_0(X17,k3_xboole_0(X16,X17)))).
% 3.19/0.82  
% 3.19/0.82  cnf(u63,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u183,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X15,X16),k5_xboole_0(X15,k3_xboole_0(X15,X16)))).
% 3.19/0.82  
% 3.19/0.82  cnf(u32,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1942,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X8,X7),k3_xboole_0(X8,X7)) | k1_xboole_0 != k3_xboole_0(X7,X8)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1986,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X0,X1),X1) | k3_xboole_0(X1,X0) != k1_xboole_0).
% 3.19/0.82  
% 3.19/0.82  cnf(u1759,axiom,
% 3.19/0.82      r1_xboole_0(k3_xboole_0(X2,X3),X2) | k1_xboole_0 != k3_xboole_0(X3,X2)).
% 3.19/0.82  
% 3.19/0.82  cnf(u2074,axiom,
% 3.19/0.82      r1_xboole_0(X13,k3_xboole_0(X14,X13)) | k1_xboole_0 != k3_xboole_0(X13,X14)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1915,axiom,
% 3.19/0.82      r1_xboole_0(X12,k3_xboole_0(X12,X11)) | k1_xboole_0 != k3_xboole_0(X11,X12)).
% 3.19/0.82  
% 3.19/0.82  cnf(u138,axiom,
% 3.19/0.82      r1_xboole_0(X6,k1_xboole_0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u40,axiom,
% 3.19/0.82      r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0).
% 3.19/0.82  
% 3.19/0.82  cnf(u147,axiom,
% 3.19/0.82      r1_xboole_0(X4,X5) | k1_xboole_0 != k3_xboole_0(X5,X4)).
% 3.19/0.82  
% 3.19/0.82  cnf(u4441,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1868,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44)) | r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44))).
% 3.19/0.82  
% 3.19/0.82  cnf(u5262,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1389,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94),k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94)) | r1_xboole_0(k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X94),k6_enumset1(X94,X94,X94,X94,X94,X94,X94,X95))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1390,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X96),k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X96)) | r1_xboole_0(k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X97),k6_enumset1(X96,X96,X96,X96,X96,X96,X96,X96))).
% 3.19/0.82  
% 3.19/0.82  cnf(u4442,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5)) | r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1901,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45)) | r1_xboole_0(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44),k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X44))).
% 3.19/0.82  
% 3.19/0.82  cnf(u5263,axiom,
% 3.19/0.82      ~r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X5)) | r1_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))).
% 3.19/0.82  
% 3.19/0.82  cnf(u524,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X15)) | ~r2_hidden(X16,k3_xboole_0(X14,X15))).
% 3.19/0.82  
% 3.19/0.82  cnf(u539,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10)) | r1_xboole_0(k3_xboole_0(X9,X10),X9)).
% 3.19/0.82  
% 3.19/0.82  cnf(u542,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X16)) | r1_xboole_0(k3_xboole_0(X15,X16),X16)).
% 3.19/0.82  
% 3.19/0.82  cnf(u557,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10)) | r1_xboole_0(X9,k3_xboole_0(X9,X10))).
% 3.19/0.82  
% 3.19/0.82  cnf(u560,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X15,X16),k3_xboole_0(X15,X16)) | r1_xboole_0(X16,k3_xboole_0(X15,X16))).
% 3.19/0.82  
% 3.19/0.82  cnf(u534,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X1,X0),X0) | r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u552,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X1,X0),X0) | r1_xboole_0(X1,X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1729,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X2,X3),X3) | r1_xboole_0(k3_xboole_0(X2,X3),X2)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1884,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X11,X12),X12) | r1_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12))).
% 3.19/0.82  
% 3.19/0.82  cnf(u2842,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X8,X9),X9) | r1_xboole_0(X8,k3_xboole_0(X8,X9))).
% 3.19/0.82  
% 3.19/0.82  cnf(u517,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X0,X1),X0) | r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u518,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X2,X3),X2) | r1_xboole_0(X3,X2)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1878,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X1,X0),X1) | r1_xboole_0(k3_xboole_0(X1,X0),X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1883,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X9,X10),X9) | r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10))).
% 3.19/0.82  
% 3.19/0.82  cnf(u2982,axiom,
% 3.19/0.82      ~r1_xboole_0(k3_xboole_0(X1,X0),X1) | r1_xboole_0(X0,k3_xboole_0(X1,X0))).
% 3.19/0.82  
% 3.19/0.82  cnf(u620,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u638,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,k3_xboole_0(X1,X0)) | r1_xboole_0(X1,X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1728,axiom,
% 3.19/0.82      ~r1_xboole_0(X1,k3_xboole_0(X0,X1)) | r1_xboole_0(k3_xboole_0(X0,X1),X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1851,axiom,
% 3.19/0.82      ~r1_xboole_0(X12,k3_xboole_0(X11,X12)) | r1_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12))).
% 3.19/0.82  
% 3.19/0.82  cnf(u2843,axiom,
% 3.19/0.82      ~r1_xboole_0(X11,k3_xboole_0(X10,X11)) | r1_xboole_0(X10,k3_xboole_0(X10,X11))).
% 3.19/0.82  
% 3.19/0.82  cnf(u603,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u604,axiom,
% 3.19/0.82      ~r1_xboole_0(X2,k3_xboole_0(X2,X3)) | r1_xboole_0(X3,X2)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1845,axiom,
% 3.19/0.82      ~r1_xboole_0(X1,k3_xboole_0(X1,X0)) | r1_xboole_0(k3_xboole_0(X1,X0),X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1850,axiom,
% 3.19/0.82      ~r1_xboole_0(X9,k3_xboole_0(X9,X10)) | r1_xboole_0(k3_xboole_0(X9,X10),k3_xboole_0(X9,X10))).
% 3.19/0.82  
% 3.19/0.82  cnf(u3017,axiom,
% 3.19/0.82      ~r1_xboole_0(X1,k3_xboole_0(X1,X0)) | r1_xboole_0(X0,k3_xboole_0(X1,X0))).
% 3.19/0.82  
% 3.19/0.82  cnf(u3335,axiom,
% 3.19/0.82      ~r1_xboole_0(X3,X2) | r1_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))).
% 3.19/0.82  
% 3.19/0.82  cnf(u3334,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u3118,axiom,
% 3.19/0.82      ~r1_xboole_0(X2,X3) | r1_xboole_0(X2,k3_xboole_0(X3,X2))).
% 3.19/0.82  
% 3.19/0.82  cnf(u3117,axiom,
% 3.19/0.82      ~r1_xboole_0(X1,X0) | r1_xboole_0(X0,k3_xboole_0(X1,X0))).
% 3.19/0.82  
% 3.19/0.82  cnf(u2839,axiom,
% 3.19/0.82      ~r1_xboole_0(X3,X2) | r1_xboole_0(X2,k3_xboole_0(X2,X3))).
% 3.19/0.82  
% 3.19/0.82  cnf(u2838,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u2699,axiom,
% 3.19/0.82      ~r1_xboole_0(X3,X2) | r1_xboole_0(k3_xboole_0(X2,X3),X3)).
% 3.19/0.82  
% 3.19/0.82  cnf(u2698,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1733,axiom,
% 3.19/0.82      ~r1_xboole_0(X10,X11) | r1_xboole_0(k3_xboole_0(X10,X11),X10)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1732,axiom,
% 3.19/0.82      ~r1_xboole_0(X9,X8) | r1_xboole_0(k3_xboole_0(X8,X9),X8)).
% 3.19/0.82  
% 3.19/0.82  cnf(u140,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u41,axiom,
% 3.19/0.82      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 3.19/0.82  
% 3.19/0.82  cnf(u1358,axiom,
% 3.19/0.82      r2_hidden(sK2(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29),k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X28)),k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X28)) | r1_xboole_0(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29),k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X28))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1350,axiom,
% 3.19/0.82      r2_hidden(sK2(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11)) | r1_xboole_0(k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X11),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12))).
% 3.19/0.82  
% 3.19/0.82  cnf(u755,axiom,
% 3.19/0.82      r2_hidden(sK2(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12)),k3_xboole_0(X11,X12)) | r1_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12))).
% 3.19/0.82  
% 3.19/0.82  cnf(u228,axiom,
% 3.19/0.82      r2_hidden(sK2(k3_xboole_0(X12,X13),X13),k3_xboole_0(X12,X13)) | r1_xboole_0(k3_xboole_0(X12,X13),X13)).
% 3.19/0.82  
% 3.19/0.82  cnf(u181,axiom,
% 3.19/0.82      r2_hidden(sK2(k3_xboole_0(X11,X12),X11),k3_xboole_0(X11,X12)) | r1_xboole_0(k3_xboole_0(X11,X12),X11)).
% 3.19/0.82  
% 3.19/0.82  cnf(u324,axiom,
% 3.19/0.82      r2_hidden(sK2(X12,k3_xboole_0(X13,X12)),k3_xboole_0(X13,X12)) | r1_xboole_0(X12,k3_xboole_0(X13,X12))).
% 3.19/0.82  
% 3.19/0.82  cnf(u274,axiom,
% 3.19/0.82      r2_hidden(sK2(X11,k3_xboole_0(X11,X12)),k3_xboole_0(X11,X12)) | r1_xboole_0(X11,k3_xboole_0(X11,X12))).
% 3.19/0.82  
% 3.19/0.82  cnf(u125,axiom,
% 3.19/0.82      r2_hidden(sK2(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u37,axiom,
% 3.19/0.82      r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u1349,axiom,
% 3.19/0.82      ~r2_hidden(X10,k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8)) | ~r1_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1353,axiom,
% 3.19/0.82      ~r2_hidden(X19,k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)) | ~r1_xboole_0(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17))).
% 3.19/0.82  
% 3.19/0.82  cnf(u95,axiom,
% 3.19/0.82      ~r2_hidden(X5,k1_xboole_0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u5100,axiom,
% 3.19/0.82      ~r2_hidden(X10,k3_xboole_0(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X8),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9))) | X8 = X9).
% 3.19/0.82  
% 3.19/0.82  cnf(u2379,axiom,
% 3.19/0.82      ~r2_hidden(X10,k3_xboole_0(X9,X8)) | k1_xboole_0 != k3_xboole_0(X8,X9)).
% 3.19/0.82  
% 3.19/0.82  cnf(u231,axiom,
% 3.19/0.82      ~r2_hidden(X20,k3_xboole_0(X18,X19)) | ~r1_xboole_0(X19,k3_xboole_0(X18,X19))).
% 3.19/0.82  
% 3.19/0.82  cnf(u227,axiom,
% 3.19/0.82      ~r2_hidden(X11,k3_xboole_0(X9,X10)) | ~r1_xboole_0(k3_xboole_0(X9,X10),X10)).
% 3.19/0.82  
% 3.19/0.82  cnf(u184,axiom,
% 3.19/0.82      ~r2_hidden(X19,k3_xboole_0(X17,X18)) | ~r1_xboole_0(X17,k3_xboole_0(X17,X18))).
% 3.19/0.82  
% 3.19/0.82  cnf(u180,axiom,
% 3.19/0.82      ~r2_hidden(X10,k3_xboole_0(X8,X9)) | ~r1_xboole_0(k3_xboole_0(X8,X9),X8)).
% 3.19/0.82  
% 3.19/0.82  cnf(u73,axiom,
% 3.19/0.82      ~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u36,axiom,
% 3.19/0.82      ~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)).
% 3.19/0.82  
% 3.19/0.82  cnf(u3576,negated_conjecture,
% 3.19/0.82      sK0 = sK1).
% 3.19/0.82  
% 3.19/0.82  cnf(u1343,axiom,
% 3.19/0.82      k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))).
% 3.19/0.82  
% 3.19/0.82  cnf(u55,axiom,
% 3.19/0.82      k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))).
% 3.19/0.82  
% 3.19/0.82  cnf(u28,axiom,
% 3.19/0.82      k5_xboole_0(X0,k1_xboole_0) = X0).
% 3.19/0.82  
% 3.19/0.82  cnf(u3618,negated_conjecture,
% 3.19/0.82      k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)).
% 3.19/0.82  
% 3.19/0.82  cnf(u3570,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k6_enumset1(X170,X170,X170,X170,X170,X170,X170,X170),k3_xboole_0(k6_enumset1(X171,X171,X171,X171,X171,X171,X171,X171),k6_enumset1(X170,X170,X170,X170,X170,X170,X170,X170))) | X170 = X171).
% 3.19/0.82  
% 3.19/0.82  cnf(u3572,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k6_enumset1(X165,X165,X165,X165,X165,X165,X165,X165),k3_xboole_0(k6_enumset1(X165,X165,X165,X165,X165,X165,X165,X165),k6_enumset1(X164,X164,X164,X164,X164,X164,X164,X164))) | X164 = X165).
% 3.19/0.82  
% 3.19/0.82  cnf(u1357,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X26),k5_xboole_0(k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X27),k6_enumset1(X26,X26,X26,X26,X26,X26,X26,X26)))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1356,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X24),k5_xboole_0(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X24),k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)))).
% 3.19/0.82  
% 3.19/0.82  cnf(u340,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) | X2 = X3).
% 3.19/0.82  
% 3.19/0.82  cnf(u1362,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37),k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X36)),k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X36))).
% 3.19/0.82  
% 3.19/0.82  cnf(u1361,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34),k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X35)),k6_enumset1(X34,X34,X34,X34,X34,X34,X34,X34))).
% 3.19/0.82  
% 3.19/0.82  cnf(u766,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(k3_xboole_0(X34,X35),k3_xboole_0(X34,X35)),k3_xboole_0(X34,X35))).
% 3.19/0.82  
% 3.19/0.82  cnf(u376,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(k3_xboole_0(X15,X16),X16),k3_xboole_0(X15,X16))).
% 3.19/0.82  
% 3.19/0.82  cnf(u373,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(k3_xboole_0(X9,X10),X9),k3_xboole_0(X9,X10))).
% 3.19/0.82  
% 3.19/0.82  cnf(u372,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(X7,k3_xboole_0(X8,X7)),k3_xboole_0(X8,X7))).
% 3.19/0.82  
% 3.19/0.82  cnf(u371,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(X5,k3_xboole_0(X5,X6)),k3_xboole_0(X5,X6))).
% 3.19/0.82  
% 3.19/0.82  cnf(u159,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X3,X2))).
% 3.19/0.82  
% 3.19/0.82  cnf(u151,axiom,
% 3.19/0.82      k1_xboole_0 = k3_xboole_0(k5_xboole_0(X2,X3),k3_xboole_0(X2,X3))).
% 3.19/0.82  
% 3.19/0.83  cnf(u96,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 3.19/0.83  
% 3.19/0.83  cnf(u3569,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(k6_enumset1(X176,X176,X176,X176,X176,X176,X176,X176),k6_enumset1(X175,X175,X175,X175,X175,X175,X175,X175)),k3_xboole_0(k6_enumset1(X176,X176,X176,X176,X176,X176,X176,X176),k6_enumset1(X175,X175,X175,X175,X175,X175,X175,X175))) | X175 = X176).
% 3.19/0.83  
% 3.19/0.83  cnf(u3571,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(k6_enumset1(X169,X169,X169,X169,X169,X169,X169,X169),k6_enumset1(X168,X168,X168,X168,X168,X168,X168,X168)),k6_enumset1(X168,X168,X168,X168,X168,X168,X168,X168)) | X168 = X169).
% 3.19/0.83  
% 3.19/0.83  cnf(u3573,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(k6_enumset1(X159,X159,X159,X159,X159,X159,X159,X159),k6_enumset1(X158,X158,X158,X158,X158,X158,X158,X158)),k6_enumset1(X159,X159,X159,X159,X159,X159,X159,X159)) | X158 = X159).
% 3.19/0.83  
% 3.19/0.83  cnf(u761,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(X24,X25),k5_xboole_0(k3_xboole_0(X24,X25),k3_xboole_0(X24,X25)))).
% 3.19/0.83  
% 3.19/0.83  cnf(u233,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(X23,X24),k5_xboole_0(k3_xboole_0(X23,X24),X24))).
% 3.19/0.83  
% 3.19/0.83  cnf(u198,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(k3_xboole_0(X6,X7),X6))).
% 3.19/0.83  
% 3.19/0.83  cnf(u245,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(X12,X13),k5_xboole_0(X13,k3_xboole_0(X12,X13)))).
% 3.19/0.83  
% 3.19/0.83  cnf(u78,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X2))).
% 3.19/0.83  
% 3.19/0.83  cnf(u242,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),k5_xboole_0(X6,k3_xboole_0(X6,X7)))).
% 3.19/0.83  
% 3.19/0.83  cnf(u77,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))).
% 3.19/0.83  
% 3.19/0.83  cnf(u106,axiom,
% 3.19/0.83      k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)).
% 3.19/0.83  
% 3.19/0.83  cnf(u172,axiom,
% 3.19/0.83      k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7))).
% 3.19/0.83  
% 3.19/0.83  cnf(u220,axiom,
% 3.19/0.83      k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))).
% 3.19/0.83  
% 3.19/0.83  cnf(u173,axiom,
% 3.19/0.83      k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))).
% 3.19/0.83  
% 3.19/0.83  cnf(u76,axiom,
% 3.19/0.83      k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)).
% 3.19/0.83  
% 3.19/0.83  cnf(u75,axiom,
% 3.19/0.83      k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X0)).
% 3.19/0.83  
% 3.19/0.83  cnf(u31,axiom,
% 3.19/0.83      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 3.19/0.83  
% 3.19/0.83  cnf(u167,axiom,
% 3.19/0.83      k1_xboole_0 != k3_xboole_0(X2,X3) | k1_xboole_0 = k3_xboole_0(X3,X2)).
% 3.19/0.83  
% 3.19/0.83  cnf(u1916,axiom,
% 3.19/0.83      k1_xboole_0 != k3_xboole_0(X13,X14) | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X14,X13),X14)).
% 3.19/0.83  
% 3.19/0.83  cnf(u2029,axiom,
% 3.19/0.83      k1_xboole_0 != k3_xboole_0(X15,X16) | k1_xboole_0 = k3_xboole_0(X16,k3_xboole_0(X16,X15))).
% 3.19/0.83  
% 3.19/0.83  cnf(u2075,axiom,
% 3.19/0.83      k1_xboole_0 != k3_xboole_0(X15,X16) | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X16,X15),X15)).
% 3.19/0.83  
% 3.19/0.83  cnf(u2121,axiom,
% 3.19/0.83      k1_xboole_0 != k3_xboole_0(X15,X16) | k1_xboole_0 = k3_xboole_0(X15,k3_xboole_0(X16,X15))).
% 3.19/0.83  
% 3.19/0.83  cnf(u2383,axiom,
% 3.19/0.83      k1_xboole_0 != k3_xboole_0(X17,X18) | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X18,X17),k3_xboole_0(X18,X17))).
% 3.19/0.83  
% 3.19/0.83  % (29058)# SZS output end Saturation.
% 3.19/0.83  % (29058)------------------------------
% 3.19/0.83  % (29058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.19/0.83  % (29058)Termination reason: Satisfiable
% 3.19/0.83  
% 3.19/0.83  % (29058)Memory used [KB]: 8187
% 3.19/0.83  % (29058)Time elapsed: 0.410 s
% 3.19/0.83  % (29058)------------------------------
% 3.19/0.83  % (29058)------------------------------
% 3.19/0.83  % (29051)Success in time 0.454 s
%------------------------------------------------------------------------------
