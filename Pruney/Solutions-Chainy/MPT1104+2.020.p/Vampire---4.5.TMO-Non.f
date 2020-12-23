%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:53 EST 2020

% Result     : Timeout 58.79s
% Output     : None 
% Verified   : 
% Statistics : Number of clauses        :  252 ( 252 expanded)
%              Number of leaves         :  252 ( 252 expanded)
%              Depth                    :    0
%              Number of atoms          :  270 ( 270 expanded)
%              Number of equality atoms :  241 ( 241 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u40,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u81,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u119,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X2)) )).

cnf(u120,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X3)) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) )).

cnf(u102,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u101,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u80,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) )).

cnf(u118,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k4_subset_1(X1,X1,X0) )).

cnf(u86,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u85,negated_conjecture,
    ( r1_tarski(sK2,u1_struct_0(sK0)) )).

cnf(u84,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u75,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 )).

cnf(u335,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u83,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u38,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u52,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u77,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )).

cnf(u127,negated_conjecture,
    ( sK1 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) )).

cnf(u124,negated_conjecture,
    ( sK2 = k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) )).

cnf(u88,negated_conjecture,
    ( k1_xboole_0 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) )).

cnf(u360,negated_conjecture,
    ( sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) )).

cnf(u297,negated_conjecture,
    ( sK2 = k7_subset_1(sK2,sK2,sK1) )).

cnf(u356,negated_conjecture,
    ( sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2) )).

cnf(u139,negated_conjecture,
    ( sK1 = k7_subset_1(sK1,sK1,sK2) )).

cnf(u396,axiom,
    ( k7_subset_1(X1,X1,k4_subset_1(X1,X1,X1)) = k7_subset_1(k4_subset_1(X1,X1,X1),k4_subset_1(X1,X1,X1),k4_subset_1(X1,X1,X1)) )).

cnf(u4446,axiom,
    ( k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k7_subset_1(X3,X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )).

cnf(u1375,axiom,
    ( k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) )).

cnf(u1136,axiom,
    ( k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )).

cnf(u1297,axiom,
    ( k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k7_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )).

cnf(u1104,axiom,
    ( k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6))) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6))) )).

cnf(u1373,axiom,
    ( k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )).

cnf(u1165,axiom,
    ( k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) )).

cnf(u476,axiom,
    ( k7_subset_1(X13,X13,k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14))) = k7_subset_1(k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14))) )).

cnf(u457,axiom,
    ( k7_subset_1(X13,X13,k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13))) = k7_subset_1(k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13))) )).

cnf(u1491,axiom,
    ( k7_subset_1(X15,X15,k5_xboole_0(X15,k7_subset_1(X16,X16,X15))) = k7_subset_1(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15))) )).

cnf(u1014,axiom,
    ( k7_subset_1(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k5_xboole_0(X9,k7_subset_1(X8,X8,X9))) = k7_subset_1(X9,X9,k5_xboole_0(X9,k7_subset_1(X8,X8,X9))) )).

cnf(u1003,axiom,
    ( k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k7_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) )).

cnf(u896,axiom,
    ( k7_subset_1(X6,X6,k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) )).

cnf(u2907,axiom,
    ( k7_subset_1(X3,X3,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u1011,axiom,
    ( k7_subset_1(k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) = k7_subset_1(X7,X7,k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) )).

cnf(u960,axiom,
    ( k7_subset_1(X10,X10,k5_xboole_0(X11,k7_subset_1(X10,X10,X11))) = k7_subset_1(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11))) )).

cnf(u428,axiom,
    ( k7_subset_1(X13,X13,k5_xboole_0(X13,k7_subset_1(X14,X14,X13))) = k7_subset_1(k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k5_xboole_0(X13,k7_subset_1(X14,X14,X13))) )).

cnf(u379,axiom,
    ( k7_subset_1(X3,X3,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u517,negated_conjecture,
    ( k7_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) )).

cnf(u509,negated_conjecture,
    ( k7_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) )).

cnf(u516,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) )).

cnf(u508,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) )).

cnf(u293,axiom,
    ( k7_subset_1(X8,X8,X7) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)),X7) )).

cnf(u292,axiom,
    ( k7_subset_1(X5,X5,X6) = k7_subset_1(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),X6) )).

cnf(u326,axiom,
    ( k7_subset_1(X4,X4,X3) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3) )).

cnf(u291,axiom,
    ( k7_subset_1(X3,X3,X4) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X4) )).

cnf(u106,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X3) = k7_subset_1(sK1,sK1,X3) )).

cnf(u105,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X2) = k7_subset_1(sK2,sK2,X2) )).

cnf(u398,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK2) = k7_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),sK2) )).

cnf(u400,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),sK1) )).

cnf(u497,negated_conjecture,
    ( k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k7_subset_1(sK1,sK1,k2_struct_0(sK0)) )).

cnf(u98,axiom,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1) )).

cnf(u103,axiom,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k7_subset_1(X0,X0,X1) )).

cnf(u515,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) )).

cnf(u507,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) )).

cnf(u312,axiom,
    ( k5_xboole_0(X1,X1) = k7_subset_1(k4_subset_1(X1,X1,X1),k4_subset_1(X1,X1,X1),X1) )).

cnf(u548,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) )).

cnf(u155,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u37,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u522,axiom,
    ( k4_subset_1(X0,X0,X0) = k4_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0)) )).

cnf(u160,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1) )).

cnf(u159,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2) )).

cnf(u50545,axiom,
    ( k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)))) = k4_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3))) )).

cnf(u50531,axiom,
    ( k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9)))) = k4_subset_1(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9))) )).

cnf(u50525,axiom,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k4_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) )).

cnf(u40110,axiom,
    ( k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)) = k4_subset_1(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9))) )).

cnf(u52318,axiom,
    ( k3_tarski(k6_enumset1(X42,X42,X42,X42,X42,X42,X42,k3_tarski(k6_enumset1(X42,X42,X42,X42,X42,X42,X42,X43)))) = k4_subset_1(k3_tarski(k6_enumset1(X43,X43,X43,X43,X43,X43,X43,X42)),k3_tarski(k6_enumset1(X43,X43,X43,X43,X43,X43,X43,X42)),k3_tarski(k6_enumset1(X43,X43,X43,X43,X43,X43,X43,X42))) )).

cnf(u49520,axiom,
    ( k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9)) = k4_subset_1(k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)),k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)),k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10))) )).

cnf(u3204,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )).

cnf(u156,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0) )).

cnf(u45381,axiom,
    ( k5_xboole_0(X3,k7_subset_1(X2,X2,X3)) = k4_subset_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )).

cnf(u45380,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k4_subset_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )).

cnf(u2505,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) )).

cnf(u2480,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) )).

cnf(u38563,axiom,
    ( k5_xboole_0(X8,k7_subset_1(X7,X7,X8)) = k4_subset_1(k5_xboole_0(X7,k7_subset_1(X8,X8,X7)),k5_xboole_0(X7,k7_subset_1(X8,X8,X7)),k5_xboole_0(X7,k7_subset_1(X8,X8,X7))) )).

cnf(u753,axiom,
    ( k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) )).

cnf(u355,axiom,
    ( k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) )).

cnf(u2432,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))) )).

cnf(u651,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))) )).

cnf(u661,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))) )).

cnf(u154,negated_conjecture,
    ( k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) )).

cnf(u618,axiom,
    ( k4_subset_1(X5,X5,X5) = k3_tarski(k6_enumset1(k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5))) )).

cnf(u611,axiom,
    ( k4_subset_1(X0,X0,X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_subset_1(X0,X0,X0))) )).

cnf(u18692,axiom,
    ( k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)))) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,k7_subset_1(X3,X3,X4)))) )).

cnf(u3947,axiom,
    ( k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))) = k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9)) )).

cnf(u18691,axiom,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X2,X1)))) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) )).

cnf(u3206,axiom,
    ( k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) )).

cnf(u28697,axiom,
    ( k3_tarski(k6_enumset1(X18,X18,X18,X18,X18,X18,X18,X19)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k5_xboole_0(X18,k7_subset_1(X19,X19,X18)))) )).

cnf(u21845,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))) )).

cnf(u16404,axiom,
    ( k3_tarski(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)))) )).

cnf(u3995,axiom,
    ( k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X36)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X36)))) )).

cnf(u4026,axiom,
    ( k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X25,X25,X25,X25,X25,X25,X25,X24)))) )).

cnf(u3822,axiom,
    ( k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)))) )).

cnf(u8351,axiom,
    ( k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k5_xboole_0(X38,k7_subset_1(X39,X39,X38)))) )).

cnf(u708,axiom,
    ( k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)))) )).

cnf(u16756,axiom,
    ( k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X32)) = k3_tarski(k6_enumset1(k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)))) )).

cnf(u22083,axiom,
    ( k3_tarski(k6_enumset1(X50,X50,X50,X50,X50,X50,X50,X51)) = k3_tarski(k6_enumset1(k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X50,k7_subset_1(X51,X51,X50)))) )).

cnf(u22075,axiom,
    ( k3_tarski(k6_enumset1(X48,X48,X48,X48,X48,X48,X48,X49)) = k3_tarski(k6_enumset1(k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k3_tarski(k6_enumset1(X49,X49,X49,X49,X49,X49,X49,X48)))) )).

cnf(u6596,axiom,
    ( k3_tarski(k6_enumset1(X49,X49,X49,X49,X49,X49,X49,X48)) = k3_tarski(k6_enumset1(k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k3_tarski(k6_enumset1(X49,X49,X49,X49,X49,X49,X49,X48)))) )).

cnf(u22184,axiom,
    ( k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) = k3_tarski(k6_enumset1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) )).

cnf(u2604,axiom,
    ( k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)) = k3_tarski(k6_enumset1(k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)))) )).

cnf(u21489,axiom,
    ( k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)) = k3_tarski(k6_enumset1(k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)))) )).

cnf(u13492,axiom,
    ( k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) = k3_tarski(k6_enumset1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X4,k7_subset_1(X3,X3,X4)))) )).

cnf(u3946,axiom,
    ( k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X7)) = k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,k5_xboole_0(X8,k7_subset_1(X7,X7,X8)))) )).

cnf(u815,axiom,
    ( k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)) = k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )).

cnf(u688,axiom,
    ( k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)))) )).

cnf(u143,axiom,
    ( k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) )).

cnf(u16219,axiom,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))) )).

cnf(u15744,axiom,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) )).

cnf(u16825,axiom,
    ( k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) )).

cnf(u689,axiom,
    ( k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)) = k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )).

cnf(u502,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))) )).

cnf(u510,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))) )).

cnf(u654,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))) )).

cnf(u643,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))) )).

cnf(u39483,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )).

cnf(u20035,axiom,
    ( k5_xboole_0(X38,k7_subset_1(X39,X39,X38)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)))) )).

cnf(u26513,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) )).

cnf(u13695,axiom,
    ( k5_xboole_0(X31,k7_subset_1(X30,X30,X31)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)))) )).

cnf(u20693,axiom,
    ( k5_xboole_0(X12,k7_subset_1(X13,X13,X12)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)))) )).

cnf(u5099,axiom,
    ( k5_xboole_0(X22,k7_subset_1(X21,X21,X22)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k5_xboole_0(X21,k7_subset_1(X22,X22,X21)))) )).

cnf(u2544,axiom,
    ( k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)))) )).

cnf(u622,axiom,
    ( k5_xboole_0(X9,k7_subset_1(X8,X8,X9)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k5_xboole_0(X9,k7_subset_1(X8,X8,X9)))) )).

cnf(u33133,axiom,
    ( k5_xboole_0(X136,k7_subset_1(X135,X135,X136)) = k3_tarski(k6_enumset1(k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k3_tarski(k6_enumset1(X136,X136,X136,X136,X136,X136,X136,X135)))) )).

cnf(u15950,axiom,
    ( k5_xboole_0(X21,k7_subset_1(X20,X20,X21)) = k3_tarski(k6_enumset1(k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k3_tarski(k6_enumset1(X20,X20,X20,X20,X20,X20,X20,X21)))) )).

cnf(u8176,axiom,
    ( k5_xboole_0(X37,k7_subset_1(X36,X36,X37)) = k3_tarski(k6_enumset1(k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)))) )).

cnf(u8159,axiom,
    ( k5_xboole_0(X31,k7_subset_1(X30,X30,X31)) = k3_tarski(k6_enumset1(k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)))) )).

cnf(u13749,axiom,
    ( k5_xboole_0(X13,k7_subset_1(X12,X12,X13)) = k3_tarski(k6_enumset1(k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)))) )).

cnf(u8123,axiom,
    ( k5_xboole_0(X13,k7_subset_1(X12,X12,X13)) = k3_tarski(k6_enumset1(k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)))) )).

cnf(u620,axiom,
    ( k5_xboole_0(X7,k7_subset_1(X6,X6,X7)) = k3_tarski(k6_enumset1(k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)))) )).

cnf(u613,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)))) )).

cnf(u638,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k6_enumset1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))) )).

cnf(u634,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k6_enumset1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))) )).

cnf(u16671,axiom,
    ( k5_xboole_0(k5_xboole_0(X52,k7_subset_1(X51,X51,X52)),k7_subset_1(X51,X51,k5_xboole_0(X52,k7_subset_1(X51,X51,X52)))) = k3_tarski(k6_enumset1(X51,X51,X51,X51,X51,X51,X51,k3_tarski(k6_enumset1(X51,X51,X51,X51,X51,X51,X51,X52)))) )).

cnf(u18359,axiom,
    ( k5_xboole_0(k3_tarski(k6_enumset1(X38,X38,X38,X38,X38,X38,X38,X37)),k7_subset_1(X37,X37,k3_tarski(k6_enumset1(X38,X38,X38,X38,X38,X38,X38,X37)))) = k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X38)))) )).

cnf(u3214,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) )).

cnf(u813,axiom,
    ( k5_xboole_0(X3,k7_subset_1(X2,X2,X3)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))) )).

cnf(u3280,axiom,
    ( k5_xboole_0(X12,k7_subset_1(X13,X13,X12)) = k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,k5_xboole_0(X13,k7_subset_1(X12,X12,X13)))) )).

cnf(u686,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))) )).

cnf(u21874,axiom,
    ( k5_xboole_0(k5_xboole_0(X28,k7_subset_1(X29,X29,X28)),k7_subset_1(X29,X29,k5_xboole_0(X28,k7_subset_1(X29,X29,X28)))) = k3_tarski(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,k3_tarski(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29)))) )).

cnf(u473,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )).

cnf(u454,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )).

cnf(u425,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X2,X1)))) )).

cnf(u392,axiom,
    ( k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) )).

cnf(u2430,axiom,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )).

cnf(u72,axiom,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) )).

cnf(u189,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK2,sK1) )).

cnf(u331,negated_conjecture,
    ( k7_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2) )).

cnf(u175,negated_conjecture,
    ( k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2) )).

cnf(u223,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u222,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u221,negated_conjecture,
    ( k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u178,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))) = k5_xboole_0(sK2,sK2) )).

cnf(u298,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK1,sK2) )).

cnf(u333,negated_conjecture,
    ( k7_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) )).

cnf(u179,negated_conjecture,
    ( k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1) )).

cnf(u182,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))) = k5_xboole_0(sK1,sK1) )).

cnf(u242,negated_conjecture,
    ( k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u244,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u243,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u647,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))) )).

cnf(u487,negated_conjecture,
    ( k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) )).

cnf(u299,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0)))) )).

cnf(u192,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0)))) )).

cnf(u241,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1)) )).

cnf(u220,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK2,sK2)) )).

cnf(u129,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u126,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u128,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u125,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u2433,axiom,
    ( k4_subset_1(X3,X3,X3) = k5_xboole_0(k4_subset_1(X3,X3,X3),k7_subset_1(X3,X3,k4_subset_1(X3,X3,X3))) )).

cnf(u366,axiom,
    ( k7_subset_1(X3,X3,k4_subset_1(X3,X3,X3)) = k5_xboole_0(k4_subset_1(X3,X3,X3),k4_subset_1(X3,X3,X3)) )).

cnf(u279,axiom,
    ( k5_xboole_0(X0,X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_subset_1(X0,X0,X0)))) )).

cnf(u2694,axiom,
    ( k5_xboole_0(X8,k7_subset_1(X9,X9,X8)) = k5_xboole_0(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k7_subset_1(X9,X9,k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)))) )).

cnf(u2656,axiom,
    ( k5_xboole_0(X7,k7_subset_1(X6,X6,X7)) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k7_subset_1(X7,X7,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)))) )).

cnf(u2819,axiom,
    ( k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)))) )).

cnf(u867,axiom,
    ( k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18)) = k5_xboole_0(k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18)),k7_subset_1(X17,X17,k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18)))) )).

cnf(u9348,axiom,
    ( k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))) )).

cnf(u8780,axiom,
    ( k7_subset_1(X2,X2,k5_xboole_0(X3,k7_subset_1(X2,X2,X3))) = k5_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3))))) )).

cnf(u10936,axiom,
    ( k7_subset_1(X21,X21,k3_tarski(k6_enumset1(X22,X22,X22,X22,X22,X22,X22,X21))) = k5_xboole_0(k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X22,X22,X22,X22,X22,X22,X22,X21))))) )).

cnf(u2078,axiom,
    ( k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )).

cnf(u2140,axiom,
    ( k7_subset_1(X15,X15,k5_xboole_0(X15,k7_subset_1(X16,X16,X15))) = k5_xboole_0(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k1_setfam_1(k6_enumset1(k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16))))) )).

cnf(u1830,axiom,
    ( k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )).

cnf(u735,axiom,
    ( k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k5_xboole_0(k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) )).

cnf(u36157,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k7_subset_1(X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) )).

cnf(u28126,axiom,
    ( k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)) = k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k7_subset_1(X5,X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))) )).

cnf(u17795,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k7_subset_1(X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) )).

cnf(u1500,axiom,
    ( k5_xboole_0(X8,k7_subset_1(X7,X7,X8)) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)),k7_subset_1(X7,X7,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)))) )).

cnf(u797,axiom,
    ( k5_xboole_0(X13,k7_subset_1(X14,X14,X13)) = k5_xboole_0(k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X13)),k7_subset_1(X13,X13,k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X13)))) )).

cnf(u734,axiom,
    ( k7_subset_1(X4,X4,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))) = k5_xboole_0(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))) )).

cnf(u9349,axiom,
    ( k7_subset_1(X3,X3,k5_xboole_0(X3,k7_subset_1(X2,X2,X3))) = k5_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3))))) )).

cnf(u8779,axiom,
    ( k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))) )).

cnf(u10816,axiom,
    ( k7_subset_1(X44,X44,k3_tarski(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45))) = k5_xboole_0(k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45))))) )).

cnf(u2125,axiom,
    ( k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6))))) )).

cnf(u9265,axiom,
    ( k7_subset_1(X37,X37,k5_xboole_0(X37,k7_subset_1(X36,X36,X37))) = k5_xboole_0(k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k1_setfam_1(k6_enumset1(k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37))))) )).

cnf(u1581,axiom,
    ( k7_subset_1(X6,X6,k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k1_setfam_1(k6_enumset1(k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6))))) )).

cnf(u121,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) )).

cnf(u16646,axiom,
    ( k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14)) = k5_xboole_0(k5_xboole_0(X14,k7_subset_1(X13,X13,X14)),k7_subset_1(X13,X13,k5_xboole_0(X14,k7_subset_1(X13,X13,X14)))) )).

cnf(u19933,axiom,
    ( k5_xboole_0(k5_xboole_0(X52,k7_subset_1(X53,X53,X52)),k7_subset_1(X52,X52,k5_xboole_0(X52,k7_subset_1(X53,X53,X52)))) = k3_tarski(k6_enumset1(X52,X52,X52,X52,X52,X52,X52,k3_tarski(k6_enumset1(X52,X52,X52,X52,X52,X52,X52,X53)))) )).

cnf(u17527,axiom,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))) )).

cnf(u30478,axiom,
    ( k5_xboole_0(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k7_subset_1(X9,X9,k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))) = k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9)))) )).

cnf(u16218,axiom,
    ( k5_xboole_0(k5_xboole_0(X11,k7_subset_1(X12,X12,X11)),k7_subset_1(X11,X11,k5_xboole_0(X11,k7_subset_1(X12,X12,X11)))) = k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X11)) )).

cnf(u13493,axiom,
    ( k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)) = k5_xboole_0(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k7_subset_1(X10,X10,k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))) )).

cnf(u4183,axiom,
    ( k5_xboole_0(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k7_subset_1(X9,X9,k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))) = k5_xboole_0(X10,k7_subset_1(X9,X9,X10)) )).

cnf(u1064,axiom,
    ( k5_xboole_0(X6,k7_subset_1(X7,X7,X6)) = k5_xboole_0(k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k7_subset_1(X7,X7,k5_xboole_0(X6,k7_subset_1(X7,X7,X6)))) )).

cnf(u690,axiom,
    ( k5_xboole_0(X7,k7_subset_1(X8,X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k7_subset_1(X8,X8,X7)),k7_subset_1(X7,X7,k5_xboole_0(X7,k7_subset_1(X8,X8,X7)))) )).

cnf(u603,axiom,
    ( k5_xboole_0(X6,k7_subset_1(X7,X7,X6)) = k5_xboole_0(k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k7_subset_1(X6,X6,k5_xboole_0(X7,k7_subset_1(X6,X6,X7)))) )).

cnf(u652,negated_conjecture,
    ( k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))) )).

cnf(u641,negated_conjecture,
    ( k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))) )).

cnf(u732,axiom,
    ( k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) )).

cnf(u437,axiom,
    ( k7_subset_1(X5,X5,k5_xboole_0(X5,k7_subset_1(X6,X6,X5))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X6,X6,X5)),k5_xboole_0(X5,k7_subset_1(X6,X6,X5))) )).

cnf(u9580,axiom,
    ( k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))) )).

cnf(u1880,axiom,
    ( k7_subset_1(X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )).

cnf(u1711,axiom,
    ( k7_subset_1(X3,X3,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) = k5_xboole_0(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k1_setfam_1(k6_enumset1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))))) )).

cnf(u1645,axiom,
    ( k7_subset_1(X16,X16,k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17))) = k5_xboole_0(k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k1_setfam_1(k6_enumset1(k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17))))) )).

cnf(u246,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))) )).

cnf(u225,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK2) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))) )).

cnf(u1631,axiom,
    ( k5_xboole_0(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k1_setfam_1(k6_enumset1(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X10,k7_subset_1(X11,X11,X10))))) = k7_subset_1(X10,X10,k5_xboole_0(X10,k7_subset_1(X11,X11,X10))) )).

cnf(u2123,axiom,
    ( k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k5_xboole_0(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3))))) )).

cnf(u1876,axiom,
    ( k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) = k5_xboole_0(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3))))) )).

cnf(u474,axiom,
    ( k7_subset_1(X5,X5,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X6,X6,X5)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k5_xboole_0(X5,k7_subset_1(X6,X6,X5))))) )).

cnf(u455,axiom,
    ( k7_subset_1(X5,X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5))))) )).

cnf(u1744,axiom,
    ( k7_subset_1(X11,X11,k5_xboole_0(X11,k7_subset_1(X10,X10,X11))) = k5_xboole_0(k5_xboole_0(X10,k7_subset_1(X11,X11,X10)),k1_setfam_1(k6_enumset1(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X10,k7_subset_1(X11,X11,X10))))) )).

cnf(u1583,axiom,
    ( k7_subset_1(X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u393,axiom,
    ( k7_subset_1(X5,X5,k5_xboole_0(X4,k7_subset_1(X5,X5,X4))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k1_setfam_1(k6_enumset1(k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5))))) )).

cnf(u144,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))) )).

cnf(u123,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u142,axiom,
    ( k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = k5_xboole_0(X3,k7_subset_1(X2,X2,X3)) )).

cnf(u116,axiom,
    ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) )).

cnf(u136,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )).

cnf(u115,axiom,
    ( k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0) )).

cnf(u278,axiom,
    ( k4_subset_1(X0,X0,X0) = k5_xboole_0(X0,k5_xboole_0(X0,X0)) )).

cnf(u114,axiom,
    ( k3_subset_1(X0,X0) = k5_xboole_0(X0,X0) )).

cnf(u104,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) )).

cnf(u113,axiom,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 )).

cnf(u42,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u41,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u176,negated_conjecture,
    ( k1_xboole_0 != sK2
    | r1_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u177,negated_conjecture,
    ( k1_xboole_0 != sK2
    | r1_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u180,negated_conjecture,
    ( k1_xboole_0 != sK1
    | r1_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u181,negated_conjecture,
    ( k1_xboole_0 != sK1
    | r1_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u78,axiom,
    ( k1_xboole_0 != k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | r1_xboole_0(X0,X1) )).

cnf(u91,axiom,
    ( k1_xboole_0 != k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))
    | r1_xboole_0(X0,X1) )).

cnf(u194,axiom,
    ( k1_xboole_0 != X1
    | r1_xboole_0(X1,X1) )).

cnf(u39,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:12:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.44  % (15077)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (15067)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (15072)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (15065)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (15088)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (15079)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (15068)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (15084)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (15073)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (15074)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (15079)Refutation not found, incomplete strategy% (15079)------------------------------
% 0.21/0.52  % (15079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15079)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15079)Memory used [KB]: 6140
% 0.21/0.52  % (15079)Time elapsed: 0.003 s
% 0.21/0.52  % (15079)------------------------------
% 0.21/0.52  % (15079)------------------------------
% 0.21/0.52  % (15071)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (15064)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (15076)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15090)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (15064)Refutation not found, incomplete strategy% (15064)------------------------------
% 0.21/0.53  % (15064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15064)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15064)Memory used [KB]: 1663
% 0.21/0.53  % (15064)Time elapsed: 0.115 s
% 0.21/0.53  % (15064)------------------------------
% 0.21/0.53  % (15064)------------------------------
% 0.21/0.53  % (15082)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (15092)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (15081)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (15080)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15093)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (15066)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (15070)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (15074)Refutation not found, incomplete strategy% (15074)------------------------------
% 0.21/0.54  % (15074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15074)Memory used [KB]: 10618
% 0.21/0.54  % (15074)Time elapsed: 0.107 s
% 0.21/0.54  % (15074)------------------------------
% 0.21/0.54  % (15074)------------------------------
% 0.21/0.54  % (15073)Refutation not found, incomplete strategy% (15073)------------------------------
% 0.21/0.54  % (15073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15073)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15073)Memory used [KB]: 10746
% 0.21/0.54  % (15073)Time elapsed: 0.108 s
% 0.21/0.54  % (15073)------------------------------
% 0.21/0.54  % (15073)------------------------------
% 0.21/0.54  % (15089)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (15083)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (15085)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (15075)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (15081)Refutation not found, incomplete strategy% (15081)------------------------------
% 0.21/0.55  % (15081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15075)Refutation not found, incomplete strategy% (15075)------------------------------
% 0.21/0.55  % (15075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (15075)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15075)Memory used [KB]: 10746
% 0.21/0.55  % (15075)Time elapsed: 0.142 s
% 0.21/0.55  % (15075)------------------------------
% 0.21/0.55  % (15075)------------------------------
% 0.21/0.55  % (15081)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (15081)Memory used [KB]: 10618
% 0.21/0.55  % (15081)Time elapsed: 0.126 s
% 0.21/0.55  % (15081)------------------------------
% 0.21/0.55  % (15081)------------------------------
% 0.21/0.55  % (15069)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (15086)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (15094)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (15086)Refutation not found, incomplete strategy% (15086)------------------------------
% 0.21/0.56  % (15086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (15086)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (15086)Memory used [KB]: 10746
% 0.21/0.56  % (15086)Time elapsed: 0.150 s
% 0.21/0.56  % (15086)------------------------------
% 0.21/0.56  % (15086)------------------------------
% 0.21/0.57  % (15091)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (15078)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (15071)Refutation not found, incomplete strategy% (15071)------------------------------
% 0.21/0.57  % (15071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (15071)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.59  
% 1.67/0.59  % (15071)Memory used [KB]: 6780
% 1.67/0.59  % (15071)Time elapsed: 0.137 s
% 1.67/0.59  % (15071)------------------------------
% 1.67/0.59  % (15071)------------------------------
% 2.10/0.64  % (15182)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.10/0.66  % (15201)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.10/0.67  % (15197)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.10/0.68  % (15194)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.10/0.68  % (15186)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.10/0.69  % (15206)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.63/0.70  % (15202)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.63/0.71  % (15065)Refutation not found, incomplete strategy% (15065)------------------------------
% 2.63/0.71  % (15065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.71  % (15065)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.71  
% 2.63/0.71  % (15065)Memory used [KB]: 6268
% 2.63/0.71  % (15065)Time elapsed: 0.298 s
% 2.63/0.71  % (15065)------------------------------
% 2.63/0.71  % (15065)------------------------------
% 2.63/0.72  % (15217)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.63/0.74  % (15072)Refutation not found, incomplete strategy% (15072)------------------------------
% 2.63/0.74  % (15072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.74  % (15072)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.74  
% 2.63/0.74  % (15072)Memory used [KB]: 12409
% 2.63/0.74  % (15072)Time elapsed: 0.325 s
% 2.63/0.74  % (15072)------------------------------
% 2.63/0.74  % (15072)------------------------------
% 2.63/0.76  % (15066)Refutation not found, incomplete strategy% (15066)------------------------------
% 2.63/0.76  % (15066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.77  % (15206)Refutation not found, incomplete strategy% (15206)------------------------------
% 3.15/0.77  % (15206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.77  % (15206)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.77  
% 3.15/0.77  % (15206)Memory used [KB]: 2302
% 3.15/0.77  % (15206)Time elapsed: 0.184 s
% 3.15/0.77  % (15206)------------------------------
% 3.15/0.77  % (15206)------------------------------
% 3.15/0.77  % (15066)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.77  
% 3.15/0.77  % (15066)Memory used [KB]: 12792
% 3.15/0.77  % (15066)Time elapsed: 0.346 s
% 3.15/0.77  % (15066)------------------------------
% 3.15/0.77  % (15066)------------------------------
% 3.15/0.80  % (15090)Refutation not found, incomplete strategy% (15090)------------------------------
% 3.15/0.80  % (15090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.80  % (15090)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.80  
% 3.15/0.80  % (15090)Memory used [KB]: 9210
% 3.15/0.80  % (15090)Time elapsed: 0.395 s
% 3.15/0.80  % (15090)------------------------------
% 3.15/0.80  % (15090)------------------------------
% 3.15/0.82  % (15186)Refutation not found, incomplete strategy% (15186)------------------------------
% 3.15/0.82  % (15186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.82  % (15186)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.82  
% 3.15/0.82  % (15186)Memory used [KB]: 6268
% 3.15/0.82  % (15186)Time elapsed: 0.259 s
% 3.15/0.82  % (15186)------------------------------
% 3.15/0.82  % (15186)------------------------------
% 3.15/0.83  % (15069)Time limit reached!
% 3.15/0.83  % (15069)------------------------------
% 3.15/0.83  % (15069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.83  % (15069)Termination reason: Time limit
% 3.15/0.83  % (15069)Termination phase: Saturation
% 3.15/0.83  
% 3.15/0.83  % (15069)Memory used [KB]: 10106
% 3.15/0.83  % (15069)Time elapsed: 0.400 s
% 3.15/0.83  % (15069)------------------------------
% 3.15/0.83  % (15069)------------------------------
% 3.15/0.83  % (15085)Refutation not found, incomplete strategy% (15085)------------------------------
% 3.15/0.83  % (15085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.15/0.83  % (15085)Termination reason: Refutation not found, incomplete strategy
% 3.15/0.83  
% 3.15/0.83  % (15085)Memory used [KB]: 3837
% 3.15/0.83  % (15085)Time elapsed: 0.421 s
% 3.15/0.83  % (15085)------------------------------
% 3.15/0.83  % (15085)------------------------------
% 3.15/0.85  % (15253)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.15/0.86  % (15255)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.82/0.89  % (15280)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 3.96/0.90  % (15282)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.96/0.90  % (15293)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 3.96/0.91  % (15076)Time limit reached!
% 3.96/0.91  % (15076)------------------------------
% 3.96/0.91  % (15076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.91  % (15076)Termination reason: Time limit
% 3.96/0.91  
% 3.96/0.91  % (15076)Memory used [KB]: 8699
% 3.96/0.91  % (15076)Time elapsed: 0.503 s
% 3.96/0.91  % (15076)------------------------------
% 3.96/0.91  % (15076)------------------------------
% 4.16/0.95  % (15299)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 4.16/0.95  % (15297)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 4.16/0.96  % (15298)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 4.16/0.99  % (15197)Time limit reached!
% 4.16/0.99  % (15197)------------------------------
% 4.16/0.99  % (15197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.16/0.99  % (15197)Termination reason: Time limit
% 4.16/0.99  % (15197)Termination phase: Saturation
% 4.16/0.99  
% 4.16/0.99  % (15197)Memory used [KB]: 6908
% 4.16/0.99  % (15197)Time elapsed: 0.400 s
% 4.16/1.00  % (15197)------------------------------
% 4.16/1.00  % (15197)------------------------------
% 4.55/1.02  % (15201)Time limit reached!
% 4.55/1.02  % (15201)------------------------------
% 4.55/1.02  % (15201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.02  % (15201)Termination reason: Time limit
% 4.55/1.02  
% 4.55/1.02  % (15201)Memory used [KB]: 14711
% 4.55/1.02  % (15201)Time elapsed: 0.414 s
% 4.55/1.02  % (15201)------------------------------
% 4.55/1.02  % (15201)------------------------------
% 4.55/1.03  % (15093)Time limit reached!
% 4.55/1.03  % (15093)------------------------------
% 4.55/1.03  % (15093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.03  % (15093)Termination reason: Time limit
% 4.55/1.03  
% 4.55/1.03  % (15093)Memory used [KB]: 8315
% 4.55/1.03  % (15093)Time elapsed: 0.624 s
% 4.55/1.03  % (15093)------------------------------
% 4.55/1.03  % (15093)------------------------------
% 4.55/1.04  % (15300)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.55/1.04  % (15080)Time limit reached!
% 4.55/1.04  % (15080)------------------------------
% 4.55/1.04  % (15080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/1.04  % (15080)Termination reason: Time limit
% 4.55/1.04  % (15080)Termination phase: Saturation
% 4.55/1.04  
% 4.55/1.04  % (15080)Memory used [KB]: 15479
% 4.55/1.05  % (15080)Time elapsed: 0.600 s
% 4.55/1.05  % (15080)------------------------------
% 4.55/1.05  % (15080)------------------------------
% 5.63/1.13  % (15301)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 5.63/1.14  % (15303)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 5.63/1.15  % (15302)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.41/1.19  % (15304)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.54/1.35  % (15300)Time limit reached!
% 7.54/1.35  % (15300)------------------------------
% 7.54/1.35  % (15300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.54/1.35  % (15300)Termination reason: Time limit
% 7.54/1.35  % (15300)Termination phase: Saturation
% 7.54/1.35  
% 7.54/1.35  % (15300)Memory used [KB]: 4605
% 7.54/1.35  % (15300)Time elapsed: 0.400 s
% 7.54/1.35  % (15300)------------------------------
% 7.54/1.35  % (15300)------------------------------
% 7.54/1.36  % (15293)Time limit reached!
% 7.54/1.36  % (15293)------------------------------
% 7.54/1.36  % (15293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.54/1.36  % (15293)Termination reason: Time limit
% 7.54/1.36  % (15293)Termination phase: Saturation
% 7.54/1.36  
% 7.54/1.36  % (15293)Memory used [KB]: 2558
% 7.54/1.36  % (15293)Time elapsed: 0.500 s
% 7.54/1.36  % (15293)------------------------------
% 7.54/1.36  % (15293)------------------------------
% 8.11/1.46  % (15305)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.73/1.50  % (15303)Time limit reached!
% 8.73/1.50  % (15303)------------------------------
% 8.73/1.50  % (15303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.73/1.50  % (15303)Termination reason: Time limit
% 8.73/1.50  
% 8.73/1.50  % (15303)Memory used [KB]: 3070
% 8.73/1.50  % (15303)Time elapsed: 0.410 s
% 8.73/1.50  % (15303)------------------------------
% 8.73/1.50  % (15303)------------------------------
% 8.95/1.51  % (15306)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.78/1.62  % (15091)Time limit reached!
% 9.78/1.62  % (15091)------------------------------
% 9.78/1.62  % (15091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.78/1.62  % (15307)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 9.78/1.63  % (15091)Termination reason: Time limit
% 9.78/1.63  
% 9.78/1.63  % (15091)Memory used [KB]: 15991
% 9.78/1.63  % (15091)Time elapsed: 1.216 s
% 9.78/1.63  % (15091)------------------------------
% 9.78/1.63  % (15091)------------------------------
% 10.52/1.71  % (15089)Time limit reached!
% 10.52/1.71  % (15089)------------------------------
% 10.52/1.71  % (15089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.52/1.71  % (15089)Termination reason: Time limit
% 10.52/1.71  
% 10.52/1.71  % (15089)Memory used [KB]: 18166
% 10.52/1.71  % (15089)Time elapsed: 1.304 s
% 10.52/1.71  % (15089)------------------------------
% 10.52/1.71  % (15089)------------------------------
% 10.52/1.75  % (15307)Refutation not found, incomplete strategy% (15307)------------------------------
% 10.52/1.75  % (15307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.52/1.76  % (15307)Termination reason: Refutation not found, incomplete strategy
% 10.52/1.76  
% 10.52/1.76  % (15307)Memory used [KB]: 6268
% 10.52/1.76  % (15307)Time elapsed: 0.227 s
% 10.52/1.76  % (15307)------------------------------
% 10.52/1.76  % (15307)------------------------------
% 10.52/1.77  % (15308)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.46/1.86  % (15310)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.46/1.86  % (15309)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 12.16/1.93  % (15092)Time limit reached!
% 12.16/1.93  % (15092)------------------------------
% 12.16/1.93  % (15092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.16/1.93  % (15092)Termination reason: Time limit
% 12.16/1.93  % (15092)Termination phase: Saturation
% 12.16/1.93  
% 12.16/1.93  % (15092)Memory used [KB]: 15991
% 12.16/1.93  % (15092)Time elapsed: 1.500 s
% 12.16/1.93  % (15092)------------------------------
% 12.16/1.93  % (15092)------------------------------
% 12.16/1.93  % (15068)Time limit reached!
% 12.16/1.93  % (15068)------------------------------
% 12.16/1.93  % (15068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.16/1.93  % (15068)Termination reason: Time limit
% 12.16/1.93  % (15068)Termination phase: Saturation
% 12.16/1.93  
% 12.16/1.93  % (15068)Memory used [KB]: 28784
% 12.16/1.93  % (15068)Time elapsed: 1.500 s
% 12.16/1.93  % (15068)------------------------------
% 12.16/1.93  % (15068)------------------------------
% 12.77/2.03  % (15311)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 12.77/2.06  % (15299)Time limit reached!
% 12.77/2.06  % (15299)------------------------------
% 12.77/2.06  % (15299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.77/2.06  % (15299)Termination reason: Time limit
% 12.77/2.06  
% 12.77/2.07  % (15299)Memory used [KB]: 15863
% 12.77/2.07  % (15299)Time elapsed: 1.217 s
% 12.77/2.07  % (15299)------------------------------
% 12.77/2.07  % (15299)------------------------------
% 13.46/2.09  % (15308)Time limit reached!
% 13.46/2.09  % (15308)------------------------------
% 13.46/2.09  % (15308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.46/2.09  % (15308)Termination reason: Time limit
% 13.46/2.09  
% 13.46/2.09  % (15308)Memory used [KB]: 9210
% 13.46/2.09  % (15308)Time elapsed: 0.434 s
% 13.46/2.09  % (15308)------------------------------
% 13.46/2.09  % (15308)------------------------------
% 14.75/2.22  % (15078)Time limit reached!
% 14.75/2.22  % (15078)------------------------------
% 14.75/2.22  % (15078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.22  % (15078)Termination reason: Time limit
% 14.75/2.22  % (15078)Termination phase: Saturation
% 14.75/2.22  
% 14.75/2.22  % (15078)Memory used [KB]: 8059
% 14.75/2.22  % (15078)Time elapsed: 1.824 s
% 14.75/2.22  % (15078)------------------------------
% 14.75/2.22  % (15078)------------------------------
% 14.75/2.23  % (15310)Time limit reached!
% 14.75/2.23  % (15310)------------------------------
% 14.75/2.23  % (15310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.23  % (15310)Termination reason: Time limit
% 14.75/2.23  % (15310)Termination phase: Saturation
% 14.75/2.23  
% 14.75/2.23  % (15310)Memory used [KB]: 21364
% 14.75/2.23  % (15310)Time elapsed: 0.400 s
% 14.75/2.23  % (15310)------------------------------
% 14.75/2.23  % (15310)------------------------------
% 14.75/2.27  % (15194)Time limit reached!
% 14.75/2.27  % (15194)------------------------------
% 14.75/2.27  % (15194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.27  % (15194)Termination reason: Time limit
% 14.75/2.27  % (15194)Termination phase: Saturation
% 14.75/2.27  
% 14.75/2.27  % (15194)Memory used [KB]: 19957
% 14.75/2.27  % (15194)Time elapsed: 1.700 s
% 14.75/2.27  % (15194)------------------------------
% 14.75/2.27  % (15194)------------------------------
% 15.39/2.35  % (15302)Time limit reached!
% 15.39/2.35  % (15302)------------------------------
% 15.39/2.35  % (15302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.39/2.35  % (15302)Termination reason: Time limit
% 15.39/2.35  % (15302)Termination phase: Saturation
% 15.39/2.35  
% 15.39/2.35  % (15302)Memory used [KB]: 12792
% 15.39/2.35  % (15302)Time elapsed: 1.300 s
% 15.39/2.35  % (15302)------------------------------
% 15.39/2.35  % (15302)------------------------------
% 16.11/2.40  % (15082)Time limit reached!
% 16.11/2.40  % (15082)------------------------------
% 16.11/2.40  % (15082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.11/2.42  % (15082)Termination reason: Time limit
% 16.11/2.42  % (15082)Termination phase: Saturation
% 16.11/2.42  
% 16.11/2.42  % (15082)Memory used [KB]: 16630
% 16.11/2.42  % (15082)Time elapsed: 2.0000 s
% 16.11/2.42  % (15082)------------------------------
% 16.11/2.42  % (15082)------------------------------
% 16.11/2.44  % (15070)Time limit reached!
% 16.11/2.44  % (15070)------------------------------
% 16.11/2.44  % (15070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.11/2.44  % (15070)Termination reason: Time limit
% 16.11/2.44  
% 16.11/2.44  % (15070)Memory used [KB]: 16375
% 16.11/2.44  % (15070)Time elapsed: 2.028 s
% 16.11/2.44  % (15070)------------------------------
% 16.11/2.44  % (15070)------------------------------
% 17.12/2.53  % (15253)Time limit reached!
% 17.12/2.53  % (15253)------------------------------
% 17.12/2.53  % (15253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.12/2.54  % (15253)Termination reason: Time limit
% 17.12/2.54  % (15253)Termination phase: Saturation
% 17.12/2.54  
% 17.12/2.54  % (15253)Memory used [KB]: 50916
% 17.12/2.54  % (15253)Time elapsed: 1.700 s
% 17.12/2.54  % (15253)------------------------------
% 17.12/2.54  % (15253)------------------------------
% 20.90/3.02  % (15083)Time limit reached!
% 20.90/3.02  % (15083)------------------------------
% 20.90/3.02  % (15083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.90/3.03  % (15083)Termination reason: Time limit
% 20.90/3.03  % (15083)Termination phase: Saturation
% 20.90/3.03  
% 20.90/3.03  % (15083)Memory used [KB]: 25202
% 20.90/3.03  % (15083)Time elapsed: 2.600 s
% 20.90/3.03  % (15083)------------------------------
% 20.90/3.03  % (15083)------------------------------
% 24.46/3.44  % (15077)Time limit reached!
% 24.46/3.44  % (15077)------------------------------
% 24.46/3.44  % (15077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.46/3.44  % (15077)Termination reason: Time limit
% 24.46/3.44  % (15077)Termination phase: Saturation
% 24.46/3.44  
% 24.46/3.44  % (15077)Memory used [KB]: 14711
% 24.46/3.44  % (15077)Time elapsed: 3.0000 s
% 24.46/3.44  % (15077)------------------------------
% 24.46/3.44  % (15077)------------------------------
% 31.39/4.31  % (15094)Time limit reached!
% 31.39/4.31  % (15094)------------------------------
% 31.39/4.31  % (15094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.39/4.31  % (15094)Termination reason: Time limit
% 31.39/4.31  
% 31.39/4.31  % (15094)Memory used [KB]: 30191
% 31.39/4.31  % (15094)Time elapsed: 3.906 s
% 31.39/4.31  % (15094)------------------------------
% 31.39/4.31  % (15094)------------------------------
% 31.69/4.38  % (15298)Time limit reached!
% 31.69/4.38  % (15298)------------------------------
% 31.69/4.38  % (15298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.69/4.40  % (15298)Termination reason: Time limit
% 31.69/4.40  
% 31.69/4.40  % (15298)Memory used [KB]: 37355
% 31.69/4.40  % (15298)Time elapsed: 3.530 s
% 31.69/4.40  % (15298)------------------------------
% 31.69/4.40  % (15298)------------------------------
% 41.15/5.61  % (15067)Time limit reached!
% 41.15/5.61  % (15067)------------------------------
% 41.15/5.61  % (15067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 41.15/5.61  % (15067)Termination reason: Time limit
% 41.15/5.61  % (15067)Termination phase: Saturation
% 41.15/5.61  
% 41.15/5.61  % (15067)Memory used [KB]: 41449
% 41.15/5.61  % (15067)Time elapsed: 5.200 s
% 41.15/5.61  % (15067)------------------------------
% 41.15/5.61  % (15067)------------------------------
% 46.55/6.19  % (15217)Time limit reached!
% 46.55/6.19  % (15217)------------------------------
% 46.55/6.19  % (15217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 46.55/6.19  % (15217)Termination reason: Time limit
% 46.55/6.19  
% 46.55/6.19  % (15217)Memory used [KB]: 31214
% 46.55/6.19  % (15217)Time elapsed: 5.560 s
% 46.55/6.19  % (15217)------------------------------
% 46.55/6.19  % (15217)------------------------------
% 49.18/6.57  % (15311)Time limit reached!
% 49.18/6.57  % (15311)------------------------------
% 49.18/6.57  % (15311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 49.18/6.57  % (15311)Termination reason: Time limit
% 49.18/6.57  % (15311)Termination phase: Saturation
% 49.18/6.57  
% 49.18/6.57  % (15311)Memory used [KB]: 156074
% 49.18/6.57  % (15311)Time elapsed: 4.600 s
% 49.18/6.57  % (15311)------------------------------
% 49.18/6.57  % (15311)------------------------------
% 52.83/6.98  % (15304)Time limit reached!
% 52.83/6.98  % (15304)------------------------------
% 52.83/6.98  % (15304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 52.83/6.98  % (15304)Termination reason: Time limit
% 52.83/6.98  % (15304)Termination phase: Saturation
% 52.83/6.98  
% 52.83/6.98  % (15304)Memory used [KB]: 31214
% 52.83/6.98  % (15304)Time elapsed: 5.900 s
% 52.83/6.98  % (15304)------------------------------
% 52.83/6.98  % (15304)------------------------------
% 58.79/7.77  % SZS status CounterSatisfiable for theBenchmark
% 58.79/7.77  % (15306)# SZS output start Saturation.
% 58.79/7.77  cnf(u40,negated_conjecture,
% 58.79/7.77      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u36,negated_conjecture,
% 58.79/7.77      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u81,axiom,
% 58.79/7.77      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u119,negated_conjecture,
% 58.79/7.77      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u120,negated_conjecture,
% 58.79/7.77      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X3))).
% 58.79/7.77  
% 58.79/7.77  cnf(u56,axiom,
% 58.79/7.77      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u102,axiom,
% 58.79/7.77      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u101,axiom,
% 58.79/7.77      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u80,axiom,
% 58.79/7.77      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u118,axiom,
% 58.79/7.77      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k4_subset_1(X1,X1,X0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u86,negated_conjecture,
% 58.79/7.77      r1_tarski(sK1,u1_struct_0(sK0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u85,negated_conjecture,
% 58.79/7.77      r1_tarski(sK2,u1_struct_0(sK0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u84,axiom,
% 58.79/7.77      r1_tarski(X0,X0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u75,axiom,
% 58.79/7.77      ~r1_tarski(X0,X1) | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0).
% 58.79/7.77  
% 58.79/7.77  cnf(u335,axiom,
% 58.79/7.77      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u83,negated_conjecture,
% 58.79/7.77      r1_xboole_0(sK2,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u38,negated_conjecture,
% 58.79/7.77      r1_xboole_0(sK1,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u52,axiom,
% 58.79/7.77      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u77,axiom,
% 58.79/7.77      ~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))).
% 58.79/7.77  
% 58.79/7.77  cnf(u127,negated_conjecture,
% 58.79/7.77      sK1 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u124,negated_conjecture,
% 58.79/7.77      sK2 = k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u88,negated_conjecture,
% 58.79/7.77      k1_xboole_0 = k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u360,negated_conjecture,
% 58.79/7.77      sK2 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u297,negated_conjecture,
% 58.79/7.77      sK2 = k7_subset_1(sK2,sK2,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u356,negated_conjecture,
% 58.79/7.77      sK1 = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u139,negated_conjecture,
% 58.79/7.77      sK1 = k7_subset_1(sK1,sK1,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u396,axiom,
% 58.79/7.77      k7_subset_1(X1,X1,k4_subset_1(X1,X1,X1)) = k7_subset_1(k4_subset_1(X1,X1,X1),k4_subset_1(X1,X1,X1),k4_subset_1(X1,X1,X1))).
% 58.79/7.77  
% 58.79/7.77  cnf(u4446,axiom,
% 58.79/7.77      k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k7_subset_1(X3,X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1375,axiom,
% 58.79/7.77      k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1136,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1297,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k7_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1104,axiom,
% 58.79/7.77      k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6))) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1373,axiom,
% 58.79/7.77      k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1165,axiom,
% 58.79/7.77      k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u476,axiom,
% 58.79/7.77      k7_subset_1(X13,X13,k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14))) = k7_subset_1(k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u457,axiom,
% 58.79/7.77      k7_subset_1(X13,X13,k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13))) = k7_subset_1(k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1491,axiom,
% 58.79/7.77      k7_subset_1(X15,X15,k5_xboole_0(X15,k7_subset_1(X16,X16,X15))) = k7_subset_1(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1014,axiom,
% 58.79/7.77      k7_subset_1(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k5_xboole_0(X9,k7_subset_1(X8,X8,X9))) = k7_subset_1(X9,X9,k5_xboole_0(X9,k7_subset_1(X8,X8,X9)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1003,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k7_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u896,axiom,
% 58.79/7.77      k7_subset_1(X6,X6,k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2907,axiom,
% 58.79/7.77      k7_subset_1(X3,X3,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1011,axiom,
% 58.79/7.77      k7_subset_1(k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) = k7_subset_1(X7,X7,k5_xboole_0(X7,k7_subset_1(X6,X6,X7)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u960,axiom,
% 58.79/7.77      k7_subset_1(X10,X10,k5_xboole_0(X11,k7_subset_1(X10,X10,X11))) = k7_subset_1(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u428,axiom,
% 58.79/7.77      k7_subset_1(X13,X13,k5_xboole_0(X13,k7_subset_1(X14,X14,X13))) = k7_subset_1(k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k5_xboole_0(X13,k7_subset_1(X14,X14,X13)),k5_xboole_0(X13,k7_subset_1(X14,X14,X13)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u379,axiom,
% 58.79/7.77      k7_subset_1(X3,X3,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u517,negated_conjecture,
% 58.79/7.77      k7_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u509,negated_conjecture,
% 58.79/7.77      k7_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u516,negated_conjecture,
% 58.79/7.77      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u508,negated_conjecture,
% 58.79/7.77      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u293,axiom,
% 58.79/7.77      k7_subset_1(X8,X8,X7) = k7_subset_1(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)),X7)).
% 58.79/7.77  
% 58.79/7.77  cnf(u292,axiom,
% 58.79/7.77      k7_subset_1(X5,X5,X6) = k7_subset_1(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),X6)).
% 58.79/7.77  
% 58.79/7.77  cnf(u326,axiom,
% 58.79/7.77      k7_subset_1(X4,X4,X3) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X3)).
% 58.79/7.77  
% 58.79/7.77  cnf(u291,axiom,
% 58.79/7.77      k7_subset_1(X3,X3,X4) = k7_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),X4)).
% 58.79/7.77  
% 58.79/7.77  cnf(u106,negated_conjecture,
% 58.79/7.77      k7_subset_1(u1_struct_0(sK0),sK1,X3) = k7_subset_1(sK1,sK1,X3)).
% 58.79/7.77  
% 58.79/7.77  cnf(u105,negated_conjecture,
% 58.79/7.77      k7_subset_1(u1_struct_0(sK0),sK2,X2) = k7_subset_1(sK2,sK2,X2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u398,negated_conjecture,
% 58.79/7.77      k5_xboole_0(u1_struct_0(sK0),sK2) = k7_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u400,negated_conjecture,
% 58.79/7.77      k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u497,negated_conjecture,
% 58.79/7.77      k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)) = k7_subset_1(sK1,sK1,k2_struct_0(sK0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u98,axiom,
% 58.79/7.77      k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X0,X0,X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u103,axiom,
% 58.79/7.77      k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) = k7_subset_1(X0,X0,X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u515,negated_conjecture,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))) = k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u507,negated_conjecture,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))) = k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u312,axiom,
% 58.79/7.77      k5_xboole_0(X1,X1) = k7_subset_1(k4_subset_1(X1,X1,X1),k4_subset_1(X1,X1,X1),X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u548,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k4_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u155,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u37,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u522,axiom,
% 58.79/7.77      k4_subset_1(X0,X0,X0) = k4_subset_1(k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0),k4_subset_1(X0,X0,X0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u160,negated_conjecture,
% 58.79/7.77      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_subset_1(sK1,sK1,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u159,negated_conjecture,
% 58.79/7.77      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k4_subset_1(sK2,sK2,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u50545,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)))) = k4_subset_1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u50531,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9)))) = k4_subset_1(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u50525,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k4_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u40110,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)) = k4_subset_1(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u52318,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X42,X42,X42,X42,X42,X42,X42,k3_tarski(k6_enumset1(X42,X42,X42,X42,X42,X42,X42,X43)))) = k4_subset_1(k3_tarski(k6_enumset1(X43,X43,X43,X43,X43,X43,X43,X42)),k3_tarski(k6_enumset1(X43,X43,X43,X43,X43,X43,X43,X42)),k3_tarski(k6_enumset1(X43,X43,X43,X43,X43,X43,X43,X42)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u49520,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9)) = k4_subset_1(k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)),k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)),k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3204,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u156,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = k4_subset_1(X0,X0,X0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u45381,axiom,
% 58.79/7.77      k5_xboole_0(X3,k7_subset_1(X2,X2,X3)) = k4_subset_1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u45380,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k4_subset_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2505,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2480,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u38563,axiom,
% 58.79/7.77      k5_xboole_0(X8,k7_subset_1(X7,X7,X8)) = k4_subset_1(k5_xboole_0(X7,k7_subset_1(X8,X8,X7)),k5_xboole_0(X7,k7_subset_1(X8,X8,X7)),k5_xboole_0(X7,k7_subset_1(X8,X8,X7)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u753,axiom,
% 58.79/7.77      k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = k4_subset_1(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u355,axiom,
% 58.79/7.77      k1_xboole_0 = k4_subset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u2432,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k3_tarski(k6_enumset1(k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u651,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u661,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u154,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u618,axiom,
% 58.79/7.77      k4_subset_1(X5,X5,X5) = k3_tarski(k6_enumset1(k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5),k4_subset_1(X5,X5,X5)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u611,axiom,
% 58.79/7.77      k4_subset_1(X0,X0,X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_subset_1(X0,X0,X0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u18692,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X3)))) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k5_xboole_0(X4,k7_subset_1(X3,X3,X4))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3947,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))) = k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9))).
% 58.79/7.77  
% 58.79/7.77  cnf(u18691,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X2,X1)))) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3206,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)))) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u28697,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X18,X18,X18,X18,X18,X18,X18,X19)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k3_tarski(k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X18)),k5_xboole_0(X18,k7_subset_1(X19,X19,X18))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u21845,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u16404,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3995,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X36)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X36))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u4026,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X24,X24,X24,X24,X24,X24,X24,X25)),k3_tarski(k6_enumset1(X25,X25,X25,X25,X25,X25,X25,X24))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3822,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X15))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u8351,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k5_xboole_0(X38,k7_subset_1(X39,X39,X38))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u708,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u16756,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X33,X33,X33,X33,X33,X33,X33,X32)) = k3_tarski(k6_enumset1(k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32)),k5_xboole_0(X32,k7_subset_1(X33,X33,X32))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u22083,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X50,X50,X50,X50,X50,X50,X50,X51)) = k3_tarski(k6_enumset1(k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X51,k7_subset_1(X50,X50,X51)),k5_xboole_0(X50,k7_subset_1(X51,X51,X50))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u22075,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X48,X48,X48,X48,X48,X48,X48,X49)) = k3_tarski(k6_enumset1(k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k5_xboole_0(X49,k7_subset_1(X48,X48,X49)),k3_tarski(k6_enumset1(X49,X49,X49,X49,X49,X49,X49,X48))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u6596,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X49,X49,X49,X49,X49,X49,X49,X48)) = k3_tarski(k6_enumset1(k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k5_xboole_0(X48,k7_subset_1(X49,X49,X48)),k3_tarski(k6_enumset1(X49,X49,X49,X49,X49,X49,X49,X48))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u22184,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) = k3_tarski(k6_enumset1(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2604,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)) = k3_tarski(k6_enumset1(k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k5_xboole_0(X16,k7_subset_1(X17,X17,X16)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u21489,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)) = k3_tarski(k6_enumset1(k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u13492,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) = k3_tarski(k6_enumset1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X4,k7_subset_1(X3,X3,X4))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3946,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X7)) = k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,k5_xboole_0(X8,k7_subset_1(X7,X7,X8))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u815,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)) = k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u688,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)) = k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u143,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u16219,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u15744,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u16825,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)) = k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u689,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)) = k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u502,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u510,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u654,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u643,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u39483,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u20035,axiom,
% 58.79/7.77      k5_xboole_0(X38,k7_subset_1(X39,X39,X38)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38)),k3_tarski(k6_enumset1(X39,X39,X39,X39,X39,X39,X39,X38))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u26513,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u13695,axiom,
% 58.79/7.77      k5_xboole_0(X31,k7_subset_1(X30,X30,X31)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u20693,axiom,
% 58.79/7.77      k5_xboole_0(X12,k7_subset_1(X13,X13,X12)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u5099,axiom,
% 58.79/7.77      k5_xboole_0(X22,k7_subset_1(X21,X21,X22)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k5_xboole_0(X21,k7_subset_1(X22,X22,X21))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2544,axiom,
% 58.79/7.77      k5_xboole_0(X3,k7_subset_1(X4,X4,X3)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u622,axiom,
% 58.79/7.77      k5_xboole_0(X9,k7_subset_1(X8,X8,X9)) = k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k5_xboole_0(X9,k7_subset_1(X8,X8,X9))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u33133,axiom,
% 58.79/7.77      k5_xboole_0(X136,k7_subset_1(X135,X135,X136)) = k3_tarski(k6_enumset1(k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k5_xboole_0(X135,k7_subset_1(X136,X136,X135)),k3_tarski(k6_enumset1(X136,X136,X136,X136,X136,X136,X136,X135))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u15950,axiom,
% 58.79/7.77      k5_xboole_0(X21,k7_subset_1(X20,X20,X21)) = k3_tarski(k6_enumset1(k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k5_xboole_0(X20,k7_subset_1(X21,X21,X20)),k3_tarski(k6_enumset1(X20,X20,X20,X20,X20,X20,X20,X21))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u8176,axiom,
% 58.79/7.77      k5_xboole_0(X37,k7_subset_1(X36,X36,X37)) = k3_tarski(k6_enumset1(k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u8159,axiom,
% 58.79/7.77      k5_xboole_0(X31,k7_subset_1(X30,X30,X31)) = k3_tarski(k6_enumset1(k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k5_xboole_0(X31,k7_subset_1(X30,X30,X31)),k3_tarski(k6_enumset1(X31,X31,X31,X31,X31,X31,X31,X30))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u13749,axiom,
% 58.79/7.77      k5_xboole_0(X13,k7_subset_1(X12,X12,X13)) = k3_tarski(k6_enumset1(k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u8123,axiom,
% 58.79/7.77      k5_xboole_0(X13,k7_subset_1(X12,X12,X13)) = k3_tarski(k6_enumset1(k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X13,k7_subset_1(X12,X12,X13)),k5_xboole_0(X12,k7_subset_1(X13,X13,X12))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u620,axiom,
% 58.79/7.77      k5_xboole_0(X7,k7_subset_1(X6,X6,X7)) = k3_tarski(k6_enumset1(k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u613,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k3_tarski(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1)),k5_xboole_0(X1,k7_subset_1(X2,X2,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u638,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k3_tarski(k6_enumset1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u634,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k3_tarski(k6_enumset1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u16671,axiom,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(X52,k7_subset_1(X51,X51,X52)),k7_subset_1(X51,X51,k5_xboole_0(X52,k7_subset_1(X51,X51,X52)))) = k3_tarski(k6_enumset1(X51,X51,X51,X51,X51,X51,X51,k3_tarski(k6_enumset1(X51,X51,X51,X51,X51,X51,X51,X52))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u18359,axiom,
% 58.79/7.77      k5_xboole_0(k3_tarski(k6_enumset1(X38,X38,X38,X38,X38,X38,X38,X37)),k7_subset_1(X37,X37,k3_tarski(k6_enumset1(X38,X38,X38,X38,X38,X38,X38,X37)))) = k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,k3_tarski(k6_enumset1(X37,X37,X37,X37,X37,X37,X37,X38))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3214,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u813,axiom,
% 58.79/7.77      k5_xboole_0(X3,k7_subset_1(X2,X2,X3)) = k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u3280,axiom,
% 58.79/7.77      k5_xboole_0(X12,k7_subset_1(X13,X13,X12)) = k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,k5_xboole_0(X13,k7_subset_1(X12,X12,X13))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u686,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u21874,axiom,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(X28,k7_subset_1(X29,X29,X28)),k7_subset_1(X29,X29,k5_xboole_0(X28,k7_subset_1(X29,X29,X28)))) = k3_tarski(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,k3_tarski(k6_enumset1(X28,X28,X28,X28,X28,X28,X28,X29))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u473,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u454,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u425,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X2,X2,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X2,X2,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u392,axiom,
% 58.79/7.77      k5_xboole_0(X1,k7_subset_1(X0,X0,X1)) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2430,axiom,
% 58.79/7.77      k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u72,axiom,
% 58.79/7.77      k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u189,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k5_xboole_0(sK2,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u331,negated_conjecture,
% 58.79/7.77      k7_subset_1(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u175,negated_conjecture,
% 58.79/7.77      k7_subset_1(sK2,sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u223,negated_conjecture,
% 58.79/7.77      k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u222,negated_conjecture,
% 58.79/7.77      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u221,negated_conjecture,
% 58.79/7.77      k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK0))) = k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u178,negated_conjecture,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))) = k5_xboole_0(sK2,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u298,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k5_xboole_0(sK1,sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u333,negated_conjecture,
% 58.79/7.77      k7_subset_1(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u179,negated_conjecture,
% 58.79/7.77      k7_subset_1(sK1,sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u182,negated_conjecture,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_setfam_1(k6_enumset1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0),k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))) = k5_xboole_0(sK1,sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u242,negated_conjecture,
% 58.79/7.77      k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,u1_struct_0(sK0))) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))).
% 58.79/7.77  
% 58.79/7.77  cnf(u244,negated_conjecture,
% 58.79/7.77      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))).
% 58.79/7.77  
% 58.79/7.77  cnf(u243,negated_conjecture,
% 58.79/7.77      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))).
% 58.79/7.77  
% 58.79/7.77  cnf(u647,negated_conjecture,
% 58.79/7.77      k2_struct_0(sK0) = k5_xboole_0(k2_struct_0(sK0),k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u487,negated_conjecture,
% 58.79/7.77      k7_subset_1(sK2,sK2,k2_struct_0(sK0)) = k5_xboole_0(k2_struct_0(sK0),k2_struct_0(sK0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u299,negated_conjecture,
% 58.79/7.77      sK2 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k2_struct_0(sK0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u192,negated_conjecture,
% 58.79/7.77      sK1 = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k2_struct_0(sK0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u241,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK1,sK1))).
% 58.79/7.77  
% 58.79/7.77  cnf(u220,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(u1_struct_0(sK0),k5_xboole_0(sK2,sK2))).
% 58.79/7.77  
% 58.79/7.77  cnf(u129,negated_conjecture,
% 58.79/7.77      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u126,negated_conjecture,
% 58.79/7.77      k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u128,negated_conjecture,
% 58.79/7.77      k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u125,negated_conjecture,
% 58.79/7.77      k3_subset_1(u1_struct_0(sK0),sK2) = k5_xboole_0(u1_struct_0(sK0),sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u2433,axiom,
% 58.79/7.77      k4_subset_1(X3,X3,X3) = k5_xboole_0(k4_subset_1(X3,X3,X3),k7_subset_1(X3,X3,k4_subset_1(X3,X3,X3)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u366,axiom,
% 58.79/7.77      k7_subset_1(X3,X3,k4_subset_1(X3,X3,X3)) = k5_xboole_0(k4_subset_1(X3,X3,X3),k4_subset_1(X3,X3,X3))).
% 58.79/7.77  
% 58.79/7.77  cnf(u279,axiom,
% 58.79/7.77      k5_xboole_0(X0,X0) = k5_xboole_0(k4_subset_1(X0,X0,X0),k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k4_subset_1(X0,X0,X0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2694,axiom,
% 58.79/7.77      k5_xboole_0(X8,k7_subset_1(X9,X9,X8)) = k5_xboole_0(k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9)),k7_subset_1(X9,X9,k3_tarski(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2656,axiom,
% 58.79/7.77      k5_xboole_0(X7,k7_subset_1(X6,X6,X7)) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k7_subset_1(X7,X7,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2819,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u867,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18)) = k5_xboole_0(k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18)),k7_subset_1(X17,X17,k3_tarski(k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X18))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u9348,axiom,
% 58.79/7.77      k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u8780,axiom,
% 58.79/7.77      k7_subset_1(X2,X2,k5_xboole_0(X3,k7_subset_1(X2,X2,X3))) = k5_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u10936,axiom,
% 58.79/7.77      k7_subset_1(X21,X21,k3_tarski(k6_enumset1(X22,X22,X22,X22,X22,X22,X22,X21))) = k5_xboole_0(k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)),k3_tarski(k6_enumset1(X22,X22,X22,X22,X22,X22,X22,X21)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2078,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2140,axiom,
% 58.79/7.77      k7_subset_1(X15,X15,k5_xboole_0(X15,k7_subset_1(X16,X16,X15))) = k5_xboole_0(k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)),k1_setfam_1(k6_enumset1(k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k5_xboole_0(X15,k7_subset_1(X16,X16,X15)),k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X15,X15,X16)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1830,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u735,axiom,
% 58.79/7.77      k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k5_xboole_0(k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u36157,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k7_subset_1(X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u28126,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)) = k5_xboole_0(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k7_subset_1(X5,X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u17795,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k7_subset_1(X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1500,axiom,
% 58.79/7.77      k5_xboole_0(X8,k7_subset_1(X7,X7,X8)) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8)),k7_subset_1(X7,X7,k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X8))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u797,axiom,
% 58.79/7.77      k5_xboole_0(X13,k7_subset_1(X14,X14,X13)) = k5_xboole_0(k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X13)),k7_subset_1(X13,X13,k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X13))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u734,axiom,
% 58.79/7.77      k7_subset_1(X4,X4,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4))) = k5_xboole_0(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X4)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u9349,axiom,
% 58.79/7.77      k7_subset_1(X3,X3,k5_xboole_0(X3,k7_subset_1(X2,X2,X3))) = k5_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u8779,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u10816,axiom,
% 58.79/7.77      k7_subset_1(X44,X44,k3_tarski(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45))) = k5_xboole_0(k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X45,X45,X45,X45,X45,X45,X45,X44)),k3_tarski(k6_enumset1(X44,X44,X44,X44,X44,X44,X44,X45)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2125,axiom,
% 58.79/7.77      k7_subset_1(X6,X6,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u9265,axiom,
% 58.79/7.77      k7_subset_1(X37,X37,k5_xboole_0(X37,k7_subset_1(X36,X36,X37))) = k5_xboole_0(k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)),k1_setfam_1(k6_enumset1(k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k5_xboole_0(X37,k7_subset_1(X36,X36,X37)),k3_tarski(k6_enumset1(X36,X36,X36,X36,X36,X36,X36,X37)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1581,axiom,
% 58.79/7.77      k7_subset_1(X6,X6,k5_xboole_0(X7,k7_subset_1(X6,X6,X7))) = k5_xboole_0(k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)),k1_setfam_1(k6_enumset1(k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k3_tarski(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X6)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u121,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,X1) = k5_xboole_0(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u16646,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X13,X13,X13,X13,X13,X13,X13,X14)) = k5_xboole_0(k5_xboole_0(X14,k7_subset_1(X13,X13,X14)),k7_subset_1(X13,X13,k5_xboole_0(X14,k7_subset_1(X13,X13,X14))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u19933,axiom,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(X52,k7_subset_1(X53,X53,X52)),k7_subset_1(X52,X52,k5_xboole_0(X52,k7_subset_1(X53,X53,X52)))) = k3_tarski(k6_enumset1(X52,X52,X52,X52,X52,X52,X52,k3_tarski(k6_enumset1(X52,X52,X52,X52,X52,X52,X52,X53))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u17527,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k7_subset_1(X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u30478,axiom,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k7_subset_1(X9,X9,k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))) = k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,k3_tarski(k6_enumset1(X10,X10,X10,X10,X10,X10,X10,X9))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u16218,axiom,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(X11,k7_subset_1(X12,X12,X11)),k7_subset_1(X11,X11,k5_xboole_0(X11,k7_subset_1(X12,X12,X11)))) = k3_tarski(k6_enumset1(X12,X12,X12,X12,X12,X12,X12,X11))).
% 58.79/7.77  
% 58.79/7.77  cnf(u13493,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)) = k5_xboole_0(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k7_subset_1(X10,X10,k5_xboole_0(X9,k7_subset_1(X10,X10,X9))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u4183,axiom,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(X9,k7_subset_1(X10,X10,X9)),k7_subset_1(X9,X9,k5_xboole_0(X9,k7_subset_1(X10,X10,X9)))) = k5_xboole_0(X10,k7_subset_1(X9,X9,X10))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1064,axiom,
% 58.79/7.77      k5_xboole_0(X6,k7_subset_1(X7,X7,X6)) = k5_xboole_0(k5_xboole_0(X6,k7_subset_1(X7,X7,X6)),k7_subset_1(X7,X7,k5_xboole_0(X6,k7_subset_1(X7,X7,X6))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u690,axiom,
% 58.79/7.77      k5_xboole_0(X7,k7_subset_1(X8,X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k7_subset_1(X8,X8,X7)),k7_subset_1(X7,X7,k5_xboole_0(X7,k7_subset_1(X8,X8,X7))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u603,axiom,
% 58.79/7.77      k5_xboole_0(X6,k7_subset_1(X7,X7,X6)) = k5_xboole_0(k5_xboole_0(X7,k7_subset_1(X6,X6,X7)),k7_subset_1(X6,X6,k5_xboole_0(X7,k7_subset_1(X6,X6,X7))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u652,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k7_subset_1(sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u641,negated_conjecture,
% 58.79/7.77      k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k7_subset_1(sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u732,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k5_xboole_0(X1,k7_subset_1(X0,X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u437,axiom,
% 58.79/7.77      k7_subset_1(X5,X5,k5_xboole_0(X5,k7_subset_1(X6,X6,X5))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X6,X6,X5)),k5_xboole_0(X5,k7_subset_1(X6,X6,X5)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u9580,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1880,axiom,
% 58.79/7.77      k7_subset_1(X1,X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1711,axiom,
% 58.79/7.77      k7_subset_1(X3,X3,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) = k5_xboole_0(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k1_setfam_1(k6_enumset1(k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k5_xboole_0(X3,k7_subset_1(X4,X4,X3)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1645,axiom,
% 58.79/7.77      k7_subset_1(X16,X16,k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17))) = k5_xboole_0(k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k1_setfam_1(k6_enumset1(k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k5_xboole_0(X17,k7_subset_1(X16,X16,X17)),k3_tarski(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u246,negated_conjecture,
% 58.79/7.77      k5_xboole_0(u1_struct_0(sK0),sK1) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)),k1_setfam_1(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u225,negated_conjecture,
% 58.79/7.77      k5_xboole_0(u1_struct_0(sK0),sK2) = k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)),k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k5_xboole_0(sK2,k5_xboole_0(u1_struct_0(sK0),sK2)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1631,axiom,
% 58.79/7.77      k5_xboole_0(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k1_setfam_1(k6_enumset1(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X10,k7_subset_1(X11,X11,X10))))) = k7_subset_1(X10,X10,k5_xboole_0(X10,k7_subset_1(X11,X11,X10)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u2123,axiom,
% 58.79/7.77      k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) = k5_xboole_0(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1876,axiom,
% 58.79/7.77      k7_subset_1(X2,X2,k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2))) = k5_xboole_0(k5_xboole_0(X3,k7_subset_1(X2,X2,X3)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k3_tarski(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X2)),k5_xboole_0(X3,k7_subset_1(X2,X2,X3)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u474,axiom,
% 58.79/7.77      k7_subset_1(X5,X5,k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X6,X6,X5)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)),k5_xboole_0(X5,k7_subset_1(X6,X6,X5)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u455,axiom,
% 58.79/7.77      k7_subset_1(X5,X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k1_setfam_1(k6_enumset1(k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1744,axiom,
% 58.79/7.77      k7_subset_1(X11,X11,k5_xboole_0(X11,k7_subset_1(X10,X10,X11))) = k5_xboole_0(k5_xboole_0(X10,k7_subset_1(X11,X11,X10)),k1_setfam_1(k6_enumset1(k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X11,k7_subset_1(X10,X10,X11)),k5_xboole_0(X10,k7_subset_1(X11,X11,X10)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u1583,axiom,
% 58.79/7.77      k7_subset_1(X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u393,axiom,
% 58.79/7.77      k7_subset_1(X5,X5,k5_xboole_0(X4,k7_subset_1(X5,X5,X4))) = k5_xboole_0(k5_xboole_0(X5,k7_subset_1(X4,X4,X5)),k1_setfam_1(k6_enumset1(k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X4,k7_subset_1(X5,X5,X4)),k5_xboole_0(X5,k7_subset_1(X4,X4,X5)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u144,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X1,k7_subset_1(X0,X0,X1)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,k7_subset_1(X0,X0,X1)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u123,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,X1) = k5_xboole_0(k5_xboole_0(X0,k7_subset_1(X1,X1,X0)),k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 58.79/7.77  
% 58.79/7.77  cnf(u142,axiom,
% 58.79/7.77      k5_xboole_0(X2,k7_subset_1(X3,X3,X2)) = k5_xboole_0(X3,k7_subset_1(X2,X2,X3))).
% 58.79/7.77  
% 58.79/7.77  cnf(u116,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u136,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))).
% 58.79/7.77  
% 58.79/7.77  cnf(u115,axiom,
% 58.79/7.77      k7_subset_1(X0,X0,X0) = k5_xboole_0(X0,X0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u278,axiom,
% 58.79/7.77      k4_subset_1(X0,X0,X0) = k5_xboole_0(X0,k5_xboole_0(X0,X0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u114,axiom,
% 58.79/7.77      k3_subset_1(X0,X0) = k5_xboole_0(X0,X0)).
% 58.79/7.77  
% 58.79/7.77  cnf(u104,axiom,
% 58.79/7.77      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k7_subset_1(X1,X1,X0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u113,axiom,
% 58.79/7.77      k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0).
% 58.79/7.77  
% 58.79/7.77  cnf(u42,axiom,
% 58.79/7.77      k5_xboole_0(X0,k1_xboole_0) = X0).
% 58.79/7.77  
% 58.79/7.77  cnf(u41,axiom,
% 58.79/7.77      k2_subset_1(X0) = X0).
% 58.79/7.77  
% 58.79/7.77  cnf(u176,negated_conjecture,
% 58.79/7.77      k1_xboole_0 != sK2 | r1_xboole_0(u1_struct_0(sK0),sK2)).
% 58.79/7.77  
% 58.79/7.77  cnf(u177,negated_conjecture,
% 58.79/7.77      k1_xboole_0 != sK2 | r1_xboole_0(sK2,u1_struct_0(sK0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u180,negated_conjecture,
% 58.79/7.77      k1_xboole_0 != sK1 | r1_xboole_0(u1_struct_0(sK0),sK1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u181,negated_conjecture,
% 58.79/7.77      k1_xboole_0 != sK1 | r1_xboole_0(sK1,u1_struct_0(sK0))).
% 58.79/7.77  
% 58.79/7.77  cnf(u78,axiom,
% 58.79/7.77      k1_xboole_0 != k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | r1_xboole_0(X0,X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u91,axiom,
% 58.79/7.77      k1_xboole_0 != k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) | r1_xboole_0(X0,X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u194,axiom,
% 58.79/7.77      k1_xboole_0 != X1 | r1_xboole_0(X1,X1)).
% 58.79/7.77  
% 58.79/7.77  cnf(u39,negated_conjecture,
% 58.79/7.77      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 58.79/7.77  
% 58.79/7.77  % (15306)# SZS output end Saturation.
% 58.79/7.77  % (15306)------------------------------
% 58.79/7.77  % (15306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 58.79/7.77  % (15306)Termination reason: Satisfiable
% 58.79/7.77  
% 58.79/7.77  % (15306)Memory used [KB]: 41449
% 58.79/7.77  % (15306)Time elapsed: 6.338 s
% 58.79/7.77  % (15306)------------------------------
% 58.79/7.77  % (15306)------------------------------
% 58.79/7.78  % (15060)Success in time 7.413 s
%------------------------------------------------------------------------------
