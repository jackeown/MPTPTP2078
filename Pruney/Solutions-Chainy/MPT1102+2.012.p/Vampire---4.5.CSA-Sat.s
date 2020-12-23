%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:30 EST 2020

% Result     : CounterSatisfiable 1.61s
% Output     : Saturation 1.61s
% Verified   : 
% Statistics : Number of clauses        :  119 ( 119 expanded)
%              Number of leaves         :  119 ( 119 expanded)
%              Depth                    :    0
%              Number of atoms          :  138 ( 138 expanded)
%              Number of equality atoms :  111 ( 111 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u30,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u37,axiom,
    ( m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) )).

cnf(u78,axiom,
    ( m1_subset_1(k3_subset_1(X2,k6_subset_1(X2,X3)),k1_zfmisc_1(X2)) )).

cnf(u79,negated_conjecture,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u68,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u55,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u203,negated_conjecture,
    ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X23,sK1) = k2_xboole_0(X23,sK1) )).

cnf(u193,negated_conjecture,
    ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X4,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X4,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u340,negated_conjecture,
    ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X26,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X26),sK1) )).

cnf(u329,negated_conjecture,
    ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X4,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X4),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u339,axiom,
    ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
    | k3_subset_1(X23,k7_subset_1(X23,X24,k6_subset_1(X23,X25))) = k4_subset_1(X23,k3_subset_1(X23,X24),k6_subset_1(X23,X25)) )).

cnf(u338,axiom,
    ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
    | k3_subset_1(X20,k7_subset_1(X20,X21,k3_subset_1(X20,k6_subset_1(X20,X22)))) = k4_subset_1(X20,k3_subset_1(X20,X21),k3_subset_1(X20,k6_subset_1(X20,X22))) )).

cnf(u328,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | k3_subset_1(X2,k7_subset_1(X2,X3,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X3),k1_xboole_0) )).

cnf(u327,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k7_subset_1(X0,X1,X0)) = k4_subset_1(X0,k3_subset_1(X0,X1),X0) )).

cnf(u204,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | k4_subset_1(X2,X3,k1_xboole_0) = X3 )).

cnf(u202,axiom,
    ( ~ m1_subset_1(X21,k1_zfmisc_1(X20))
    | k4_subset_1(X20,X21,k6_subset_1(X20,X22)) = k2_xboole_0(X21,k6_subset_1(X20,X22)) )).

cnf(u201,axiom,
    ( ~ m1_subset_1(X18,k1_zfmisc_1(X17))
    | k4_subset_1(X17,X18,k3_subset_1(X17,k6_subset_1(X17,X19))) = k2_xboole_0(X18,k3_subset_1(X17,k6_subset_1(X17,X19))) )).

cnf(u191,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) )).

cnf(u48,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u46,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) )).

cnf(u176,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,k1_xboole_0,X3) )).

cnf(u173,axiom,
    ( k7_subset_1(X17,k3_subset_1(X17,k6_subset_1(X17,X18)),X19) = k6_subset_1(k3_subset_1(X17,k6_subset_1(X17,X18)),X19) )).

cnf(u174,axiom,
    ( k7_subset_1(X20,k6_subset_1(X20,X21),X22) = k6_subset_1(k6_subset_1(X20,X21),X22) )).

cnf(u163,axiom,
    ( k6_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u165,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X4) = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),X4) )).

cnf(u175,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X23) = k6_subset_1(sK1,X23) )).

cnf(u549,axiom,
    ( k4_subset_1(X19,k3_subset_1(X19,k6_subset_1(X19,X20)),k6_subset_1(X19,X21)) = k2_xboole_0(k3_subset_1(X19,k6_subset_1(X19,X20)),k6_subset_1(X19,X21)) )).

cnf(u550,axiom,
    ( k4_subset_1(X22,k6_subset_1(X22,X23),k6_subset_1(X22,X24)) = k2_xboole_0(k6_subset_1(X22,X23),k6_subset_1(X22,X24)) )).

cnf(u552,axiom,
    ( k6_subset_1(X2,X3) = k4_subset_1(X2,k1_xboole_0,k6_subset_1(X2,X3)) )).

cnf(u1817,axiom,
    ( k4_subset_1(X5,k3_subset_1(X5,k6_subset_1(X5,X6)),k3_subset_1(X5,k6_subset_1(X5,X7))) = k2_xboole_0(k3_subset_1(X5,k6_subset_1(X5,X6)),k3_subset_1(X5,k6_subset_1(X5,X7))) )).

cnf(u1437,axiom,
    ( k4_subset_1(X13,k6_subset_1(X13,X15),k3_subset_1(X13,k6_subset_1(X13,X14))) = k2_xboole_0(k6_subset_1(X13,X15),k3_subset_1(X13,k6_subset_1(X13,X14))) )).

cnf(u571,axiom,
    ( k3_subset_1(X7,k6_subset_1(X7,X8)) = k4_subset_1(X7,k1_xboole_0,k3_subset_1(X7,k6_subset_1(X7,X8))) )).

cnf(u252,axiom,
    ( k6_subset_1(X9,X10) = k4_subset_1(X9,k6_subset_1(X9,X10),k1_xboole_0) )).

cnf(u251,axiom,
    ( k3_subset_1(X7,k6_subset_1(X7,X8)) = k4_subset_1(X7,k3_subset_1(X7,k6_subset_1(X7,X8)),k1_xboole_0) )).

cnf(u242,axiom,
    ( k1_xboole_0 = k4_subset_1(X1,k1_xboole_0,k1_xboole_0) )).

cnf(u769,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u768,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u228,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X1)),sK1) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X1))) )).

cnf(u229,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2),sK1) = k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X2)) )).

cnf(u956,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u219,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) )).

cnf(u987,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u861,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u542,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X4)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X4)) )).

cnf(u551,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k6_subset_1(u1_struct_0(sK0),X25)) = k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X25)) )).

cnf(u986,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u773,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u380,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2)),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2))) )).

cnf(u381,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X3)) )).

cnf(u954,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u371,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u607,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2))) )).

cnf(u560,negated_conjecture,
    ( k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2))) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2))) )).

cnf(u243,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0) )).

cnf(u253,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) )).

cnf(u822,negated_conjecture,
    ( sK1 = k6_subset_1(sK1,k1_xboole_0) )).

cnf(u443,negated_conjecture,
    ( sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u1238,axiom,
    ( k6_subset_1(X10,X11) = k6_subset_1(X10,k3_subset_1(X10,k6_subset_1(X10,X11))) )).

cnf(u115,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1) )).

cnf(u114,axiom,
    ( k3_subset_1(X12,k6_subset_1(X12,X13)) = k6_subset_1(X12,k6_subset_1(X12,X13)) )).

cnf(u771,negated_conjecture,
    ( k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0)) )).

cnf(u1005,axiom,
    ( k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X1),X0) )).

cnf(u1019,axiom,
    ( k1_xboole_0 = k6_subset_1(k3_subset_1(X8,k6_subset_1(X8,X9)),X8) )).

cnf(u774,negated_conjecture,
    ( k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u67,axiom,
    ( k1_xboole_0 = k6_subset_1(k1_xboole_0,X5) )).

cnf(u64,axiom,
    ( k1_xboole_0 = k6_subset_1(X0,X0) )).

cnf(u65,axiom,
    ( k1_xboole_0 = k6_subset_1(X1,k2_xboole_0(X2,X1)) )).

cnf(u51,axiom,
    ( k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1)) )).

cnf(u955,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),sK1)) )).

cnf(u431,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u975,axiom,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,k3_subset_1(X0,k6_subset_1(X0,X1))) )).

cnf(u1352,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1))) )).

cnf(u116,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u2275,axiom,
    ( k2_xboole_0(k6_subset_1(X5,X6),k3_subset_1(X5,k6_subset_1(X5,X7))) = k3_subset_1(X5,k6_subset_1(k3_subset_1(X5,k6_subset_1(X5,X6)),k3_subset_1(X5,k6_subset_1(X5,X7)))) )).

cnf(u1983,axiom,
    ( k2_xboole_0(k6_subset_1(X13,X14),k6_subset_1(X13,X15)) = k3_subset_1(X13,k6_subset_1(k3_subset_1(X13,k6_subset_1(X13,X14)),k6_subset_1(X13,X15))) )).

cnf(u1944,axiom,
    ( k3_subset_1(X17,k6_subset_1(k6_subset_1(X17,X18),k6_subset_1(X17,X19))) = k2_xboole_0(k3_subset_1(X17,k6_subset_1(X17,X18)),k6_subset_1(X17,X19)) )).

cnf(u1667,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X1))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k6_subset_1(u1_struct_0(sK0),X1),k3_subset_1(u1_struct_0(sK0),sK1))) )).

cnf(u1665,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X0)),k3_subset_1(u1_struct_0(sK0),sK1))) )).

cnf(u985,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X20)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(sK1,k6_subset_1(u1_struct_0(sK0),X20))) )).

cnf(u1537,negated_conjecture,
    ( k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X2)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2)),sK1)) )).

cnf(u982,negated_conjecture,
    ( k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X4)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X4))) )).

cnf(u1331,negated_conjecture,
    ( k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3)))) )).

cnf(u438,negated_conjecture,
    ( k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k6_subset_1(u1_struct_0(sK0),X3),sK1)) )).

cnf(u90,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u52,axiom,
    ( k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) )).

cnf(u1964,axiom,
    ( k2_xboole_0(k3_subset_1(X13,k6_subset_1(X13,X15)),k3_subset_1(X13,k6_subset_1(X13,X14))) = k3_subset_1(X13,k6_subset_1(k6_subset_1(X13,X15),k3_subset_1(X13,k6_subset_1(X13,X14)))) )).

cnf(u1351,negated_conjecture,
    ( k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3)))) )).

cnf(u1001,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u962,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u1359,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u776,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) )).

cnf(u772,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u770,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u40,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u50,axiom,
    ( k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 )).

cnf(u991,axiom,
    ( k4_subset_1(X9,k6_subset_1(X9,X10),X9) = X9 )).

cnf(u1078,axiom,
    ( k4_subset_1(X8,k3_subset_1(X8,k6_subset_1(X8,X9)),X8) = X8 )).

cnf(u277,axiom,
    ( k4_subset_1(X1,k1_xboole_0,X1) = X1 )).

cnf(u990,axiom,
    ( k4_subset_1(X0,X0,k6_subset_1(X0,X1)) = X0 )).

cnf(u1063,axiom,
    ( k4_subset_1(X8,X8,k3_subset_1(X8,k6_subset_1(X8,X9))) = X8 )).

cnf(u241,axiom,
    ( k4_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u953,axiom,
    ( k4_subset_1(X0,X0,X0) = X0 )).

cnf(u755,axiom,
    ( k6_subset_1(X1,k1_xboole_0) = X1 )).

cnf(u742,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u33,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u2029,axiom,
    ( k2_xboole_0(k6_subset_1(X2,X3),k3_subset_1(X2,k6_subset_1(X2,X3))) = X2 )).

cnf(u1912,axiom,
    ( k2_xboole_0(k6_subset_1(X8,X9),X8) = X8 )).

cnf(u2014,axiom,
    ( k2_xboole_0(k3_subset_1(X0,k6_subset_1(X0,X1)),k6_subset_1(X0,X1)) = X0 )).

cnf(u1876,axiom,
    ( k2_xboole_0(k3_subset_1(X8,k6_subset_1(X8,X9)),X8) = X8 )).

cnf(u56,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u979,axiom,
    ( k2_xboole_0(X2,k6_subset_1(X2,X3)) = X2 )).

cnf(u997,axiom,
    ( k2_xboole_0(X8,k3_subset_1(X8,k6_subset_1(X8,X9))) = X8 )).

cnf(u34,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u952,axiom,
    ( k2_xboole_0(X1,X1) = X1 )).

cnf(u32,negated_conjecture,
    ( sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:41:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.47  % (19310)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (19307)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (19312)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (19315)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (19309)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (19314)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (19322)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (19311)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (19320)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (19313)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (19308)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (19317)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (19321)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (19318)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (19316)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (19324)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (19323)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (19319)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.61/0.58  % SZS status CounterSatisfiable for theBenchmark
% 1.61/0.58  % (19319)# SZS output start Saturation.
% 1.61/0.58  cnf(u30,negated_conjecture,
% 1.61/0.58      l1_struct_0(sK0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u31,negated_conjecture,
% 1.61/0.58      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u37,axiom,
% 1.61/0.58      m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u78,axiom,
% 1.61/0.58      m1_subset_1(k3_subset_1(X2,k6_subset_1(X2,X3)),k1_zfmisc_1(X2))).
% 1.61/0.58  
% 1.61/0.58  cnf(u79,negated_conjecture,
% 1.61/0.58      m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u68,axiom,
% 1.61/0.58      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u55,axiom,
% 1.61/0.58      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u203,negated_conjecture,
% 1.61/0.58      ~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X23,sK1) = k2_xboole_0(X23,sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u193,negated_conjecture,
% 1.61/0.58      ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X4,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(X4,k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u340,negated_conjecture,
% 1.61/0.58      ~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X26,sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X26),sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u329,negated_conjecture,
% 1.61/0.58      ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X4,k3_subset_1(u1_struct_0(sK0),sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X4),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u339,axiom,
% 1.61/0.58      ~m1_subset_1(X24,k1_zfmisc_1(X23)) | k3_subset_1(X23,k7_subset_1(X23,X24,k6_subset_1(X23,X25))) = k4_subset_1(X23,k3_subset_1(X23,X24),k6_subset_1(X23,X25))).
% 1.61/0.58  
% 1.61/0.58  cnf(u338,axiom,
% 1.61/0.58      ~m1_subset_1(X21,k1_zfmisc_1(X20)) | k3_subset_1(X20,k7_subset_1(X20,X21,k3_subset_1(X20,k6_subset_1(X20,X22)))) = k4_subset_1(X20,k3_subset_1(X20,X21),k3_subset_1(X20,k6_subset_1(X20,X22)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u328,axiom,
% 1.61/0.58      ~m1_subset_1(X3,k1_zfmisc_1(X2)) | k3_subset_1(X2,k7_subset_1(X2,X3,k1_xboole_0)) = k4_subset_1(X2,k3_subset_1(X2,X3),k1_xboole_0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u327,axiom,
% 1.61/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X0)) = k4_subset_1(X0,k3_subset_1(X0,X1),X0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u204,axiom,
% 1.61/0.58      ~m1_subset_1(X3,k1_zfmisc_1(X2)) | k4_subset_1(X2,X3,k1_xboole_0) = X3).
% 1.61/0.58  
% 1.61/0.58  cnf(u202,axiom,
% 1.61/0.58      ~m1_subset_1(X21,k1_zfmisc_1(X20)) | k4_subset_1(X20,X21,k6_subset_1(X20,X22)) = k2_xboole_0(X21,k6_subset_1(X20,X22))).
% 1.61/0.58  
% 1.61/0.58  cnf(u201,axiom,
% 1.61/0.58      ~m1_subset_1(X18,k1_zfmisc_1(X17)) | k4_subset_1(X17,X18,k3_subset_1(X17,k6_subset_1(X17,X19))) = k2_xboole_0(X18,k3_subset_1(X17,k6_subset_1(X17,X19)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u191,axiom,
% 1.61/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u54,axiom,
% 1.61/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)).
% 1.61/0.58  
% 1.61/0.58  cnf(u53,axiom,
% 1.61/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u48,axiom,
% 1.61/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u46,axiom,
% 1.61/0.58      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u44,axiom,
% 1.61/0.58      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u176,axiom,
% 1.61/0.58      k1_xboole_0 = k7_subset_1(X2,k1_xboole_0,X3)).
% 1.61/0.58  
% 1.61/0.58  cnf(u173,axiom,
% 1.61/0.58      k7_subset_1(X17,k3_subset_1(X17,k6_subset_1(X17,X18)),X19) = k6_subset_1(k3_subset_1(X17,k6_subset_1(X17,X18)),X19)).
% 1.61/0.58  
% 1.61/0.58  cnf(u174,axiom,
% 1.61/0.58      k7_subset_1(X20,k6_subset_1(X20,X21),X22) = k6_subset_1(k6_subset_1(X20,X21),X22)).
% 1.61/0.58  
% 1.61/0.58  cnf(u163,axiom,
% 1.61/0.58      k6_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u165,negated_conjecture,
% 1.61/0.58      k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X4) = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),X4)).
% 1.61/0.58  
% 1.61/0.58  cnf(u175,negated_conjecture,
% 1.61/0.58      k7_subset_1(u1_struct_0(sK0),sK1,X23) = k6_subset_1(sK1,X23)).
% 1.61/0.58  
% 1.61/0.58  cnf(u549,axiom,
% 1.61/0.58      k4_subset_1(X19,k3_subset_1(X19,k6_subset_1(X19,X20)),k6_subset_1(X19,X21)) = k2_xboole_0(k3_subset_1(X19,k6_subset_1(X19,X20)),k6_subset_1(X19,X21))).
% 1.61/0.58  
% 1.61/0.58  cnf(u550,axiom,
% 1.61/0.58      k4_subset_1(X22,k6_subset_1(X22,X23),k6_subset_1(X22,X24)) = k2_xboole_0(k6_subset_1(X22,X23),k6_subset_1(X22,X24))).
% 1.61/0.58  
% 1.61/0.58  cnf(u552,axiom,
% 1.61/0.58      k6_subset_1(X2,X3) = k4_subset_1(X2,k1_xboole_0,k6_subset_1(X2,X3))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1817,axiom,
% 1.61/0.58      k4_subset_1(X5,k3_subset_1(X5,k6_subset_1(X5,X6)),k3_subset_1(X5,k6_subset_1(X5,X7))) = k2_xboole_0(k3_subset_1(X5,k6_subset_1(X5,X6)),k3_subset_1(X5,k6_subset_1(X5,X7)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1437,axiom,
% 1.61/0.58      k4_subset_1(X13,k6_subset_1(X13,X15),k3_subset_1(X13,k6_subset_1(X13,X14))) = k2_xboole_0(k6_subset_1(X13,X15),k3_subset_1(X13,k6_subset_1(X13,X14)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u571,axiom,
% 1.61/0.58      k3_subset_1(X7,k6_subset_1(X7,X8)) = k4_subset_1(X7,k1_xboole_0,k3_subset_1(X7,k6_subset_1(X7,X8)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u252,axiom,
% 1.61/0.58      k6_subset_1(X9,X10) = k4_subset_1(X9,k6_subset_1(X9,X10),k1_xboole_0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u251,axiom,
% 1.61/0.58      k3_subset_1(X7,k6_subset_1(X7,X8)) = k4_subset_1(X7,k3_subset_1(X7,k6_subset_1(X7,X8)),k1_xboole_0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u242,axiom,
% 1.61/0.58      k1_xboole_0 = k4_subset_1(X1,k1_xboole_0,k1_xboole_0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u769,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u768,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u228,negated_conjecture,
% 1.61/0.58      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X1)),sK1) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X1)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u229,negated_conjecture,
% 1.61/0.58      k4_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2),sK1) = k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X2))).
% 1.61/0.58  
% 1.61/0.58  cnf(u956,negated_conjecture,
% 1.61/0.58      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u219,negated_conjecture,
% 1.61/0.58      sK1 = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u987,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u861,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u542,negated_conjecture,
% 1.61/0.58      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X4)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X4))).
% 1.61/0.58  
% 1.61/0.58  cnf(u551,negated_conjecture,
% 1.61/0.58      k4_subset_1(u1_struct_0(sK0),sK1,k6_subset_1(u1_struct_0(sK0),X25)) = k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X25))).
% 1.61/0.58  
% 1.61/0.58  cnf(u986,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u773,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u380,negated_conjecture,
% 1.61/0.58      k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2)),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u381,negated_conjecture,
% 1.61/0.58      k4_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X3))).
% 1.61/0.58  
% 1.61/0.58  cnf(u954,negated_conjecture,
% 1.61/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u371,negated_conjecture,
% 1.61/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u607,negated_conjecture,
% 1.61/0.58      k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u560,negated_conjecture,
% 1.61/0.58      k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2))) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u243,negated_conjecture,
% 1.61/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k1_xboole_0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u253,negated_conjecture,
% 1.61/0.58      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u822,negated_conjecture,
% 1.61/0.58      sK1 = k6_subset_1(sK1,k1_xboole_0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u443,negated_conjecture,
% 1.61/0.58      sK1 = k6_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1238,axiom,
% 1.61/0.58      k6_subset_1(X10,X11) = k6_subset_1(X10,k3_subset_1(X10,k6_subset_1(X10,X11)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u115,negated_conjecture,
% 1.61/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k6_subset_1(u1_struct_0(sK0),sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u114,axiom,
% 1.61/0.58      k3_subset_1(X12,k6_subset_1(X12,X13)) = k6_subset_1(X12,k6_subset_1(X12,X13))).
% 1.61/0.58  
% 1.61/0.58  cnf(u771,negated_conjecture,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(sK1,u1_struct_0(sK0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1005,axiom,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(k6_subset_1(X0,X1),X0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u1019,axiom,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(k3_subset_1(X8,k6_subset_1(X8,X9)),X8)).
% 1.61/0.58  
% 1.61/0.58  cnf(u774,negated_conjecture,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u67,axiom,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(k1_xboole_0,X5)).
% 1.61/0.58  
% 1.61/0.58  cnf(u64,axiom,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(X0,X0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u65,axiom,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(X1,k2_xboole_0(X2,X1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u51,axiom,
% 1.61/0.58      k1_xboole_0 = k6_subset_1(X0,k2_xboole_0(X0,X1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u955,negated_conjecture,
% 1.61/0.58      sK1 = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u431,negated_conjecture,
% 1.61/0.58      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u975,axiom,
% 1.61/0.58      k6_subset_1(X0,X1) = k3_subset_1(X0,k3_subset_1(X0,k6_subset_1(X0,X1)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1352,negated_conjecture,
% 1.61/0.58      k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),sK1)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u116,axiom,
% 1.61/0.58      k1_xboole_0 = k3_subset_1(X0,X0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u2275,axiom,
% 1.61/0.58      k2_xboole_0(k6_subset_1(X5,X6),k3_subset_1(X5,k6_subset_1(X5,X7))) = k3_subset_1(X5,k6_subset_1(k3_subset_1(X5,k6_subset_1(X5,X6)),k3_subset_1(X5,k6_subset_1(X5,X7))))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1983,axiom,
% 1.61/0.58      k2_xboole_0(k6_subset_1(X13,X14),k6_subset_1(X13,X15)) = k3_subset_1(X13,k6_subset_1(k3_subset_1(X13,k6_subset_1(X13,X14)),k6_subset_1(X13,X15)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1944,axiom,
% 1.61/0.58      k3_subset_1(X17,k6_subset_1(k6_subset_1(X17,X18),k6_subset_1(X17,X19))) = k2_xboole_0(k3_subset_1(X17,k6_subset_1(X17,X18)),k6_subset_1(X17,X19))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1667,negated_conjecture,
% 1.61/0.58      k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X1))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k6_subset_1(u1_struct_0(sK0),X1),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1665,negated_conjecture,
% 1.61/0.58      k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X0)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X0)),k3_subset_1(u1_struct_0(sK0),sK1)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u985,negated_conjecture,
% 1.61/0.58      k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X20)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(sK1,k6_subset_1(u1_struct_0(sK0),X20)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1537,negated_conjecture,
% 1.61/0.58      k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X2)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X2)),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u982,negated_conjecture,
% 1.61/0.58      k2_xboole_0(sK1,k6_subset_1(u1_struct_0(sK0),X4)) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k6_subset_1(u1_struct_0(sK0),X4)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1331,negated_conjecture,
% 1.61/0.58      k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))))).
% 1.61/0.58  
% 1.61/0.58  cnf(u438,negated_conjecture,
% 1.61/0.58      k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(k6_subset_1(u1_struct_0(sK0),X3),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u90,axiom,
% 1.61/0.58      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u52,axiom,
% 1.61/0.58      k6_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1964,axiom,
% 1.61/0.58      k2_xboole_0(k3_subset_1(X13,k6_subset_1(X13,X15)),k3_subset_1(X13,k6_subset_1(X13,X14))) = k3_subset_1(X13,k6_subset_1(k6_subset_1(X13,X15),k3_subset_1(X13,k6_subset_1(X13,X14))))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1351,negated_conjecture,
% 1.61/0.58      k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))) = k3_subset_1(u1_struct_0(sK0),k6_subset_1(sK1,k3_subset_1(u1_struct_0(sK0),k6_subset_1(u1_struct_0(sK0),X3))))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1001,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u962,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k2_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u1359,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u776,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1)).
% 1.61/0.58  
% 1.61/0.58  cnf(u772,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k2_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  cnf(u770,negated_conjecture,
% 1.61/0.58      u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 1.61/0.58  
% 1.61/0.58  cnf(u40,axiom,
% 1.61/0.58      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 1.61/0.58  
% 1.61/0.58  cnf(u50,axiom,
% 1.61/0.58      k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u991,axiom,
% 1.61/0.58      k4_subset_1(X9,k6_subset_1(X9,X10),X9) = X9).
% 1.61/0.58  
% 1.61/0.58  cnf(u1078,axiom,
% 1.61/0.58      k4_subset_1(X8,k3_subset_1(X8,k6_subset_1(X8,X9)),X8) = X8).
% 1.61/0.58  
% 1.61/0.58  cnf(u277,axiom,
% 1.61/0.58      k4_subset_1(X1,k1_xboole_0,X1) = X1).
% 1.61/0.58  
% 1.61/0.58  cnf(u990,axiom,
% 1.61/0.58      k4_subset_1(X0,X0,k6_subset_1(X0,X1)) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u1063,axiom,
% 1.61/0.58      k4_subset_1(X8,X8,k3_subset_1(X8,k6_subset_1(X8,X9))) = X8).
% 1.61/0.58  
% 1.61/0.58  cnf(u241,axiom,
% 1.61/0.58      k4_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u953,axiom,
% 1.61/0.58      k4_subset_1(X0,X0,X0) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u755,axiom,
% 1.61/0.58      k6_subset_1(X1,k1_xboole_0) = X1).
% 1.61/0.58  
% 1.61/0.58  cnf(u742,axiom,
% 1.61/0.58      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u33,axiom,
% 1.61/0.58      k2_subset_1(X0) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u2029,axiom,
% 1.61/0.58      k2_xboole_0(k6_subset_1(X2,X3),k3_subset_1(X2,k6_subset_1(X2,X3))) = X2).
% 1.61/0.58  
% 1.61/0.58  cnf(u1912,axiom,
% 1.61/0.58      k2_xboole_0(k6_subset_1(X8,X9),X8) = X8).
% 1.61/0.58  
% 1.61/0.58  cnf(u2014,axiom,
% 1.61/0.58      k2_xboole_0(k3_subset_1(X0,k6_subset_1(X0,X1)),k6_subset_1(X0,X1)) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u1876,axiom,
% 1.61/0.58      k2_xboole_0(k3_subset_1(X8,k6_subset_1(X8,X9)),X8) = X8).
% 1.61/0.58  
% 1.61/0.58  cnf(u56,axiom,
% 1.61/0.58      k2_xboole_0(k1_xboole_0,X0) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u979,axiom,
% 1.61/0.58      k2_xboole_0(X2,k6_subset_1(X2,X3)) = X2).
% 1.61/0.58  
% 1.61/0.58  cnf(u997,axiom,
% 1.61/0.58      k2_xboole_0(X8,k3_subset_1(X8,k6_subset_1(X8,X9))) = X8).
% 1.61/0.58  
% 1.61/0.58  cnf(u34,axiom,
% 1.61/0.58      k2_xboole_0(X0,k1_xboole_0) = X0).
% 1.61/0.58  
% 1.61/0.58  cnf(u952,axiom,
% 1.61/0.58      k2_xboole_0(X1,X1) = X1).
% 1.61/0.58  
% 1.61/0.58  cnf(u32,negated_conjecture,
% 1.61/0.58      sK1 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 1.61/0.58  
% 1.61/0.58  % (19319)# SZS output end Saturation.
% 1.61/0.58  % (19319)------------------------------
% 1.61/0.58  % (19319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (19319)Termination reason: Satisfiable
% 1.61/0.58  
% 1.61/0.58  % (19319)Memory used [KB]: 2686
% 1.61/0.58  % (19319)Time elapsed: 0.149 s
% 1.61/0.58  % (19319)------------------------------
% 1.61/0.58  % (19319)------------------------------
% 1.61/0.58  % (19306)Success in time 0.212 s
%------------------------------------------------------------------------------
