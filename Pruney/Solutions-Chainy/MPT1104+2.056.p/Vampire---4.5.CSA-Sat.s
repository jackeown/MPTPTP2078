%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:57 EST 2020

% Result     : CounterSatisfiable 3.64s
% Output     : Saturation 3.64s
% Verified   : 
% Statistics : Number of clauses        :  177 ( 177 expanded)
%              Number of leaves         :  177 ( 177 expanded)
%              Depth                    :    0
%              Number of atoms          :  197 ( 197 expanded)
%              Number of equality atoms :  160 ( 160 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u62,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u35,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u106,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1) )).

cnf(u107,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK2) = k2_xboole_0(X1,sK2) )).

cnf(u58,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u59,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u108,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | k2_xboole_0(X3,X2) = k4_subset_1(X2,X3,X2) )).

cnf(u38,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u57,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u424,negated_conjecture,
    ( r1_tarski(sK2,k2_struct_0(sK0)) )).

cnf(u184,negated_conjecture,
    ( r1_tarski(sK1,k2_struct_0(sK0)) )).

cnf(u4524,axiom,
    ( r1_tarski(k3_xboole_0(X15,X16),k3_xboole_0(X16,X15)) )).

cnf(u524,axiom,
    ( r1_tarski(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) )).

cnf(u477,axiom,
    ( r1_tarski(X4,k2_xboole_0(X4,X5)) )).

cnf(u278,axiom,
    ( r1_tarski(X9,k2_xboole_0(X8,X9)) )).

cnf(u186,axiom,
    ( r1_tarski(k4_xboole_0(X8,X9),k2_xboole_0(X9,X8)) )).

cnf(u97,axiom,
    ( r1_tarski(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5)) )).

cnf(u141,axiom,
    ( r1_tarski(k3_xboole_0(X1,X0),X0) )).

cnf(u64,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u43,axiom,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) )).

cnf(u79,axiom,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) )).

cnf(u60,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u431,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(sK0),sK2)
    | k2_struct_0(sK0) = sK2 )).

cnf(u258,negated_conjecture,
    ( ~ r1_tarski(k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u907,axiom,
    ( ~ r1_tarski(k2_xboole_0(X13,X14),X13)
    | k2_xboole_0(X13,X14) = X13 )).

cnf(u338,axiom,
    ( ~ r1_tarski(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12))
    | k2_xboole_0(X12,X13) = k4_xboole_0(X13,X12) )).

cnf(u170,axiom,
    ( ~ r1_tarski(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | k2_xboole_0(X0,X1) = k4_xboole_0(X0,X1) )).

cnf(u339,axiom,
    ( ~ r1_tarski(k2_xboole_0(X14,X15),X15)
    | k2_xboole_0(X14,X15) = X15 )).

cnf(u123,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u102,axiom,
    ( ~ r1_tarski(X1,k4_xboole_0(X1,X2))
    | k4_xboole_0(X1,X2) = X1 )).

cnf(u473,axiom,
    ( ~ r1_tarski(X0,k3_xboole_0(X1,X0))
    | k3_xboole_0(X1,X0) = X0 )).

cnf(u139,axiom,
    ( ~ r1_tarski(X0,k3_xboole_0(X0,X1))
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u53,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u56,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u252,negated_conjecture,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) )).

cnf(u766,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u286,negated_conjecture,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u251,negated_conjecture,
    ( sK2 = k4_xboole_0(sK2,sK1) )).

cnf(u742,negated_conjecture,
    ( sK2 = k3_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u396,negated_conjecture,
    ( sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) )).

cnf(u250,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u806,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u115,negated_conjecture,
    ( sK1 = k5_xboole_0(sK1,k1_xboole_0) )).

cnf(u402,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u76,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,sK2) )).

cnf(u432,negated_conjecture,
    ( sK1 = k3_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u259,negated_conjecture,
    ( sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) )).

cnf(u417,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK1,sK2) )).

cnf(u121,negated_conjecture,
    ( k2_struct_0(sK0) = k5_xboole_0(sK2,sK1) )).

cnf(u436,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u401,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u406,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0)) )).

cnf(u1080,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,sK1) )).

cnf(u433,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0)) )).

cnf(u119,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u120,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u37,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u103,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u343,axiom,
    ( k4_subset_1(X0,X0,X0) = X0 )).

cnf(u122,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u113,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u40,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u4555,axiom,
    ( k1_xboole_0 = k5_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X9,X10)) )).

cnf(u801,axiom,
    ( k1_xboole_0 = k5_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5)) )).

cnf(u92,axiom,
    ( k1_xboole_0 = k5_xboole_0(X4,X4) )).

cnf(u416,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1) )).

cnf(u88,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2) )).

cnf(u124,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) )).

cnf(u153,axiom,
    ( k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) )).

cnf(u395,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)) )).

cnf(u392,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) )).

cnf(u136,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

cnf(u590,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k2_xboole_0(X12,X13)) )).

cnf(u589,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X10,X11)) )).

cnf(u202,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) )).

cnf(u4557,axiom,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20)) )).

cnf(u2825,axiom,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1) )).

cnf(u587,axiom,
    ( k1_xboole_0 = k4_xboole_0(k3_xboole_0(X7,X8),X7) )).

cnf(u255,axiom,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X9,X8)) )).

cnf(u63,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u68,axiom,
    ( k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) )).

cnf(u44,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u1141,axiom,
    ( k5_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)) = X5 )).

cnf(u834,axiom,
    ( k5_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11 )).

cnf(u152,axiom,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u610,axiom,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 )).

cnf(u613,axiom,
    ( k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 )).

cnf(u647,axiom,
    ( k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7 )).

cnf(u836,axiom,
    ( k5_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = X12 )).

cnf(u249,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u104,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

cnf(u231,axiom,
    ( k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7 )).

cnf(u100,axiom,
    ( k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = X3 )).

cnf(u210,axiom,
    ( k5_xboole_0(k2_xboole_0(X4,X5),X4) = k4_xboole_0(X5,X4) )).

cnf(u80,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u105,axiom,
    ( k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3) )).

cnf(u211,axiom,
    ( k5_xboole_0(k2_xboole_0(X7,X6),X6) = k4_xboole_0(X7,X6) )).

cnf(u89,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u51,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u292,axiom,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u201,axiom,
    ( k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) )).

cnf(u93,axiom,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) )).

cnf(u52,axiom,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) )).

cnf(u738,axiom,
    ( k4_xboole_0(X13,X12) = k3_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12)) )).

cnf(u291,axiom,
    ( k4_xboole_0(X6,X7) = k3_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) )).

cnf(u195,axiom,
    ( k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) )).

cnf(u219,axiom,
    ( k4_xboole_0(X2,X1) = k3_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2)) )).

cnf(u171,axiom,
    ( k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3)) )).

cnf(u75,axiom,
    ( k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1) )).

cnf(u909,axiom,
    ( k3_xboole_0(k2_xboole_0(X17,X18),X17) = X17 )).

cnf(u739,axiom,
    ( k3_xboole_0(k2_xboole_0(X14,X15),X15) = X15 )).

cnf(u3416,axiom,
    ( k3_xboole_0(X41,X42) = k5_xboole_0(k3_xboole_0(X42,X41),k1_xboole_0) )).

cnf(u3412,axiom,
    ( k3_xboole_0(X37,X38) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X38,X37)) )).

cnf(u3819,axiom,
    ( k3_xboole_0(X12,X11) = k5_xboole_0(X11,k4_xboole_0(X11,X12)) )).

cnf(u214,axiom,
    ( k5_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) )).

cnf(u6585,axiom,
    ( k3_xboole_0(X4,X3) = k4_xboole_0(k3_xboole_0(X3,X4),k1_xboole_0) )).

cnf(u1143,axiom,
    ( k3_xboole_0(X12,X11) = k4_xboole_0(X11,k4_xboole_0(X11,X12)) )).

cnf(u49,axiom,
    ( k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )).

cnf(u474,axiom,
    ( k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3) )).

cnf(u4541,axiom,
    ( k3_xboole_0(X11,X12) = k3_xboole_0(k3_xboole_0(X12,X11),k3_xboole_0(X11,X12)) )).

cnf(u4528,axiom,
    ( k3_xboole_0(X23,X24) = k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X23)) )).

cnf(u1151,axiom,
    ( k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) )).

cnf(u1139,axiom,
    ( k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X4,X3)) )).

cnf(u309,axiom,
    ( k3_xboole_0(X8,X9) = k3_xboole_0(X8,k3_xboole_0(X8,X9)) )).

cnf(u6298,axiom,
    ( k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X8,X7),X7) )).

cnf(u140,axiom,
    ( k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2) )).

cnf(u45,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u7735,axiom,
    ( k3_xboole_0(X19,X18) = k2_xboole_0(k3_xboole_0(X18,X19),k1_xboole_0) )).

cnf(u7731,axiom,
    ( k3_xboole_0(X9,X8) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X8,X9)) )).

cnf(u4537,axiom,
    ( k3_xboole_0(X42,X41) = k2_xboole_0(k3_xboole_0(X41,X42),k3_xboole_0(X42,X41)) )).

cnf(u4534,axiom,
    ( k3_xboole_0(X36,X35) = k2_xboole_0(k3_xboole_0(X36,X35),k3_xboole_0(X35,X36)) )).

cnf(u71,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u72,axiom,
    ( k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1 )).

cnf(u47,axiom,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 )).

cnf(u341,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u340,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u65,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u1356,axiom,
    ( k2_xboole_0(k4_xboole_0(X24,X25),X24) = X24 )).

cnf(u3028,axiom,
    ( k2_xboole_0(k3_xboole_0(X42,X41),X41) = X41 )).

cnf(u1075,axiom,
    ( k2_xboole_0(k3_xboole_0(X9,X10),X9) = X9 )).

cnf(u48,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) )).

cnf(u1225,axiom,
    ( k2_xboole_0(X16,X17) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X17,X16)) )).

cnf(u660,axiom,
    ( k2_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X13,X12),X12) )).

cnf(u653,axiom,
    ( k2_xboole_0(X10,X11) = k5_xboole_0(k4_xboole_0(X10,X11),X11) )).

cnf(u1093,axiom,
    ( k2_xboole_0(X28,X29) = k5_xboole_0(k2_xboole_0(X29,X28),k1_xboole_0) )).

cnf(u661,axiom,
    ( k2_xboole_0(X14,X15) = k5_xboole_0(X15,k4_xboole_0(X14,X15)) )).

cnf(u50,axiom,
    ( k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) )).

cnf(u280,axiom,
    ( k2_xboole_0(X6,X5) = k4_xboole_0(k2_xboole_0(X5,X6),k1_xboole_0) )).

cnf(u1068,axiom,
    ( k2_xboole_0(X21,X20) = k3_xboole_0(k2_xboole_0(X20,X21),k2_xboole_0(X21,X20)) )).

cnf(u242,axiom,
    ( k2_xboole_0(X13,X12) = k3_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13)) )).

cnf(u1086,axiom,
    ( k2_xboole_0(X9,X8) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X8,X9)) )).

cnf(u2175,axiom,
    ( k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),k2_xboole_0(X12,X13)) )).

cnf(u944,axiom,
    ( k2_xboole_0(X6,X5) = k2_xboole_0(k4_xboole_0(X6,X5),k2_xboole_0(X5,X6)) )).

cnf(u658,axiom,
    ( k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5)) )).

cnf(u1960,axiom,
    ( k2_xboole_0(X23,X22) = k2_xboole_0(k2_xboole_0(X22,X23),k1_xboole_0) )).

cnf(u654,axiom,
    ( k2_xboole_0(X13,X12) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12)) )).

cnf(u6230,axiom,
    ( k2_xboole_0(X21,X22) = k2_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X22,X21)) )).

cnf(u247,axiom,
    ( k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) )).

cnf(u5446,axiom,
    ( k2_xboole_0(X15,X14) = k2_xboole_0(k2_xboole_0(X14,X15),X14) )).

cnf(u1073,axiom,
    ( k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),X5) )).

cnf(u1950,axiom,
    ( k2_xboole_0(X12,X13) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12)) )).

cnf(u657,axiom,
    ( k2_xboole_0(X10,X11) = k2_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) )).

cnf(u954,axiom,
    ( k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5)) )).

cnf(u253,axiom,
    ( k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1) )).

cnf(u254,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) )).

cnf(u6625,axiom,
    ( k2_xboole_0(X8,X7) = k2_xboole_0(X7,k2_xboole_0(X7,X8)) )).

cnf(u848,axiom,
    ( k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) )).

cnf(u46,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u228,axiom,
    ( k2_xboole_0(X5,X6) = k2_xboole_0(X5,k2_xboole_0(X5,X6)) )).

cnf(u98,axiom,
    ( k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) )).

cnf(u41,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u609,axiom,
    ( k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4 )).

cnf(u679,axiom,
    ( k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 )).

cnf(u648,axiom,
    ( k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 )).

cnf(u248,axiom,
    ( k2_xboole_0(X7,X7) = X7 )).

cnf(u39,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:44:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.47/0.56  % (31516)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.47/0.57  % (31532)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.57  % (31531)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.57  % (31515)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.47/0.58  % (31524)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.66/0.59  % (31523)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.59  % (31523)Refutation not found, incomplete strategy% (31523)------------------------------
% 1.66/0.59  % (31523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (31523)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.59  
% 1.66/0.59  % (31523)Memory used [KB]: 10618
% 1.66/0.59  % (31523)Time elapsed: 0.151 s
% 1.66/0.59  % (31523)------------------------------
% 1.66/0.59  % (31523)------------------------------
% 1.66/0.60  % (31532)Refutation not found, incomplete strategy% (31532)------------------------------
% 1.66/0.60  % (31532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (31511)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.66/0.60  % (31532)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (31532)Memory used [KB]: 6268
% 1.66/0.60  % (31532)Time elapsed: 0.164 s
% 1.66/0.60  % (31532)------------------------------
% 1.66/0.60  % (31532)------------------------------
% 1.66/0.62  % (31509)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.66/0.62  % (31507)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.66/0.62  % (31510)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.66/0.62  % (31512)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.66/0.63  % (31525)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.66/0.63  % (31508)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.63  % (31521)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.63  % (31530)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.63  % (31534)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.63  % (31533)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.66/0.64  % (31517)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.66/0.64  % (31535)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.66/0.64  % (31513)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.64  % (31529)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.66/0.64  % (31518)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.66/0.64  % (31520)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.66/0.64  % (31522)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.64  % (31536)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.64  % (31536)Refutation not found, incomplete strategy% (31536)------------------------------
% 1.66/0.64  % (31536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.64  % (31536)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.64  
% 1.66/0.64  % (31536)Memory used [KB]: 1663
% 1.66/0.64  % (31536)Time elapsed: 0.003 s
% 1.66/0.64  % (31527)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.66/0.64  % (31536)------------------------------
% 1.66/0.64  % (31536)------------------------------
% 1.66/0.64  % (31514)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.65  % (31526)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.65  % (31519)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.19/0.65  % (31508)Refutation not found, incomplete strategy% (31508)------------------------------
% 2.19/0.65  % (31508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (31508)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.65  
% 2.19/0.65  % (31508)Memory used [KB]: 1663
% 2.19/0.65  % (31508)Time elapsed: 0.207 s
% 2.19/0.65  % (31508)------------------------------
% 2.19/0.65  % (31508)------------------------------
% 2.19/0.65  % (31525)Refutation not found, incomplete strategy% (31525)------------------------------
% 2.19/0.65  % (31525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (31525)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.65  
% 2.19/0.65  % (31525)Memory used [KB]: 1791
% 2.19/0.65  % (31525)Time elapsed: 0.196 s
% 2.19/0.65  % (31525)------------------------------
% 2.19/0.65  % (31525)------------------------------
% 2.19/0.65  % (31519)Refutation not found, incomplete strategy% (31519)------------------------------
% 2.19/0.65  % (31519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (31519)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.65  
% 2.19/0.65  % (31519)Memory used [KB]: 10746
% 2.19/0.65  % (31519)Time elapsed: 0.216 s
% 2.19/0.65  % (31519)------------------------------
% 2.19/0.65  % (31519)------------------------------
% 2.19/0.65  % (31534)Refutation not found, incomplete strategy% (31534)------------------------------
% 2.19/0.65  % (31534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.65  % (31534)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.65  
% 2.19/0.65  % (31534)Memory used [KB]: 6268
% 2.19/0.65  % (31534)Time elapsed: 0.194 s
% 2.19/0.65  % (31534)------------------------------
% 2.19/0.65  % (31534)------------------------------
% 2.19/0.66  % (31528)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.19/0.66  % (31521)Refutation not found, incomplete strategy% (31521)------------------------------
% 2.19/0.66  % (31521)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.66  % (31521)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.66  
% 2.19/0.66  % (31521)Memory used [KB]: 1791
% 2.19/0.66  % (31521)Time elapsed: 0.176 s
% 2.19/0.66  % (31521)------------------------------
% 2.19/0.66  % (31521)------------------------------
% 2.33/0.69  % (31517)Refutation not found, incomplete strategy% (31517)------------------------------
% 2.33/0.69  % (31517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.33/0.70  % (31517)Termination reason: Refutation not found, incomplete strategy
% 2.33/0.70  
% 2.33/0.70  % (31517)Memory used [KB]: 11513
% 2.33/0.70  % (31517)Time elapsed: 0.257 s
% 2.33/0.70  % (31517)------------------------------
% 2.33/0.70  % (31517)------------------------------
% 2.58/0.72  % (31535)Refutation not found, incomplete strategy% (31535)------------------------------
% 2.58/0.72  % (31535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.58/0.72  % (31535)Termination reason: Refutation not found, incomplete strategy
% 2.58/0.72  
% 2.58/0.72  % (31535)Memory used [KB]: 11897
% 2.58/0.72  % (31535)Time elapsed: 0.264 s
% 2.58/0.72  % (31535)------------------------------
% 2.58/0.72  % (31535)------------------------------
% 2.58/0.73  % (31538)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.58/0.73  % (31537)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.78/0.76  % (31539)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.78/0.78  % (31541)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.78/0.78  % (31540)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.78/0.78  % (31539)Refutation not found, incomplete strategy% (31539)------------------------------
% 2.78/0.78  % (31539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.78  % (31539)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.78  
% 2.78/0.78  % (31539)Memory used [KB]: 6268
% 2.78/0.78  % (31539)Time elapsed: 0.096 s
% 2.78/0.78  % (31539)------------------------------
% 2.78/0.78  % (31539)------------------------------
% 2.78/0.78  % (31510)Refutation not found, incomplete strategy% (31510)------------------------------
% 2.78/0.78  % (31510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.78  % (31510)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.78  
% 2.78/0.78  % (31510)Memory used [KB]: 6268
% 2.78/0.78  % (31510)Time elapsed: 0.340 s
% 2.78/0.78  % (31510)------------------------------
% 2.78/0.78  % (31510)------------------------------
% 2.78/0.78  % (31544)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.78/0.78  % (31542)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.78/0.79  % (31507)Refutation not found, incomplete strategy% (31507)------------------------------
% 2.78/0.79  % (31507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.79  % (31543)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.78/0.79  % (31540)Refutation not found, incomplete strategy% (31540)------------------------------
% 2.78/0.79  % (31540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.79  % (31540)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.79  
% 2.78/0.79  % (31540)Memory used [KB]: 10874
% 2.78/0.79  % (31540)Time elapsed: 0.098 s
% 2.78/0.79  % (31540)------------------------------
% 2.78/0.79  % (31540)------------------------------
% 2.78/0.79  % (31543)Refutation not found, incomplete strategy% (31543)------------------------------
% 2.78/0.79  % (31543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.79  % (31515)Refutation not found, incomplete strategy% (31515)------------------------------
% 2.78/0.79  % (31515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.80  % (31507)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.80  
% 2.78/0.80  % (31507)Memory used [KB]: 1791
% 2.78/0.80  % (31507)Time elapsed: 0.346 s
% 2.78/0.80  % (31507)------------------------------
% 2.78/0.80  % (31507)------------------------------
% 2.78/0.81  % (31522)Refutation not found, incomplete strategy% (31522)------------------------------
% 2.78/0.81  % (31522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.78/0.81  % (31522)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.81  
% 2.78/0.81  % (31522)Memory used [KB]: 6268
% 2.78/0.81  % (31522)Time elapsed: 0.375 s
% 2.78/0.81  % (31522)------------------------------
% 2.78/0.81  % (31522)------------------------------
% 2.78/0.81  % (31543)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.81  
% 2.78/0.81  % (31543)Memory used [KB]: 10746
% 2.78/0.81  % (31543)Time elapsed: 0.113 s
% 2.78/0.81  % (31543)------------------------------
% 2.78/0.81  % (31543)------------------------------
% 2.78/0.81  % (31515)Termination reason: Refutation not found, incomplete strategy
% 2.78/0.81  
% 2.78/0.81  % (31515)Memory used [KB]: 6396
% 2.78/0.81  % (31515)Time elapsed: 0.354 s
% 2.78/0.81  % (31515)------------------------------
% 2.78/0.81  % (31515)------------------------------
% 2.78/0.82  % (31548)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.35/0.84  % (31559)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.35/0.85  % (31531)Time limit reached!
% 3.35/0.85  % (31531)------------------------------
% 3.35/0.85  % (31531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.86  % (31509)Time limit reached!
% 3.35/0.86  % (31509)------------------------------
% 3.35/0.86  % (31509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.86  % (31531)Termination reason: Time limit
% 3.35/0.86  
% 3.35/0.86  % (31531)Memory used [KB]: 12920
% 3.35/0.86  % (31531)Time elapsed: 0.413 s
% 3.35/0.86  % (31531)------------------------------
% 3.35/0.86  % (31531)------------------------------
% 3.35/0.87  % (31509)Termination reason: Time limit
% 3.35/0.87  
% 3.35/0.87  % (31509)Memory used [KB]: 6524
% 3.35/0.87  % (31509)Time elapsed: 0.421 s
% 3.35/0.87  % (31509)------------------------------
% 3.35/0.87  % (31509)------------------------------
% 3.35/0.87  % (31559)Refutation not found, incomplete strategy% (31559)------------------------------
% 3.35/0.87  % (31559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.87  % (31559)Termination reason: Refutation not found, incomplete strategy
% 3.35/0.87  
% 3.35/0.87  % (31559)Memory used [KB]: 11001
% 3.35/0.87  % (31559)Time elapsed: 0.127 s
% 3.35/0.87  % (31559)------------------------------
% 3.35/0.87  % (31559)------------------------------
% 3.35/0.88  % (31541)Refutation not found, incomplete strategy% (31541)------------------------------
% 3.35/0.88  % (31541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.35/0.88  % (31541)Termination reason: Refutation not found, incomplete strategy
% 3.35/0.88  
% 3.35/0.88  % (31541)Memory used [KB]: 11513
% 3.35/0.88  % (31541)Time elapsed: 0.204 s
% 3.35/0.88  % (31541)------------------------------
% 3.35/0.88  % (31541)------------------------------
% 3.64/0.88  % (31591)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.64/0.89  % SZS status CounterSatisfiable for theBenchmark
% 3.64/0.89  % (31514)# SZS output start Saturation.
% 3.64/0.89  cnf(u62,axiom,
% 3.64/0.89      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u36,negated_conjecture,
% 3.64/0.89      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 3.64/0.89  
% 3.64/0.89  cnf(u35,negated_conjecture,
% 3.64/0.89      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 3.64/0.89  
% 3.64/0.89  cnf(u106,negated_conjecture,
% 3.64/0.89      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u107,negated_conjecture,
% 3.64/0.89      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK2) = k2_xboole_0(X1,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u58,axiom,
% 3.64/0.89      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u59,axiom,
% 3.64/0.89      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u108,axiom,
% 3.64/0.89      ~m1_subset_1(X3,k1_zfmisc_1(X2)) | k2_xboole_0(X3,X2) = k4_subset_1(X2,X3,X2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u38,negated_conjecture,
% 3.64/0.89      r1_xboole_0(sK1,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u57,axiom,
% 3.64/0.89      ~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u424,negated_conjecture,
% 3.64/0.89      r1_tarski(sK2,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u184,negated_conjecture,
% 3.64/0.89      r1_tarski(sK1,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u4524,axiom,
% 3.64/0.89      r1_tarski(k3_xboole_0(X15,X16),k3_xboole_0(X16,X15))).
% 3.64/0.89  
% 3.64/0.89  cnf(u524,axiom,
% 3.64/0.89      r1_tarski(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))).
% 3.64/0.89  
% 3.64/0.89  cnf(u477,axiom,
% 3.64/0.89      r1_tarski(X4,k2_xboole_0(X4,X5))).
% 3.64/0.89  
% 3.64/0.89  cnf(u278,axiom,
% 3.64/0.89      r1_tarski(X9,k2_xboole_0(X8,X9))).
% 3.64/0.89  
% 3.64/0.89  cnf(u186,axiom,
% 3.64/0.89      r1_tarski(k4_xboole_0(X8,X9),k2_xboole_0(X9,X8))).
% 3.64/0.89  
% 3.64/0.89  cnf(u97,axiom,
% 3.64/0.89      r1_tarski(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5))).
% 3.64/0.89  
% 3.64/0.89  cnf(u141,axiom,
% 3.64/0.89      r1_tarski(k3_xboole_0(X1,X0),X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u64,axiom,
% 3.64/0.89      r1_tarski(k1_xboole_0,X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u43,axiom,
% 3.64/0.89      r1_tarski(k4_xboole_0(X0,X1),X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u79,axiom,
% 3.64/0.89      r1_tarski(k3_xboole_0(X0,X1),X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u60,axiom,
% 3.64/0.89      r1_tarski(X1,X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u431,negated_conjecture,
% 3.64/0.89      ~r1_tarski(k2_struct_0(sK0),sK2) | k2_struct_0(sK0) = sK2).
% 3.64/0.89  
% 3.64/0.89  cnf(u258,negated_conjecture,
% 3.64/0.89      ~r1_tarski(k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u907,axiom,
% 3.64/0.89      ~r1_tarski(k2_xboole_0(X13,X14),X13) | k2_xboole_0(X13,X14) = X13).
% 3.64/0.89  
% 3.64/0.89  cnf(u338,axiom,
% 3.64/0.89      ~r1_tarski(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12)) | k2_xboole_0(X12,X13) = k4_xboole_0(X13,X12)).
% 3.64/0.89  
% 3.64/0.89  cnf(u170,axiom,
% 3.64/0.89      ~r1_tarski(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) | k2_xboole_0(X0,X1) = k4_xboole_0(X0,X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u339,axiom,
% 3.64/0.89      ~r1_tarski(k2_xboole_0(X14,X15),X15) | k2_xboole_0(X14,X15) = X15).
% 3.64/0.89  
% 3.64/0.89  cnf(u123,axiom,
% 3.64/0.89      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u102,axiom,
% 3.64/0.89      ~r1_tarski(X1,k4_xboole_0(X1,X2)) | k4_xboole_0(X1,X2) = X1).
% 3.64/0.89  
% 3.64/0.89  cnf(u473,axiom,
% 3.64/0.89      ~r1_tarski(X0,k3_xboole_0(X1,X0)) | k3_xboole_0(X1,X0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u139,axiom,
% 3.64/0.89      ~r1_tarski(X0,k3_xboole_0(X0,X1)) | k3_xboole_0(X0,X1) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u53,axiom,
% 3.64/0.89      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u56,axiom,
% 3.64/0.89      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u252,negated_conjecture,
% 3.64/0.89      sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u766,negated_conjecture,
% 3.64/0.89      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u286,negated_conjecture,
% 3.64/0.89      sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u251,negated_conjecture,
% 3.64/0.89      sK2 = k4_xboole_0(sK2,sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u742,negated_conjecture,
% 3.64/0.89      sK2 = k3_xboole_0(k2_struct_0(sK0),sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u396,negated_conjecture,
% 3.64/0.89      sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u250,negated_conjecture,
% 3.64/0.89      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u806,negated_conjecture,
% 3.64/0.89      sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u115,negated_conjecture,
% 3.64/0.89      sK1 = k5_xboole_0(sK1,k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u402,negated_conjecture,
% 3.64/0.89      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u76,negated_conjecture,
% 3.64/0.89      sK1 = k4_xboole_0(sK1,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u432,negated_conjecture,
% 3.64/0.89      sK1 = k3_xboole_0(k2_struct_0(sK0),sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u259,negated_conjecture,
% 3.64/0.89      sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u417,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k5_xboole_0(sK1,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u121,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k5_xboole_0(sK2,sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u436,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u401,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u406,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u1080,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k2_xboole_0(sK2,sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u433,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u119,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u120,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u37,negated_conjecture,
% 3.64/0.89      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u103,negated_conjecture,
% 3.64/0.89      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u343,axiom,
% 3.64/0.89      k4_subset_1(X0,X0,X0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u122,negated_conjecture,
% 3.64/0.89      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u113,negated_conjecture,
% 3.64/0.89      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u40,axiom,
% 3.64/0.89      k2_subset_1(X0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u4555,axiom,
% 3.64/0.89      k1_xboole_0 = k5_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X9,X10))).
% 3.64/0.89  
% 3.64/0.89  cnf(u801,axiom,
% 3.64/0.89      k1_xboole_0 = k5_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5))).
% 3.64/0.89  
% 3.64/0.89  cnf(u92,axiom,
% 3.64/0.89      k1_xboole_0 = k5_xboole_0(X4,X4)).
% 3.64/0.89  
% 3.64/0.89  cnf(u416,negated_conjecture,
% 3.64/0.89      k1_xboole_0 = k3_xboole_0(sK2,sK1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u88,negated_conjecture,
% 3.64/0.89      k1_xboole_0 = k3_xboole_0(sK1,sK2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u124,axiom,
% 3.64/0.89      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u153,axiom,
% 3.64/0.89      k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u395,negated_conjecture,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u392,negated_conjecture,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u136,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u590,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,X12),k2_xboole_0(X12,X13))).
% 3.64/0.89  
% 3.64/0.89  cnf(u589,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,X11),k2_xboole_0(X10,X11))).
% 3.64/0.89  
% 3.64/0.89  cnf(u202,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u4557,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k3_xboole_0(X20,X19),k3_xboole_0(X19,X20))).
% 3.64/0.89  
% 3.64/0.89  cnf(u2825,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u587,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k3_xboole_0(X7,X8),X7)).
% 3.64/0.89  
% 3.64/0.89  cnf(u255,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X9,X8))).
% 3.64/0.89  
% 3.64/0.89  cnf(u63,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u68,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u44,axiom,
% 3.64/0.89      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u1141,axiom,
% 3.64/0.89      k5_xboole_0(k3_xboole_0(X6,X5),k4_xboole_0(X5,X6)) = X5).
% 3.64/0.89  
% 3.64/0.89  cnf(u834,axiom,
% 3.64/0.89      k5_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11).
% 3.64/0.89  
% 3.64/0.89  cnf(u152,axiom,
% 3.64/0.89      k5_xboole_0(k1_xboole_0,X0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u610,axiom,
% 3.64/0.89      k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u613,axiom,
% 3.64/0.89      k5_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2).
% 3.64/0.89  
% 3.64/0.89  cnf(u647,axiom,
% 3.64/0.89      k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7).
% 3.64/0.89  
% 3.64/0.89  cnf(u836,axiom,
% 3.64/0.89      k5_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12)) = X12).
% 3.64/0.89  
% 3.64/0.89  cnf(u249,axiom,
% 3.64/0.89      k5_xboole_0(X0,k1_xboole_0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u104,negated_conjecture,
% 3.64/0.89      k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u231,axiom,
% 3.64/0.89      k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7).
% 3.64/0.89  
% 3.64/0.89  cnf(u100,axiom,
% 3.64/0.89      k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = X3).
% 3.64/0.89  
% 3.64/0.89  cnf(u210,axiom,
% 3.64/0.89      k5_xboole_0(k2_xboole_0(X4,X5),X4) = k4_xboole_0(X5,X4)).
% 3.64/0.89  
% 3.64/0.89  cnf(u80,axiom,
% 3.64/0.89      k4_xboole_0(X0,k1_xboole_0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u105,axiom,
% 3.64/0.89      k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3)).
% 3.64/0.89  
% 3.64/0.89  cnf(u211,axiom,
% 3.64/0.89      k5_xboole_0(k2_xboole_0(X7,X6),X6) = k4_xboole_0(X7,X6)).
% 3.64/0.89  
% 3.64/0.89  cnf(u89,axiom,
% 3.64/0.89      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u51,axiom,
% 3.64/0.89      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u292,axiom,
% 3.64/0.89      k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u201,axiom,
% 3.64/0.89      k4_xboole_0(X2,X3) = k4_xboole_0(X2,k3_xboole_0(X2,X3))).
% 3.64/0.89  
% 3.64/0.89  cnf(u93,axiom,
% 3.64/0.89      k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u52,axiom,
% 3.64/0.89      k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u738,axiom,
% 3.64/0.89      k4_xboole_0(X13,X12) = k3_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12))).
% 3.64/0.89  
% 3.64/0.89  cnf(u291,axiom,
% 3.64/0.89      k4_xboole_0(X6,X7) = k3_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))).
% 3.64/0.89  
% 3.64/0.89  cnf(u195,axiom,
% 3.64/0.89      k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))).
% 3.64/0.89  
% 3.64/0.89  cnf(u219,axiom,
% 3.64/0.89      k4_xboole_0(X2,X1) = k3_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X1,X2))).
% 3.64/0.89  
% 3.64/0.89  cnf(u171,axiom,
% 3.64/0.89      k4_xboole_0(X2,X3) = k3_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3))).
% 3.64/0.89  
% 3.64/0.89  cnf(u75,axiom,
% 3.64/0.89      k4_xboole_0(X1,X2) = k3_xboole_0(k4_xboole_0(X1,X2),X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u909,axiom,
% 3.64/0.89      k3_xboole_0(k2_xboole_0(X17,X18),X17) = X17).
% 3.64/0.89  
% 3.64/0.89  cnf(u739,axiom,
% 3.64/0.89      k3_xboole_0(k2_xboole_0(X14,X15),X15) = X15).
% 3.64/0.89  
% 3.64/0.89  cnf(u3416,axiom,
% 3.64/0.89      k3_xboole_0(X41,X42) = k5_xboole_0(k3_xboole_0(X42,X41),k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u3412,axiom,
% 3.64/0.89      k3_xboole_0(X37,X38) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X38,X37))).
% 3.64/0.89  
% 3.64/0.89  cnf(u3819,axiom,
% 3.64/0.89      k3_xboole_0(X12,X11) = k5_xboole_0(X11,k4_xboole_0(X11,X12))).
% 3.64/0.89  
% 3.64/0.89  cnf(u214,axiom,
% 3.64/0.89      k5_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10)).
% 3.64/0.89  
% 3.64/0.89  cnf(u6585,axiom,
% 3.64/0.89      k3_xboole_0(X4,X3) = k4_xboole_0(k3_xboole_0(X3,X4),k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u1143,axiom,
% 3.64/0.89      k3_xboole_0(X12,X11) = k4_xboole_0(X11,k4_xboole_0(X11,X12))).
% 3.64/0.89  
% 3.64/0.89  cnf(u49,axiom,
% 3.64/0.89      k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u474,axiom,
% 3.64/0.89      k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X3)).
% 3.64/0.89  
% 3.64/0.89  cnf(u4541,axiom,
% 3.64/0.89      k3_xboole_0(X11,X12) = k3_xboole_0(k3_xboole_0(X12,X11),k3_xboole_0(X11,X12))).
% 3.64/0.89  
% 3.64/0.89  cnf(u4528,axiom,
% 3.64/0.89      k3_xboole_0(X23,X24) = k3_xboole_0(k3_xboole_0(X23,X24),k3_xboole_0(X24,X23))).
% 3.64/0.89  
% 3.64/0.89  cnf(u1151,axiom,
% 3.64/0.89      k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u1139,axiom,
% 3.64/0.89      k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X4,X3))).
% 3.64/0.89  
% 3.64/0.89  cnf(u309,axiom,
% 3.64/0.89      k3_xboole_0(X8,X9) = k3_xboole_0(X8,k3_xboole_0(X8,X9))).
% 3.64/0.89  
% 3.64/0.89  cnf(u6298,axiom,
% 3.64/0.89      k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X8,X7),X7)).
% 3.64/0.89  
% 3.64/0.89  cnf(u140,axiom,
% 3.64/0.89      k3_xboole_0(X2,X3) = k3_xboole_0(k3_xboole_0(X2,X3),X2)).
% 3.64/0.89  
% 3.64/0.89  cnf(u45,axiom,
% 3.64/0.89      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u7735,axiom,
% 3.64/0.89      k3_xboole_0(X19,X18) = k2_xboole_0(k3_xboole_0(X18,X19),k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u7731,axiom,
% 3.64/0.89      k3_xboole_0(X9,X8) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X8,X9))).
% 3.64/0.89  
% 3.64/0.89  cnf(u4537,axiom,
% 3.64/0.89      k3_xboole_0(X42,X41) = k2_xboole_0(k3_xboole_0(X41,X42),k3_xboole_0(X42,X41))).
% 3.64/0.89  
% 3.64/0.89  cnf(u4534,axiom,
% 3.64/0.89      k3_xboole_0(X36,X35) = k2_xboole_0(k3_xboole_0(X36,X35),k3_xboole_0(X35,X36))).
% 3.64/0.89  
% 3.64/0.89  cnf(u71,axiom,
% 3.64/0.89      k3_xboole_0(X0,X0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u72,axiom,
% 3.64/0.89      k3_xboole_0(X1,k2_xboole_0(X2,X1)) = X1).
% 3.64/0.89  
% 3.64/0.89  cnf(u47,axiom,
% 3.64/0.89      k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u341,negated_conjecture,
% 3.64/0.89      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u340,negated_conjecture,
% 3.64/0.89      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u65,axiom,
% 3.64/0.89      k2_xboole_0(k1_xboole_0,X0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u1356,axiom,
% 3.64/0.89      k2_xboole_0(k4_xboole_0(X24,X25),X24) = X24).
% 3.64/0.89  
% 3.64/0.89  cnf(u3028,axiom,
% 3.64/0.89      k2_xboole_0(k3_xboole_0(X42,X41),X41) = X41).
% 3.64/0.89  
% 3.64/0.89  cnf(u1075,axiom,
% 3.64/0.89      k2_xboole_0(k3_xboole_0(X9,X10),X9) = X9).
% 3.64/0.89  
% 3.64/0.89  cnf(u48,axiom,
% 3.64/0.89      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u1225,axiom,
% 3.64/0.89      k2_xboole_0(X16,X17) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X17,X16))).
% 3.64/0.89  
% 3.64/0.89  cnf(u660,axiom,
% 3.64/0.89      k2_xboole_0(X12,X13) = k5_xboole_0(k4_xboole_0(X13,X12),X12)).
% 3.64/0.89  
% 3.64/0.89  cnf(u653,axiom,
% 3.64/0.89      k2_xboole_0(X10,X11) = k5_xboole_0(k4_xboole_0(X10,X11),X11)).
% 3.64/0.89  
% 3.64/0.89  cnf(u1093,axiom,
% 3.64/0.89      k2_xboole_0(X28,X29) = k5_xboole_0(k2_xboole_0(X29,X28),k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u661,axiom,
% 3.64/0.89      k2_xboole_0(X14,X15) = k5_xboole_0(X15,k4_xboole_0(X14,X15))).
% 3.64/0.89  
% 3.64/0.89  cnf(u50,axiom,
% 3.64/0.89      k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))).
% 3.64/0.89  
% 3.64/0.89  cnf(u280,axiom,
% 3.64/0.89      k2_xboole_0(X6,X5) = k4_xboole_0(k2_xboole_0(X5,X6),k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u1068,axiom,
% 3.64/0.89      k2_xboole_0(X21,X20) = k3_xboole_0(k2_xboole_0(X20,X21),k2_xboole_0(X21,X20))).
% 3.64/0.89  
% 3.64/0.89  cnf(u242,axiom,
% 3.64/0.89      k2_xboole_0(X13,X12) = k3_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13))).
% 3.64/0.89  
% 3.64/0.89  cnf(u1086,axiom,
% 3.64/0.89      k2_xboole_0(X9,X8) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X8,X9))).
% 3.64/0.89  
% 3.64/0.89  cnf(u2175,axiom,
% 3.64/0.89      k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),k2_xboole_0(X12,X13))).
% 3.64/0.89  
% 3.64/0.89  cnf(u944,axiom,
% 3.64/0.89      k2_xboole_0(X6,X5) = k2_xboole_0(k4_xboole_0(X6,X5),k2_xboole_0(X5,X6))).
% 3.64/0.89  
% 3.64/0.89  cnf(u658,axiom,
% 3.64/0.89      k2_xboole_0(X4,X5) = k2_xboole_0(k4_xboole_0(X4,X5),k2_xboole_0(X4,X5))).
% 3.64/0.89  
% 3.64/0.89  cnf(u1960,axiom,
% 3.64/0.89      k2_xboole_0(X23,X22) = k2_xboole_0(k2_xboole_0(X22,X23),k1_xboole_0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u654,axiom,
% 3.64/0.89      k2_xboole_0(X13,X12) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12))).
% 3.64/0.89  
% 3.64/0.89  cnf(u6230,axiom,
% 3.64/0.89      k2_xboole_0(X21,X22) = k2_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X22,X21))).
% 3.64/0.89  
% 3.64/0.89  cnf(u247,axiom,
% 3.64/0.89      k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))).
% 3.64/0.89  
% 3.64/0.89  cnf(u5446,axiom,
% 3.64/0.89      k2_xboole_0(X15,X14) = k2_xboole_0(k2_xboole_0(X14,X15),X14)).
% 3.64/0.89  
% 3.64/0.89  cnf(u1073,axiom,
% 3.64/0.89      k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),X5)).
% 3.64/0.89  
% 3.64/0.89  cnf(u1950,axiom,
% 3.64/0.89      k2_xboole_0(X12,X13) = k2_xboole_0(k2_xboole_0(X12,X13),k4_xboole_0(X13,X12))).
% 3.64/0.89  
% 3.64/0.89  cnf(u657,axiom,
% 3.64/0.89      k2_xboole_0(X10,X11) = k2_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11))).
% 3.64/0.89  
% 3.64/0.89  cnf(u954,axiom,
% 3.64/0.89      k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5))).
% 3.64/0.89  
% 3.64/0.89  cnf(u253,axiom,
% 3.64/0.89      k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1)).
% 3.64/0.89  
% 3.64/0.89  cnf(u254,axiom,
% 3.64/0.89      k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u6625,axiom,
% 3.64/0.89      k2_xboole_0(X8,X7) = k2_xboole_0(X7,k2_xboole_0(X7,X8))).
% 3.64/0.89  
% 3.64/0.89  cnf(u848,axiom,
% 3.64/0.89      k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u46,axiom,
% 3.64/0.89      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 3.64/0.89  
% 3.64/0.89  cnf(u228,axiom,
% 3.64/0.89      k2_xboole_0(X5,X6) = k2_xboole_0(X5,k2_xboole_0(X5,X6))).
% 3.64/0.89  
% 3.64/0.89  cnf(u98,axiom,
% 3.64/0.89      k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))).
% 3.64/0.89  
% 3.64/0.89  cnf(u41,axiom,
% 3.64/0.89      k2_xboole_0(X0,k1_xboole_0) = X0).
% 3.64/0.89  
% 3.64/0.89  cnf(u609,axiom,
% 3.64/0.89      k2_xboole_0(X4,k4_xboole_0(X4,X5)) = X4).
% 3.64/0.89  
% 3.64/0.89  cnf(u679,axiom,
% 3.64/0.89      k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1).
% 3.64/0.89  
% 3.64/0.89  cnf(u648,axiom,
% 3.64/0.89      k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6).
% 3.64/0.89  
% 3.64/0.89  cnf(u248,axiom,
% 3.64/0.89      k2_xboole_0(X7,X7) = X7).
% 3.64/0.89  
% 3.64/0.89  cnf(u39,negated_conjecture,
% 3.64/0.89      k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2).
% 3.64/0.89  
% 3.64/0.89  % (31514)# SZS output end Saturation.
% 3.64/0.89  % (31514)------------------------------
% 3.64/0.89  % (31514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.64/0.89  % (31514)Termination reason: Satisfiable
% 3.64/0.89  
% 3.64/0.89  % (31514)Memory used [KB]: 4477
% 3.64/0.89  % (31514)Time elapsed: 0.455 s
% 3.64/0.89  % (31514)------------------------------
% 3.64/0.89  % (31514)------------------------------
% 3.64/0.89  % (31506)Success in time 0.512 s
%------------------------------------------------------------------------------
