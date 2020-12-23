%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:59 EST 2020

% Result     : CounterSatisfiable 5.96s
% Output     : Saturation 5.96s
% Verified   : 
% Statistics : Number of clauses        :  129 ( 129 expanded)
%              Number of leaves         :  129 ( 129 expanded)
%              Depth                    :    0
%              Number of atoms          :  136 ( 136 expanded)
%              Number of equality atoms :  125 ( 125 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u49,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u30,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u2216,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) )).

cnf(u2217,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1) )).

cnf(u44,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u2218,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3) )).

cnf(u28,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u43,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 )).

cnf(u1239,axiom,
    ( k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3) )).

cnf(u4881,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u4880,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u2894,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u2895,negated_conjecture,
    ( sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1) )).

cnf(u2422,negated_conjecture,
    ( sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2) )).

cnf(u27,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u2425,negated_conjecture,
    ( sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u2424,negated_conjecture,
    ( sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u7763,axiom,
    ( k2_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X76,k4_xboole_0(X76,X75)),k1_xboole_0) )).

cnf(u7349,axiom,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X75,k4_xboole_0(X75,X76))) = k5_xboole_0(k4_xboole_0(X76,k4_xboole_0(X76,X75)),k1_xboole_0) )).

cnf(u6457,axiom,
    ( k4_xboole_0(k4_xboole_0(X71,k4_xboole_0(X71,X72)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X71)),k1_xboole_0) )).

cnf(u6461,axiom,
    ( k4_xboole_0(X78,k4_xboole_0(X78,X77)) = k5_xboole_0(k4_xboole_0(X77,k4_xboole_0(X77,X78)),k1_xboole_0) )).

cnf(u4274,axiom,
    ( k1_xboole_0 = k5_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36))) )).

cnf(u781,axiom,
    ( k1_xboole_0 = k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X8,X7)) )).

cnf(u386,axiom,
    ( k4_xboole_0(X9,X8) = k5_xboole_0(k2_xboole_0(X8,X9),X8) )).

cnf(u382,axiom,
    ( k4_xboole_0(X6,X7) = k5_xboole_0(k2_xboole_0(X6,X7),X7) )).

cnf(u1195,axiom,
    ( k2_xboole_0(X8,X7) = k5_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0) )).

cnf(u680,axiom,
    ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) )).

cnf(u336,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u768,axiom,
    ( k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k5_xboole_0(X13,k4_xboole_0(X13,X14)) )).

cnf(u365,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) )).

cnf(u46,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )).

cnf(u2427,negated_conjecture,
    ( sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u436,negated_conjecture,
    ( sK2 = k4_xboole_0(sK2,sK1) )).

cnf(u2426,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u66,negated_conjecture,
    ( sK1 = k4_xboole_0(sK1,sK2) )).

cnf(u1238,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1) )).

cnf(u1237,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

cnf(u2431,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)) )).

cnf(u2429,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) )).

cnf(u4243,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),k4_xboole_0(X15,k4_xboole_0(X15,X16))) )).

cnf(u496,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) )).

cnf(u465,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) )).

cnf(u469,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8) )).

cnf(u149,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X2,X1)) )).

cnf(u71,axiom,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) )).

cnf(u137,axiom,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X6)) )).

cnf(u50,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u54,axiom,
    ( k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) )).

cnf(u35,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u6435,axiom,
    ( k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0) )).

cnf(u3043,axiom,
    ( k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X10,X9)) = k4_xboole_0(X10,k4_xboole_0(X10,X9)) )).

cnf(u1874,axiom,
    ( k4_xboole_0(X7,k4_xboole_0(X7,X6)) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k1_xboole_0) )).

cnf(u369,axiom,
    ( k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),k4_xboole_0(X8,X9)) )).

cnf(u425,axiom,
    ( k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5))) )).

cnf(u678,axiom,
    ( k4_xboole_0(X5,X6) = k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))) )).

cnf(u498,axiom,
    ( k4_xboole_0(X16,X17) = k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17))) )).

cnf(u47,axiom,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) )).

cnf(u113,axiom,
    ( k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5) )).

cnf(u79,axiom,
    ( k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) )).

cnf(u41,axiom,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) )).

cnf(u390,axiom,
    ( k2_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X15,X14),k1_xboole_0) )).

cnf(u2434,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u2433,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK1) )).

cnf(u2461,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0)) )).

cnf(u2471,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK2,sK1) )).

cnf(u2437,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0)) )).

cnf(u2423,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u2896,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u2428,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u7372,axiom,
    ( k4_xboole_0(k4_xboole_0(X46,k4_xboole_0(X46,X47)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X47,k4_xboole_0(X47,X46)),k1_xboole_0) )).

cnf(u7340,axiom,
    ( k4_xboole_0(k4_xboole_0(X58,k4_xboole_0(X58,X57)),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X57,k4_xboole_0(X57,X58))) )).

cnf(u3414,axiom,
    ( k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X35,k4_xboole_0(X35,X34))) )).

cnf(u4226,axiom,
    ( k4_xboole_0(X74,k4_xboole_0(X74,X73)) = k2_xboole_0(k4_xboole_0(X73,k4_xboole_0(X73,X74)),k4_xboole_0(X74,k4_xboole_0(X74,X73))) )).

cnf(u4225,axiom,
    ( k4_xboole_0(X72,k4_xboole_0(X72,X71)) = k2_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X71)),k4_xboole_0(X71,k4_xboole_0(X71,X72))) )).

cnf(u3151,axiom,
    ( k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k2_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X34)),k1_xboole_0) )).

cnf(u6890,axiom,
    ( k2_xboole_0(k4_xboole_0(X79,k4_xboole_0(X79,X80)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X80,k4_xboole_0(X80,X79)),k1_xboole_0) )).

cnf(u6879,axiom,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X58)),k1_xboole_0) )).

cnf(u6853,axiom,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k4_xboole_0(X6,X5))) )).

cnf(u1548,axiom,
    ( k2_xboole_0(X25,X24) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X24,X25)) )).

cnf(u595,axiom,
    ( k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X12,X13)) )).

cnf(u5308,axiom,
    ( k2_xboole_0(X54,X53) = k2_xboole_0(k4_xboole_0(X54,X53),k2_xboole_0(X53,X54)) )).

cnf(u1467,axiom,
    ( k2_xboole_0(X19,X18) = k2_xboole_0(k4_xboole_0(X18,X19),k2_xboole_0(X18,X19)) )).

cnf(u135,axiom,
    ( k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8)) )).

cnf(u871,axiom,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X2,X1),X1) )).

cnf(u700,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),X1) )).

cnf(u974,axiom,
    ( k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) )).

cnf(u4489,axiom,
    ( k2_xboole_0(X56,X57) = k2_xboole_0(k2_xboole_0(X57,X56),k4_xboole_0(X56,X57)) )).

cnf(u981,axiom,
    ( k2_xboole_0(X19,X18) = k2_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19)) )).

cnf(u133,axiom,
    ( k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6)) )).

cnf(u2006,axiom,
    ( k2_xboole_0(X23,X22) = k2_xboole_0(k2_xboole_0(X22,X23),X22) )).

cnf(u978,axiom,
    ( k2_xboole_0(X15,X14) = k2_xboole_0(k2_xboole_0(X14,X15),X15) )).

cnf(u291,axiom,
    ( k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) )).

cnf(u165,axiom,
    ( k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1)) )).

cnf(u169,axiom,
    ( k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5)) )).

cnf(u75,axiom,
    ( k2_xboole_0(X4,X3) = k2_xboole_0(k2_xboole_0(X4,X3),X3) )).

cnf(u74,axiom,
    ( k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) )).

cnf(u487,axiom,
    ( k2_xboole_0(X12,X13) = k2_xboole_0(X13,k4_xboole_0(X12,X13)) )).

cnf(u1464,axiom,
    ( k2_xboole_0(X13,X12) = k2_xboole_0(X12,k2_xboole_0(X12,X13)) )).

cnf(u175,axiom,
    ( k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4)) )).

cnf(u37,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u99,axiom,
    ( k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) )).

cnf(u88,axiom,
    ( k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) )).

cnf(u39,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) )).

cnf(u444,axiom,
    ( k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 )).

cnf(u591,axiom,
    ( k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5) = X5 )).

cnf(u701,axiom,
    ( k5_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = X3 )).

cnf(u381,axiom,
    ( k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11 )).

cnf(u4883,axiom,
    ( k4_subset_1(X0,X0,X0) = X0 )).

cnf(u31,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u783,axiom,
    ( k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)) = X11 )).

cnf(u335,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u388,axiom,
    ( k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5 )).

cnf(u385,axiom,
    ( k4_xboole_0(X12,k4_xboole_0(X13,X12)) = X12 )).

cnf(u33,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u475,axiom,
    ( k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X21)),X20) = X20 )).

cnf(u479,axiom,
    ( k2_xboole_0(k4_xboole_0(X28,X29),X28) = X28 )).

cnf(u497,axiom,
    ( k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2 )).

cnf(u463,axiom,
    ( k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 )).

cnf(u48,axiom,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 )).

cnf(u51,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 )).

cnf(u555,axiom,
    ( k2_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))) = X5 )).

cnf(u471,axiom,
    ( k2_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X12,X13))) = X12 )).

cnf(u472,axiom,
    ( k2_xboole_0(X14,k4_xboole_0(X14,X15)) = X14 )).

cnf(u76,axiom,
    ( k2_xboole_0(X5,X5) = X5 )).

cnf(u32,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u29,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:53:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.27/0.52  % (3069)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.53  % (3074)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.27/0.53  % (3078)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.53  % (3073)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.53  % (3068)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.54  % (3072)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.54  % (3066)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.54  % (3087)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.54  % (3079)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.54  % (3079)Refutation not found, incomplete strategy% (3079)------------------------------
% 1.27/0.54  % (3079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (3079)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (3079)Memory used [KB]: 6140
% 1.27/0.54  % (3079)Time elapsed: 0.002 s
% 1.27/0.54  % (3079)------------------------------
% 1.27/0.54  % (3079)------------------------------
% 1.38/0.54  % (3073)Refutation not found, incomplete strategy% (3073)------------------------------
% 1.38/0.54  % (3073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (3073)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (3073)Memory used [KB]: 10746
% 1.38/0.54  % (3073)Time elapsed: 0.120 s
% 1.38/0.54  % (3073)------------------------------
% 1.38/0.54  % (3073)------------------------------
% 1.38/0.54  % (3067)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (3093)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (3092)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (3085)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.54  % (3066)Refutation not found, incomplete strategy% (3066)------------------------------
% 1.38/0.54  % (3066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (3087)Refutation not found, incomplete strategy% (3087)------------------------------
% 1.38/0.54  % (3087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (3087)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (3087)Memory used [KB]: 1791
% 1.38/0.54  % (3087)Time elapsed: 0.092 s
% 1.38/0.54  % (3087)------------------------------
% 1.38/0.54  % (3087)------------------------------
% 1.38/0.54  % (3066)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (3066)Memory used [KB]: 10874
% 1.38/0.54  % (3066)Time elapsed: 0.106 s
% 1.38/0.54  % (3066)------------------------------
% 1.38/0.54  % (3066)------------------------------
% 1.38/0.55  % (3064)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.55  % (3082)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (3071)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (3064)Refutation not found, incomplete strategy% (3064)------------------------------
% 1.38/0.55  % (3064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (3064)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (3064)Memory used [KB]: 1791
% 1.38/0.55  % (3064)Time elapsed: 0.135 s
% 1.38/0.55  % (3064)------------------------------
% 1.38/0.55  % (3064)------------------------------
% 1.38/0.55  % (3074)Refutation not found, incomplete strategy% (3074)------------------------------
% 1.38/0.55  % (3074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (3074)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (3074)Memory used [KB]: 10618
% 1.38/0.55  % (3074)Time elapsed: 0.135 s
% 1.38/0.55  % (3074)------------------------------
% 1.38/0.55  % (3074)------------------------------
% 1.38/0.55  % (3091)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (3084)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (3086)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (3072)Refutation not found, incomplete strategy% (3072)------------------------------
% 1.38/0.55  % (3072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (3072)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (3072)Memory used [KB]: 10746
% 1.38/0.55  % (3072)Time elapsed: 0.136 s
% 1.38/0.55  % (3072)------------------------------
% 1.38/0.55  % (3072)------------------------------
% 1.38/0.55  % (3070)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.55  % (3089)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (3090)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (3065)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.55  % (3077)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.55  % (3083)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.56  % (3081)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.56  % (3090)Refutation not found, incomplete strategy% (3090)------------------------------
% 1.38/0.56  % (3090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (3090)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (3090)Memory used [KB]: 10874
% 1.38/0.56  % (3090)Time elapsed: 0.151 s
% 1.38/0.56  % (3090)------------------------------
% 1.38/0.56  % (3090)------------------------------
% 1.38/0.56  % (3081)Refutation not found, incomplete strategy% (3081)------------------------------
% 1.38/0.56  % (3081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (3081)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (3081)Memory used [KB]: 10618
% 1.38/0.56  % (3081)Time elapsed: 0.149 s
% 1.38/0.56  % (3081)------------------------------
% 1.38/0.56  % (3081)------------------------------
% 1.38/0.56  % (3075)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (3088)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.56  % (3075)Refutation not found, incomplete strategy% (3075)------------------------------
% 1.38/0.56  % (3075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (3075)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (3075)Memory used [KB]: 10746
% 1.38/0.56  % (3075)Time elapsed: 0.152 s
% 1.38/0.56  % (3075)------------------------------
% 1.38/0.56  % (3075)------------------------------
% 1.38/0.56  % (3076)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.56  % (3085)Refutation not found, incomplete strategy% (3085)------------------------------
% 1.38/0.56  % (3085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (3085)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (3085)Memory used [KB]: 1791
% 1.38/0.56  % (3085)Time elapsed: 0.140 s
% 1.38/0.56  % (3085)------------------------------
% 1.38/0.56  % (3085)------------------------------
% 1.38/0.57  % (3080)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.57  % (3086)Refutation not found, incomplete strategy% (3086)------------------------------
% 1.38/0.57  % (3086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (3086)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (3086)Memory used [KB]: 11001
% 1.38/0.57  % (3086)Time elapsed: 0.152 s
% 1.38/0.57  % (3086)------------------------------
% 1.38/0.57  % (3086)------------------------------
% 1.38/0.57  % (3089)Refutation not found, incomplete strategy% (3089)------------------------------
% 1.38/0.57  % (3089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (3089)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.57  
% 1.38/0.57  % (3089)Memory used [KB]: 6524
% 1.38/0.57  % (3089)Time elapsed: 0.154 s
% 1.38/0.57  % (3089)------------------------------
% 1.38/0.57  % (3089)------------------------------
% 1.38/0.58  % (3084)Refutation not found, incomplete strategy% (3084)------------------------------
% 1.38/0.58  % (3084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (3084)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (3084)Memory used [KB]: 11001
% 1.38/0.58  % (3084)Time elapsed: 0.172 s
% 1.38/0.58  % (3084)------------------------------
% 1.38/0.58  % (3084)------------------------------
% 1.38/0.62  % (3068)Refutation not found, incomplete strategy% (3068)------------------------------
% 1.38/0.62  % (3068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.62  % (3068)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.62  
% 1.38/0.62  % (3068)Memory used [KB]: 6908
% 1.38/0.62  % (3068)Time elapsed: 0.204 s
% 1.38/0.62  % (3068)------------------------------
% 1.38/0.62  % (3068)------------------------------
% 1.94/0.68  % (3100)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.17/0.70  % (3102)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.17/0.72  % (3101)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.17/0.72  % (3104)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.17/0.73  % (3097)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.17/0.73  % (3097)Refutation not found, incomplete strategy% (3097)------------------------------
% 2.17/0.73  % (3097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.73  % (3097)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.73  
% 2.17/0.73  % (3097)Memory used [KB]: 6268
% 2.17/0.73  % (3097)Time elapsed: 0.153 s
% 2.17/0.73  % (3097)------------------------------
% 2.17/0.73  % (3097)------------------------------
% 2.17/0.74  % (3099)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.17/0.74  % (3103)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.17/0.74  % (3106)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.17/0.75  % (3098)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.51/0.76  % (3110)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.51/0.76  % (3111)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.55/0.77  % (3105)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.55/0.78  % (3110)Refutation not found, incomplete strategy% (3110)------------------------------
% 2.55/0.78  % (3110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.78  % (3110)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.78  
% 2.55/0.78  % (3110)Memory used [KB]: 6396
% 2.55/0.78  % (3110)Time elapsed: 0.164 s
% 2.55/0.78  % (3110)------------------------------
% 2.55/0.78  % (3110)------------------------------
% 2.55/0.78  % (3111)Refutation not found, incomplete strategy% (3111)------------------------------
% 2.55/0.78  % (3111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.78  % (3111)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.78  
% 2.55/0.78  % (3111)Memory used [KB]: 1918
% 2.55/0.78  % (3111)Time elapsed: 0.187 s
% 2.55/0.78  % (3111)------------------------------
% 2.55/0.78  % (3111)------------------------------
% 2.55/0.79  % (3112)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.55/0.79  % (3113)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.55/0.79  % (3113)Refutation not found, incomplete strategy% (3113)------------------------------
% 2.55/0.79  % (3113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.79  % (3113)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.79  
% 2.55/0.79  % (3113)Memory used [KB]: 1791
% 2.55/0.79  % (3113)Time elapsed: 0.178 s
% 2.55/0.79  % (3113)------------------------------
% 2.55/0.79  % (3113)------------------------------
% 2.55/0.80  % (3105)Refutation not found, incomplete strategy% (3105)------------------------------
% 2.55/0.80  % (3105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.55/0.80  % (3105)Termination reason: Refutation not found, incomplete strategy
% 2.55/0.80  
% 2.55/0.80  % (3105)Memory used [KB]: 1918
% 2.55/0.80  % (3105)Time elapsed: 0.202 s
% 2.55/0.80  % (3105)------------------------------
% 2.55/0.80  % (3105)------------------------------
% 2.97/0.81  % (3069)Time limit reached!
% 2.97/0.81  % (3069)------------------------------
% 2.97/0.81  % (3069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.82  % (3069)Termination reason: Time limit
% 2.97/0.82  % (3069)Termination phase: Saturation
% 2.97/0.82  
% 2.97/0.82  % (3069)Memory used [KB]: 8059
% 2.97/0.82  % (3069)Time elapsed: 0.400 s
% 2.97/0.82  % (3069)------------------------------
% 2.97/0.82  % (3069)------------------------------
% 2.97/0.84  % (3130)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.08/0.91  % (3065)Time limit reached!
% 3.08/0.91  % (3065)------------------------------
% 3.08/0.91  % (3065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.91  % (3065)Termination reason: Time limit
% 3.08/0.91  
% 3.08/0.91  % (3065)Memory used [KB]: 7931
% 3.08/0.91  % (3065)Time elapsed: 0.505 s
% 3.08/0.91  % (3065)------------------------------
% 3.08/0.91  % (3065)------------------------------
% 3.08/0.92  % (3136)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 3.08/0.92  % (3136)Refutation not found, incomplete strategy% (3136)------------------------------
% 3.08/0.92  % (3136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.08/0.92  % (3136)Termination reason: Refutation not found, incomplete strategy
% 3.08/0.92  
% 3.08/0.92  % (3136)Memory used [KB]: 6524
% 3.08/0.92  % (3136)Time elapsed: 0.158 s
% 3.08/0.92  % (3136)------------------------------
% 3.08/0.92  % (3136)------------------------------
% 3.39/0.93  % (3076)Time limit reached!
% 3.39/0.93  % (3076)------------------------------
% 3.39/0.93  % (3076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.39/0.93  % (3076)Termination reason: Time limit
% 3.39/0.93  
% 3.39/0.93  % (3076)Memory used [KB]: 8955
% 3.39/0.93  % (3076)Time elapsed: 0.520 s
% 3.39/0.93  % (3076)------------------------------
% 3.39/0.93  % (3076)------------------------------
% 3.39/0.94  % (3141)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 3.39/0.94  % (3144)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 3.39/0.94  % (3139)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 3.39/0.96  % (3138)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 3.39/0.98  % (3142)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 3.66/0.99  % (3101)Time limit reached!
% 3.66/0.99  % (3101)------------------------------
% 3.66/0.99  % (3101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.99  % (3101)Termination reason: Time limit
% 3.66/0.99  % (3101)Termination phase: Saturation
% 3.66/0.99  
% 3.66/0.99  % (3101)Memory used [KB]: 13304
% 3.66/0.99  % (3101)Time elapsed: 0.400 s
% 3.66/0.99  % (3101)------------------------------
% 3.66/0.99  % (3101)------------------------------
% 3.66/0.99  % (3071)Refutation not found, incomplete strategy% (3071)------------------------------
% 3.66/0.99  % (3071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.99  % (3071)Termination reason: Refutation not found, incomplete strategy
% 3.66/0.99  
% 3.66/0.99  % (3071)Memory used [KB]: 9722
% 3.66/0.99  % (3071)Time elapsed: 0.543 s
% 3.66/0.99  % (3071)------------------------------
% 3.66/0.99  % (3071)------------------------------
% 3.66/1.00  % (3080)Time limit reached!
% 3.66/1.00  % (3080)------------------------------
% 3.66/1.00  % (3080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/1.00  % (3080)Termination reason: Time limit
% 3.66/1.00  % (3080)Termination phase: Saturation
% 3.66/1.00  
% 3.66/1.00  % (3080)Memory used [KB]: 14839
% 3.66/1.00  % (3080)Time elapsed: 0.600 s
% 3.66/1.00  % (3080)------------------------------
% 3.66/1.00  % (3080)------------------------------
% 3.66/1.01  % (3092)Time limit reached!
% 3.66/1.01  % (3092)------------------------------
% 3.66/1.01  % (3092)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/1.01  % (3092)Termination reason: Time limit
% 3.66/1.01  
% 3.66/1.01  % (3092)Memory used [KB]: 8187
% 3.66/1.01  % (3092)Time elapsed: 0.611 s
% 3.66/1.01  % (3092)------------------------------
% 3.66/1.01  % (3092)------------------------------
% 4.05/1.05  % (3100)Time limit reached!
% 4.05/1.05  % (3100)------------------------------
% 4.05/1.05  % (3100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/1.05  % (3100)Termination reason: Time limit
% 4.05/1.05  
% 4.05/1.05  % (3100)Memory used [KB]: 8059
% 4.05/1.05  % (3100)Time elapsed: 0.405 s
% 4.05/1.05  % (3100)------------------------------
% 4.05/1.05  % (3100)------------------------------
% 4.05/1.07  % (3147)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 5.60/1.08  % (3150)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 5.60/1.11  % (3151)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.60/1.12  % (3149)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 5.96/1.12  % (3112)Time limit reached!
% 5.96/1.12  % (3112)------------------------------
% 5.96/1.12  % (3112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.96/1.12  % (3112)Termination reason: Time limit
% 5.96/1.12  
% 5.96/1.12  % (3112)Memory used [KB]: 2302
% 5.96/1.12  % (3112)Time elapsed: 0.508 s
% 5.96/1.12  % (3112)------------------------------
% 5.96/1.12  % (3112)------------------------------
% 5.96/1.13  % (3103)Refutation not found, incomplete strategy% (3103)------------------------------
% 5.96/1.13  % (3103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.96/1.13  % (3103)Termination reason: Refutation not found, incomplete strategy
% 5.96/1.13  
% 5.96/1.13  % (3103)Memory used [KB]: 5373
% 5.96/1.13  % (3103)Time elapsed: 0.541 s
% 5.96/1.13  % (3103)------------------------------
% 5.96/1.13  % (3103)------------------------------
% 5.96/1.13  % (3152)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 5.96/1.13  % (3153)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.96/1.13  % (3152)Refutation not found, incomplete strategy% (3152)------------------------------
% 5.96/1.13  % (3152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.96/1.13  % (3152)Termination reason: Refutation not found, incomplete strategy
% 5.96/1.13  
% 5.96/1.13  % (3152)Memory used [KB]: 6268
% 5.96/1.13  % (3152)Time elapsed: 0.113 s
% 5.96/1.13  % (3152)------------------------------
% 5.96/1.13  % (3152)------------------------------
% 5.96/1.14  % SZS status CounterSatisfiable for theBenchmark
% 5.96/1.14  % (3070)# SZS output start Saturation.
% 5.96/1.14  cnf(u49,axiom,
% 5.96/1.14      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u30,negated_conjecture,
% 5.96/1.14      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u26,negated_conjecture,
% 5.96/1.14      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2216,negated_conjecture,
% 5.96/1.14      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2217,negated_conjecture,
% 5.96/1.14      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u44,axiom,
% 5.96/1.14      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u45,axiom,
% 5.96/1.14      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2218,axiom,
% 5.96/1.14      ~m1_subset_1(X2,k1_zfmisc_1(X3)) | k2_xboole_0(X2,X3) = k4_subset_1(X3,X2,X3)).
% 5.96/1.14  
% 5.96/1.14  cnf(u28,negated_conjecture,
% 5.96/1.14      r1_xboole_0(sK1,sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u43,axiom,
% 5.96/1.14      ~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u1239,axiom,
% 5.96/1.14      k4_xboole_0(X2,X3) = k7_subset_1(X2,X2,X3)).
% 5.96/1.14  
% 5.96/1.14  cnf(u4881,negated_conjecture,
% 5.96/1.14      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u4880,negated_conjecture,
% 5.96/1.14      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2894,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2895,negated_conjecture,
% 5.96/1.14      sK1 = k4_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2422,negated_conjecture,
% 5.96/1.14      sK2 = k4_subset_1(u1_struct_0(sK0),sK2,sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u27,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2425,negated_conjecture,
% 5.96/1.14      sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2424,negated_conjecture,
% 5.96/1.14      sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u7763,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X75,k4_xboole_0(X75,X76)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X76,k4_xboole_0(X76,X75)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u7349,axiom,
% 5.96/1.14      k2_xboole_0(k1_xboole_0,k4_xboole_0(X75,k4_xboole_0(X75,X76))) = k5_xboole_0(k4_xboole_0(X76,k4_xboole_0(X76,X75)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u6457,axiom,
% 5.96/1.14      k4_xboole_0(k4_xboole_0(X71,k4_xboole_0(X71,X72)),k1_xboole_0) = k5_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X71)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u6461,axiom,
% 5.96/1.14      k4_xboole_0(X78,k4_xboole_0(X78,X77)) = k5_xboole_0(k4_xboole_0(X77,k4_xboole_0(X77,X78)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u4274,axiom,
% 5.96/1.14      k1_xboole_0 = k5_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,X35)),k4_xboole_0(X35,k4_xboole_0(X35,X36)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u781,axiom,
% 5.96/1.14      k1_xboole_0 = k5_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X8,X7))).
% 5.96/1.14  
% 5.96/1.14  cnf(u386,axiom,
% 5.96/1.14      k4_xboole_0(X9,X8) = k5_xboole_0(k2_xboole_0(X8,X9),X8)).
% 5.96/1.14  
% 5.96/1.14  cnf(u382,axiom,
% 5.96/1.14      k4_xboole_0(X6,X7) = k5_xboole_0(k2_xboole_0(X6,X7),X7)).
% 5.96/1.14  
% 5.96/1.14  cnf(u1195,axiom,
% 5.96/1.14      k2_xboole_0(X8,X7) = k5_xboole_0(k2_xboole_0(X7,X8),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u680,axiom,
% 5.96/1.14      k4_xboole_0(X5,k4_xboole_0(X5,X4)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))).
% 5.96/1.14  
% 5.96/1.14  cnf(u336,axiom,
% 5.96/1.14      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u768,axiom,
% 5.96/1.14      k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k5_xboole_0(X13,k4_xboole_0(X13,X14))).
% 5.96/1.14  
% 5.96/1.14  cnf(u365,axiom,
% 5.96/1.14      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u46,axiom,
% 5.96/1.14      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2427,negated_conjecture,
% 5.96/1.14      sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u436,negated_conjecture,
% 5.96/1.14      sK2 = k4_xboole_0(sK2,sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2426,negated_conjecture,
% 5.96/1.14      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u66,negated_conjecture,
% 5.96/1.14      sK1 = k4_xboole_0(sK1,sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u1238,negated_conjecture,
% 5.96/1.14      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u1237,negated_conjecture,
% 5.96/1.14      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2431,negated_conjecture,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2429,negated_conjecture,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u61,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u4243,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),k4_xboole_0(X15,k4_xboole_0(X15,X16)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u496,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6)).
% 5.96/1.14  
% 5.96/1.14  cnf(u465,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u469,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8)).
% 5.96/1.14  
% 5.96/1.14  cnf(u149,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X2,X1))).
% 5.96/1.14  
% 5.96/1.14  cnf(u71,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1))).
% 5.96/1.14  
% 5.96/1.14  cnf(u137,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X7,X6))).
% 5.96/1.14  
% 5.96/1.14  cnf(u50,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u54,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))).
% 5.96/1.14  
% 5.96/1.14  cnf(u35,axiom,
% 5.96/1.14      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 5.96/1.14  
% 5.96/1.14  cnf(u6435,axiom,
% 5.96/1.14      k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u3043,axiom,
% 5.96/1.14      k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X10)),k4_xboole_0(X10,X9)) = k4_xboole_0(X10,k4_xboole_0(X10,X9))).
% 5.96/1.14  
% 5.96/1.14  cnf(u1874,axiom,
% 5.96/1.14      k4_xboole_0(X7,k4_xboole_0(X7,X6)) = k4_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X7)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u369,axiom,
% 5.96/1.14      k4_xboole_0(X9,k4_xboole_0(X9,X8)) = k4_xboole_0(k4_xboole_0(X9,k4_xboole_0(X9,X8)),k4_xboole_0(X8,X9))).
% 5.96/1.14  
% 5.96/1.14  cnf(u425,axiom,
% 5.96/1.14      k4_xboole_0(X5,X6) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X6,X5)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u678,axiom,
% 5.96/1.14      k4_xboole_0(X5,X6) = k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u498,axiom,
% 5.96/1.14      k4_xboole_0(X16,X17) = k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u47,axiom,
% 5.96/1.14      k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u113,axiom,
% 5.96/1.14      k4_xboole_0(X6,X5) = k4_xboole_0(k4_xboole_0(X6,X5),X5)).
% 5.96/1.14  
% 5.96/1.14  cnf(u79,axiom,
% 5.96/1.14      k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u41,axiom,
% 5.96/1.14      k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u390,axiom,
% 5.96/1.14      k2_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X15,X14),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2434,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2433,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k2_xboole_0(k2_struct_0(sK0),sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2461,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k2_xboole_0(sK2,k2_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2471,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k2_xboole_0(sK2,sK1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2437,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k2_xboole_0(sK1,k2_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2423,negated_conjecture,
% 5.96/1.14      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 5.96/1.14  
% 5.96/1.14  cnf(u2896,negated_conjecture,
% 5.96/1.14      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2428,negated_conjecture,
% 5.96/1.14      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u7372,axiom,
% 5.96/1.14      k4_xboole_0(k4_xboole_0(X46,k4_xboole_0(X46,X47)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X47,k4_xboole_0(X47,X46)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u7340,axiom,
% 5.96/1.14      k4_xboole_0(k4_xboole_0(X58,k4_xboole_0(X58,X57)),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X57,k4_xboole_0(X57,X58)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u3414,axiom,
% 5.96/1.14      k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X35,k4_xboole_0(X35,X34)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u4226,axiom,
% 5.96/1.14      k4_xboole_0(X74,k4_xboole_0(X74,X73)) = k2_xboole_0(k4_xboole_0(X73,k4_xboole_0(X73,X74)),k4_xboole_0(X74,k4_xboole_0(X74,X73)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u4225,axiom,
% 5.96/1.14      k4_xboole_0(X72,k4_xboole_0(X72,X71)) = k2_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X71)),k4_xboole_0(X71,k4_xboole_0(X71,X72)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u3151,axiom,
% 5.96/1.14      k4_xboole_0(X34,k4_xboole_0(X34,X35)) = k2_xboole_0(k4_xboole_0(X35,k4_xboole_0(X35,X34)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u6890,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X79,k4_xboole_0(X79,X80)),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X80,k4_xboole_0(X80,X79)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u6879,axiom,
% 5.96/1.14      k2_xboole_0(k1_xboole_0,k4_xboole_0(X58,k4_xboole_0(X58,X57))) = k2_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X58)),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u6853,axiom,
% 5.96/1.14      k2_xboole_0(k1_xboole_0,k4_xboole_0(X5,k4_xboole_0(X5,X6))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k4_xboole_0(X6,X5)))).
% 5.96/1.14  
% 5.96/1.14  cnf(u1548,axiom,
% 5.96/1.14      k2_xboole_0(X25,X24) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X24,X25))).
% 5.96/1.14  
% 5.96/1.14  cnf(u595,axiom,
% 5.96/1.14      k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X12,X13))).
% 5.96/1.14  
% 5.96/1.14  cnf(u5308,axiom,
% 5.96/1.14      k2_xboole_0(X54,X53) = k2_xboole_0(k4_xboole_0(X54,X53),k2_xboole_0(X53,X54))).
% 5.96/1.14  
% 5.96/1.14  cnf(u1467,axiom,
% 5.96/1.14      k2_xboole_0(X19,X18) = k2_xboole_0(k4_xboole_0(X18,X19),k2_xboole_0(X18,X19))).
% 5.96/1.14  
% 5.96/1.14  cnf(u135,axiom,
% 5.96/1.14      k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8))).
% 5.96/1.14  
% 5.96/1.14  cnf(u871,axiom,
% 5.96/1.14      k2_xboole_0(X1,X2) = k2_xboole_0(k4_xboole_0(X2,X1),X1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u700,axiom,
% 5.96/1.14      k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),X1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u974,axiom,
% 5.96/1.14      k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u4489,axiom,
% 5.96/1.14      k2_xboole_0(X56,X57) = k2_xboole_0(k2_xboole_0(X57,X56),k4_xboole_0(X56,X57))).
% 5.96/1.14  
% 5.96/1.14  cnf(u981,axiom,
% 5.96/1.14      k2_xboole_0(X19,X18) = k2_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X18,X19))).
% 5.96/1.14  
% 5.96/1.14  cnf(u133,axiom,
% 5.96/1.14      k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X6,X5),k2_xboole_0(X5,X6))).
% 5.96/1.14  
% 5.96/1.14  cnf(u2006,axiom,
% 5.96/1.14      k2_xboole_0(X23,X22) = k2_xboole_0(k2_xboole_0(X22,X23),X22)).
% 5.96/1.14  
% 5.96/1.14  cnf(u978,axiom,
% 5.96/1.14      k2_xboole_0(X15,X14) = k2_xboole_0(k2_xboole_0(X14,X15),X15)).
% 5.96/1.14  
% 5.96/1.14  cnf(u291,axiom,
% 5.96/1.14      k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6))).
% 5.96/1.14  
% 5.96/1.14  cnf(u165,axiom,
% 5.96/1.14      k2_xboole_0(X1,X0) = k2_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X0,X1))).
% 5.96/1.14  
% 5.96/1.14  cnf(u169,axiom,
% 5.96/1.14      k2_xboole_0(X5,X6) = k2_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5))).
% 5.96/1.14  
% 5.96/1.14  cnf(u75,axiom,
% 5.96/1.14      k2_xboole_0(X4,X3) = k2_xboole_0(k2_xboole_0(X4,X3),X3)).
% 5.96/1.14  
% 5.96/1.14  cnf(u74,axiom,
% 5.96/1.14      k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)).
% 5.96/1.14  
% 5.96/1.14  cnf(u487,axiom,
% 5.96/1.14      k2_xboole_0(X12,X13) = k2_xboole_0(X13,k4_xboole_0(X12,X13))).
% 5.96/1.14  
% 5.96/1.14  cnf(u1464,axiom,
% 5.96/1.14      k2_xboole_0(X13,X12) = k2_xboole_0(X12,k2_xboole_0(X12,X13))).
% 5.96/1.14  
% 5.96/1.14  cnf(u175,axiom,
% 5.96/1.14      k2_xboole_0(X3,X4) = k2_xboole_0(X4,k2_xboole_0(X3,X4))).
% 5.96/1.14  
% 5.96/1.14  cnf(u37,axiom,
% 5.96/1.14      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 5.96/1.14  
% 5.96/1.14  cnf(u99,axiom,
% 5.96/1.14      k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))).
% 5.96/1.14  
% 5.96/1.14  cnf(u88,axiom,
% 5.96/1.14      k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))).
% 5.96/1.14  
% 5.96/1.14  cnf(u39,axiom,
% 5.96/1.14      k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))).
% 5.96/1.14  
% 5.96/1.14  cnf(u444,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u591,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5) = X5).
% 5.96/1.14  
% 5.96/1.14  cnf(u701,axiom,
% 5.96/1.14      k5_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = X3).
% 5.96/1.14  
% 5.96/1.14  cnf(u381,axiom,
% 5.96/1.14      k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11).
% 5.96/1.14  
% 5.96/1.14  cnf(u4883,axiom,
% 5.96/1.14      k4_subset_1(X0,X0,X0) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u31,axiom,
% 5.96/1.14      k2_subset_1(X0) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u783,axiom,
% 5.96/1.14      k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X12,X11)) = X11).
% 5.96/1.14  
% 5.96/1.14  cnf(u335,axiom,
% 5.96/1.14      k5_xboole_0(X0,k1_xboole_0) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u388,axiom,
% 5.96/1.14      k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5).
% 5.96/1.14  
% 5.96/1.14  cnf(u385,axiom,
% 5.96/1.14      k4_xboole_0(X12,k4_xboole_0(X13,X12)) = X12).
% 5.96/1.14  
% 5.96/1.14  cnf(u33,axiom,
% 5.96/1.14      k4_xboole_0(X0,k1_xboole_0) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u475,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X20,k4_xboole_0(X20,X21)),X20) = X20).
% 5.96/1.14  
% 5.96/1.14  cnf(u479,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X28,X29),X28) = X28).
% 5.96/1.14  
% 5.96/1.14  cnf(u497,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2).
% 5.96/1.14  
% 5.96/1.14  cnf(u463,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2).
% 5.96/1.14  
% 5.96/1.14  cnf(u48,axiom,
% 5.96/1.14      k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u51,axiom,
% 5.96/1.14      k2_xboole_0(k1_xboole_0,X0) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u555,axiom,
% 5.96/1.14      k2_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5))) = X5).
% 5.96/1.14  
% 5.96/1.14  cnf(u471,axiom,
% 5.96/1.14      k2_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X12,X13))) = X12).
% 5.96/1.14  
% 5.96/1.14  cnf(u472,axiom,
% 5.96/1.14      k2_xboole_0(X14,k4_xboole_0(X14,X15)) = X14).
% 5.96/1.14  
% 5.96/1.14  cnf(u76,axiom,
% 5.96/1.14      k2_xboole_0(X5,X5) = X5).
% 5.96/1.14  
% 5.96/1.14  cnf(u32,axiom,
% 5.96/1.14      k2_xboole_0(X0,k1_xboole_0) = X0).
% 5.96/1.14  
% 5.96/1.14  cnf(u29,negated_conjecture,
% 5.96/1.14      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 5.96/1.14  
% 5.96/1.14  % (3070)# SZS output end Saturation.
% 5.96/1.14  % (3070)------------------------------
% 5.96/1.14  % (3070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.96/1.14  % (3070)Termination reason: Satisfiable
% 5.96/1.14  
% 5.96/1.14  % (3070)Memory used [KB]: 10106
% 5.96/1.14  % (3070)Time elapsed: 0.728 s
% 5.96/1.14  % (3070)------------------------------
% 5.96/1.14  % (3070)------------------------------
% 6.23/1.15  % (3153)Refutation not found, incomplete strategy% (3153)------------------------------
% 6.23/1.15  % (3153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.23/1.15  % (3153)Termination reason: Refutation not found, incomplete strategy
% 6.23/1.15  
% 6.23/1.15  % (3153)Memory used [KB]: 6268
% 6.23/1.15  % (3153)Time elapsed: 0.120 s
% 6.23/1.15  % (3153)------------------------------
% 6.23/1.15  % (3153)------------------------------
% 6.23/1.16  % (3063)Success in time 0.8 s
%------------------------------------------------------------------------------
