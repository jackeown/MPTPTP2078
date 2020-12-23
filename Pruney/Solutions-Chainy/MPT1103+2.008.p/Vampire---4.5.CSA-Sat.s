%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:35 EST 2020

% Result     : CounterSatisfiable 1.37s
% Output     : Saturation 1.37s
% Verified   : 
% Statistics : Number of clauses        :  103 ( 103 expanded)
%              Number of leaves         :  103 ( 103 expanded)
%              Depth                    :    0
%              Number of atoms          :  269 ( 269 expanded)
%              Number of equality atoms :  225 ( 225 expanded)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u28,axiom,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) )).

cnf(u56,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u27,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u88,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | r2_hidden(X0,X1) )).

cnf(u43,axiom,
    ( r1_tarski(sK2(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u68,axiom,
    ( r2_hidden(sK2(X2,X3),X3)
    | r2_hidden(sK2(X2,X3),k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) = X3 )).

cnf(u70,axiom,
    ( r2_hidden(sK2(X0,X1),X1)
    | sK2(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,X1)))
    | k1_zfmisc_1(X0) = X1 )).

cnf(u90,axiom,
    ( r2_hidden(sK2(X1,X2),X2)
    | k5_xboole_0(sK2(X1,X2),k7_subset_1(X1,X1,sK2(X1,X2))) = X1
    | k1_zfmisc_1(X1) = X2 )).

cnf(u81,axiom,
    ( r2_hidden(sK2(X2,k1_zfmisc_1(X3)),k1_zfmisc_1(X2))
    | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3)
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u121,axiom,
    ( r2_hidden(sK2(X0,k1_zfmisc_1(X1)),k1_zfmisc_1(X0))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1 )).

cnf(u125,axiom,
    ( r2_hidden(sK2(X2,k1_zfmisc_1(X3)),k1_zfmisc_1(X2))
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3))))
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u68_001,axiom,
    ( r2_hidden(sK2(X2,X3),X3)
    | r2_hidden(sK2(X2,X3),k1_zfmisc_1(X2))
    | k1_zfmisc_1(X2) = X3 )).

cnf(u60,axiom,
    ( r2_hidden(X0,k1_zfmisc_1(X0)) )).

cnf(u59,negated_conjecture,
    ( r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u44,axiom,
    ( ~ r2_hidden(sK2(X0,X1),X1)
    | ~ r1_tarski(sK2(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u53,axiom,
    ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
    | r1_tarski(X2,X0) )).

cnf(u69,axiom,
    ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)
    | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u81_002,axiom,
    ( r2_hidden(sK2(X2,k1_zfmisc_1(X3)),k1_zfmisc_1(X2))
    | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3)
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u110,axiom,
    ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X0,X0,sK2(X0,k1_zfmisc_1(X1)))) = X0 )).

cnf(u117,axiom,
    ( r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3)
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X2,X2,X2,sK2(X2,k1_zfmisc_1(X3))))
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u69_003,axiom,
    ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)
    | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u113,axiom,
    ( r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)
    | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1 )).

cnf(u118,axiom,
    ( r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X2)
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3))))
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u43_004,axiom,
    ( r1_tarski(sK2(X0,X1),X0)
    | r2_hidden(sK2(X0,X1),X1)
    | k1_zfmisc_1(X0) = X1 )).

cnf(u63,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u61,negated_conjecture,
    ( r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u128,axiom,
    ( ~ r1_tarski(sK2(X0,X1),X0)
    | k1_zfmisc_1(X0) = X1
    | sK2(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,X1))) )).

cnf(u54,axiom,
    ( ~ r1_tarski(X2,X0)
    | r2_hidden(X2,k1_zfmisc_1(X0)) )).

cnf(u51,axiom,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 )).

cnf(u89,axiom,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = X1 )).

cnf(u148,axiom,
    ( k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1
    | sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,k1_zfmisc_1(X1))))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u155,axiom,
    ( sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4))))
    | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X3,k1_zfmisc_1(X4))))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u182,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X4,k1_zfmisc_1(X3)),sK2(X4,k1_zfmisc_1(X3)),X3)
    | sK2(X4,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X4,k1_zfmisc_1(X3))))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u177,axiom,
    ( k7_subset_1(X5,X5,sK2(X6,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X6,k1_zfmisc_1(X5)))
    | sK2(X6,k1_zfmisc_1(X5)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X6,k1_zfmisc_1(X5))))
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X6) )).

cnf(u267,axiom,
    ( k5_xboole_0(sK2(X10,k1_zfmisc_1(X9)),k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9)))) = X9
    | sK2(X10,k1_zfmisc_1(X9)) = k1_setfam_1(k2_enumset1(X10,X10,X10,sK2(X10,k1_zfmisc_1(X9))))
    | k1_zfmisc_1(X9) = k1_zfmisc_1(X10) )).

cnf(u143,axiom,
    ( sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4))))
    | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4)))) = X3
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u155_005,axiom,
    ( sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4))))
    | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X3,k1_zfmisc_1(X4))))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u183,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X3)
    | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4))))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u179,axiom,
    ( k7_subset_1(X5,X5,sK2(X5,k1_zfmisc_1(X6))) = k5_xboole_0(X5,sK2(X5,k1_zfmisc_1(X6)))
    | sK2(X5,k1_zfmisc_1(X6)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X5,k1_zfmisc_1(X6))))
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X6) )).

cnf(u305,axiom,
    ( k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3))))
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u286,axiom,
    ( k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3))))
    | k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X3,sK2(X2,k1_zfmisc_1(X3)))) = X3
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u65,negated_conjecture,
    ( sK1 = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0))) )).

cnf(u77,negated_conjecture,
    ( u1_struct_0(sK0) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u66,axiom,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 )).

cnf(u190,axiom,
    ( k7_subset_1(X9,X9,sK2(X10,k1_zfmisc_1(X9))) = k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9)))
    | k1_xboole_0 = k7_subset_1(sK2(X10,k1_zfmisc_1(X9)),sK2(X10,k1_zfmisc_1(X9)),X10)
    | k1_zfmisc_1(X9) = k1_zfmisc_1(X10) )).

cnf(u171,axiom,
    ( k7_subset_1(X2,X2,sK2(X3,k1_zfmisc_1(X2))) = k5_xboole_0(X2,sK2(X3,k1_zfmisc_1(X2)))
    | k5_xboole_0(sK2(X3,k1_zfmisc_1(X2)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X2)))) = X3
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u177_006,axiom,
    ( k7_subset_1(X5,X5,sK2(X6,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X6,k1_zfmisc_1(X5)))
    | sK2(X6,k1_zfmisc_1(X5)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X6,k1_zfmisc_1(X5))))
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X6) )).

cnf(u263,axiom,
    ( k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X11,sK2(X11,k1_zfmisc_1(X12)))
    | k7_subset_1(X12,X12,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X12,sK2(X11,k1_zfmisc_1(X12)))
    | k1_zfmisc_1(X11) = k1_zfmisc_1(X12) )).

cnf(u309,axiom,
    ( k7_subset_1(X15,X15,sK2(X16,k1_zfmisc_1(X15))) = k5_xboole_0(X15,sK2(X16,k1_zfmisc_1(X15)))
    | k5_xboole_0(sK2(X16,k1_zfmisc_1(X15)),k5_xboole_0(X16,sK2(X16,k1_zfmisc_1(X15)))) = X16
    | k1_zfmisc_1(X15) = k1_zfmisc_1(X16) )).

cnf(u185,axiom,
    ( k7_subset_1(X8,X8,sK2(X8,k1_zfmisc_1(X9))) = k5_xboole_0(X8,sK2(X8,k1_zfmisc_1(X9)))
    | k1_xboole_0 = k7_subset_1(sK2(X8,k1_zfmisc_1(X9)),sK2(X8,k1_zfmisc_1(X9)),X9)
    | k1_zfmisc_1(X8) = k1_zfmisc_1(X9) )).

cnf(u174,axiom,
    ( k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4))) = k5_xboole_0(X3,sK2(X3,k1_zfmisc_1(X4)))
    | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X4,X4,sK2(X3,k1_zfmisc_1(X4)))) = X4
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u271,axiom,
    ( k7_subset_1(X13,X13,sK2(X13,k1_zfmisc_1(X14))) = k5_xboole_0(X13,sK2(X13,k1_zfmisc_1(X14)))
    | k5_xboole_0(sK2(X13,k1_zfmisc_1(X14)),k5_xboole_0(X14,sK2(X13,k1_zfmisc_1(X14)))) = X14
    | k1_zfmisc_1(X14) = k1_zfmisc_1(X13) )).

cnf(u179_007,axiom,
    ( k7_subset_1(X5,X5,sK2(X5,k1_zfmisc_1(X6))) = k5_xboole_0(X5,sK2(X5,k1_zfmisc_1(X6)))
    | sK2(X5,k1_zfmisc_1(X6)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X5,k1_zfmisc_1(X6))))
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X6) )).

cnf(u263_008,axiom,
    ( k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X11,sK2(X11,k1_zfmisc_1(X12)))
    | k7_subset_1(X12,X12,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X12,sK2(X11,k1_zfmisc_1(X12)))
    | k1_zfmisc_1(X11) = k1_zfmisc_1(X12) )).

cnf(u97,axiom,
    ( k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )).

cnf(u91,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u29,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u49,axiom,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) )).

cnf(u175,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X1)
    | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) )).

cnf(u186,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X6)
    | k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X7)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(X7) )).

cnf(u183_009,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X3)
    | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4))))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u190_010,axiom,
    ( k7_subset_1(X9,X9,sK2(X10,k1_zfmisc_1(X9))) = k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9)))
    | k1_xboole_0 = k7_subset_1(sK2(X10,k1_zfmisc_1(X9)),sK2(X10,k1_zfmisc_1(X9)),X10)
    | k1_zfmisc_1(X9) = k1_zfmisc_1(X10) )).

cnf(u209,axiom,
    ( k5_xboole_0(sK2(X5,k1_zfmisc_1(X4)),k5_xboole_0(X4,sK2(X5,k1_zfmisc_1(X4)))) = X4
    | k1_xboole_0 = k7_subset_1(sK2(X5,k1_zfmisc_1(X4)),sK2(X5,k1_zfmisc_1(X4)),X5)
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) )).

cnf(u172,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X0)),sK2(X1,k1_zfmisc_1(X0)),X0)
    | k5_xboole_0(sK2(X1,k1_zfmisc_1(X0)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X0)))) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u182_011,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X4,k1_zfmisc_1(X3)),sK2(X4,k1_zfmisc_1(X3)),X3)
    | sK2(X4,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X4,k1_zfmisc_1(X3))))
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u186_012,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X6)
    | k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X7)
    | k1_zfmisc_1(X6) = k1_zfmisc_1(X7) )).

cnf(u185_013,axiom,
    ( k7_subset_1(X8,X8,sK2(X8,k1_zfmisc_1(X9))) = k5_xboole_0(X8,sK2(X8,k1_zfmisc_1(X9)))
    | k1_xboole_0 = k7_subset_1(sK2(X8,k1_zfmisc_1(X9)),sK2(X8,k1_zfmisc_1(X9)),X9)
    | k1_zfmisc_1(X8) = k1_zfmisc_1(X9) )).

cnf(u200,axiom,
    ( k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0
    | k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u101,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0)) )).

cnf(u25,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u102,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u30,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u286_014,axiom,
    ( k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3))))
    | k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X3,sK2(X2,k1_zfmisc_1(X3)))) = X3
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u285,axiom,
    ( k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X4,sK2(X4,k1_zfmisc_1(X5)))) = X4
    | k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5)))) = X5
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)
    | k7_subset_1(X5,X5,sK2(X4,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5))) )).

cnf(u283,axiom,
    ( k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X12,sK2(X12,k1_zfmisc_1(X13)))) = X12
    | k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X13,sK2(X12,k1_zfmisc_1(X13)))) = X13
    | k1_zfmisc_1(X12) = k1_zfmisc_1(X13) )).

cnf(u271_015,axiom,
    ( k7_subset_1(X13,X13,sK2(X13,k1_zfmisc_1(X14))) = k5_xboole_0(X13,sK2(X13,k1_zfmisc_1(X14)))
    | k5_xboole_0(sK2(X13,k1_zfmisc_1(X14)),k5_xboole_0(X14,sK2(X13,k1_zfmisc_1(X14)))) = X14
    | k1_zfmisc_1(X14) = k1_zfmisc_1(X13) )).

cnf(u267_016,axiom,
    ( k5_xboole_0(sK2(X10,k1_zfmisc_1(X9)),k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9)))) = X9
    | sK2(X10,k1_zfmisc_1(X9)) = k1_setfam_1(k2_enumset1(X10,X10,X10,sK2(X10,k1_zfmisc_1(X9))))
    | k1_zfmisc_1(X9) = k1_zfmisc_1(X10) )).

cnf(u220,axiom,
    ( k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k5_xboole_0(X8,sK2(X9,k1_zfmisc_1(X8)))) = X8
    | k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k7_subset_1(X9,X9,sK2(X9,k1_zfmisc_1(X8)))) = X9
    | k1_zfmisc_1(X8) = k1_zfmisc_1(X9)
    | sK2(X9,k1_zfmisc_1(X8)) = k1_setfam_1(k2_enumset1(X9,X9,X9,sK2(X9,k1_zfmisc_1(X8)))) )).

cnf(u219,axiom,
    ( k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k5_xboole_0(X10,sK2(X11,k1_zfmisc_1(X10)))) = X10
    | k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X10)))) = X11
    | k1_zfmisc_1(X10) = k1_zfmisc_1(X11) )).

cnf(u209_017,axiom,
    ( k5_xboole_0(sK2(X5,k1_zfmisc_1(X4)),k5_xboole_0(X4,sK2(X5,k1_zfmisc_1(X4)))) = X4
    | k1_xboole_0 = k7_subset_1(sK2(X5,k1_zfmisc_1(X4)),sK2(X5,k1_zfmisc_1(X4)),X5)
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) )).

cnf(u309_018,axiom,
    ( k7_subset_1(X15,X15,sK2(X16,k1_zfmisc_1(X15))) = k5_xboole_0(X15,sK2(X16,k1_zfmisc_1(X15)))
    | k5_xboole_0(sK2(X16,k1_zfmisc_1(X15)),k5_xboole_0(X16,sK2(X16,k1_zfmisc_1(X15)))) = X16
    | k1_zfmisc_1(X15) = k1_zfmisc_1(X16) )).

cnf(u305_019,axiom,
    ( k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3))))
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u286_020,axiom,
    ( k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2
    | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3))))
    | k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X3,sK2(X2,k1_zfmisc_1(X3)))) = X3
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u285_021,axiom,
    ( k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X4,sK2(X4,k1_zfmisc_1(X5)))) = X4
    | k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5)))) = X5
    | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)
    | k7_subset_1(X5,X5,sK2(X4,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5))) )).

cnf(u283_022,axiom,
    ( k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X12,sK2(X12,k1_zfmisc_1(X13)))) = X12
    | k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X13,sK2(X12,k1_zfmisc_1(X13)))) = X13
    | k1_zfmisc_1(X12) = k1_zfmisc_1(X13) )).

cnf(u243,axiom,
    ( k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0
    | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u200_023,axiom,
    ( k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0
    | k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u139,axiom,
    ( k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X2)))) = X1
    | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) )).

cnf(u148_024,axiom,
    ( k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1
    | sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,k1_zfmisc_1(X1))))
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u175_025,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X1)
    | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) )).

cnf(u174_026,axiom,
    ( k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4))) = k5_xboole_0(X3,sK2(X3,k1_zfmisc_1(X4)))
    | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X4,X4,sK2(X3,k1_zfmisc_1(X4)))) = X4
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u243_027,axiom,
    ( k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0
    | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u139_028,axiom,
    ( k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X2)))) = X1
    | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2
    | k1_zfmisc_1(X1) = k1_zfmisc_1(X2) )).

cnf(u143_029,axiom,
    ( sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4))))
    | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4)))) = X3
    | k1_zfmisc_1(X3) = k1_zfmisc_1(X4) )).

cnf(u172_030,axiom,
    ( k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X0)),sK2(X1,k1_zfmisc_1(X0)),X0)
    | k5_xboole_0(sK2(X1,k1_zfmisc_1(X0)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X0)))) = X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) )).

cnf(u171_031,axiom,
    ( k7_subset_1(X2,X2,sK2(X3,k1_zfmisc_1(X2))) = k5_xboole_0(X2,sK2(X3,k1_zfmisc_1(X2)))
    | k5_xboole_0(sK2(X3,k1_zfmisc_1(X2)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X2)))) = X3
    | k1_zfmisc_1(X2) = k1_zfmisc_1(X3) )).

cnf(u219_032,axiom,
    ( k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k5_xboole_0(X10,sK2(X11,k1_zfmisc_1(X10)))) = X10
    | k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X10)))) = X11
    | k1_zfmisc_1(X10) = k1_zfmisc_1(X11) )).

cnf(u220_033,axiom,
    ( k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k5_xboole_0(X8,sK2(X9,k1_zfmisc_1(X8)))) = X8
    | k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k7_subset_1(X9,X9,sK2(X9,k1_zfmisc_1(X8)))) = X9
    | k1_zfmisc_1(X8) = k1_zfmisc_1(X9)
    | sK2(X9,k1_zfmisc_1(X8)) = k1_setfam_1(k2_enumset1(X9,X9,X9,sK2(X9,k1_zfmisc_1(X8)))) )).

cnf(u106,negated_conjecture,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u87,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u31,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u55,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:50:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (28074)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (28090)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (28066)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (28074)Refutation not found, incomplete strategy% (28074)------------------------------
% 0.21/0.51  % (28074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28074)Memory used [KB]: 10618
% 0.21/0.51  % (28074)Time elapsed: 0.103 s
% 0.21/0.51  % (28074)------------------------------
% 0.21/0.51  % (28074)------------------------------
% 1.25/0.51  % (28075)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.25/0.51  % (28064)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.51  % (28076)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.51  % (28085)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.51  % (28082)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.52  % (28085)Refutation not found, incomplete strategy% (28085)------------------------------
% 1.25/0.52  % (28085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (28085)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (28085)Memory used [KB]: 10746
% 1.25/0.52  % (28085)Time elapsed: 0.080 s
% 1.25/0.52  % (28085)------------------------------
% 1.25/0.52  % (28085)------------------------------
% 1.25/0.52  % (28072)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (28071)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.52  % (28063)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.25/0.52  % (28063)Refutation not found, incomplete strategy% (28063)------------------------------
% 1.25/0.52  % (28063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (28063)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (28063)Memory used [KB]: 1663
% 1.25/0.52  % (28063)Time elapsed: 0.093 s
% 1.25/0.52  % (28063)------------------------------
% 1.25/0.52  % (28063)------------------------------
% 1.25/0.52  % (28092)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.52  % (28065)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.25/0.52  % (28077)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.52  % (28065)Refutation not found, incomplete strategy% (28065)------------------------------
% 1.25/0.52  % (28065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (28065)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (28065)Memory used [KB]: 10746
% 1.25/0.52  % (28065)Time elapsed: 0.117 s
% 1.25/0.52  % (28065)------------------------------
% 1.25/0.52  % (28065)------------------------------
% 1.25/0.53  % (28087)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.53  % (28079)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.53  % (28080)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.53  % (28084)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.25/0.53  % (28080)Refutation not found, incomplete strategy% (28080)------------------------------
% 1.25/0.53  % (28080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (28084)Refutation not found, incomplete strategy% (28084)------------------------------
% 1.25/0.53  % (28084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (28088)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.53  % (28067)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.53  % (28069)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.53  % (28067)Refutation not found, incomplete strategy% (28067)------------------------------
% 1.37/0.53  % (28067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (28088)Refutation not found, incomplete strategy% (28088)------------------------------
% 1.37/0.53  % (28088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (28080)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (28080)Memory used [KB]: 10618
% 1.37/0.53  % (28080)Time elapsed: 0.127 s
% 1.37/0.53  % (28080)------------------------------
% 1.37/0.53  % (28080)------------------------------
% 1.37/0.53  % (28068)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.53  % (28088)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (28088)Memory used [KB]: 6268
% 1.37/0.53  % (28088)Time elapsed: 0.130 s
% 1.37/0.53  % (28088)------------------------------
% 1.37/0.53  % (28088)------------------------------
% 1.37/0.53  % (28075)Refutation not found, incomplete strategy% (28075)------------------------------
% 1.37/0.53  % (28075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (28075)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (28075)Memory used [KB]: 6268
% 1.37/0.53  % (28075)Time elapsed: 0.112 s
% 1.37/0.53  % (28075)------------------------------
% 1.37/0.53  % (28075)------------------------------
% 1.37/0.53  % (28072)Refutation not found, incomplete strategy% (28072)------------------------------
% 1.37/0.53  % (28072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (28072)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (28072)Memory used [KB]: 10618
% 1.37/0.53  % (28072)Time elapsed: 0.129 s
% 1.37/0.53  % (28072)------------------------------
% 1.37/0.53  % (28072)------------------------------
% 1.37/0.53  % (28067)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.53  
% 1.37/0.53  % (28067)Memory used [KB]: 6268
% 1.37/0.53  % (28067)Time elapsed: 0.129 s
% 1.37/0.53  % (28067)------------------------------
% 1.37/0.53  % (28067)------------------------------
% 1.37/0.54  % (28086)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.54  % (28084)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (28084)Memory used [KB]: 1663
% 1.37/0.54  % (28084)Time elapsed: 0.135 s
% 1.37/0.54  % (28084)------------------------------
% 1.37/0.54  % (28084)------------------------------
% 1.37/0.54  % (28089)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.54  % (28071)Refutation not found, incomplete strategy% (28071)------------------------------
% 1.37/0.54  % (28071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (28071)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (28071)Memory used [KB]: 10746
% 1.37/0.54  % (28071)Time elapsed: 0.135 s
% 1.37/0.54  % (28071)------------------------------
% 1.37/0.54  % (28071)------------------------------
% 1.37/0.54  % (28070)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.54  % (28089)Refutation not found, incomplete strategy% (28089)------------------------------
% 1.37/0.54  % (28089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (28089)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (28089)Memory used [KB]: 10746
% 1.37/0.54  % (28089)Time elapsed: 0.141 s
% 1.37/0.54  % (28089)------------------------------
% 1.37/0.54  % (28089)------------------------------
% 1.37/0.54  % (28081)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.55  % (28078)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.55  % (28078)Refutation not found, incomplete strategy% (28078)------------------------------
% 1.37/0.55  % (28078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (28078)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (28078)Memory used [KB]: 6140
% 1.37/0.55  % (28078)Time elapsed: 0.001 s
% 1.37/0.55  % (28078)------------------------------
% 1.37/0.55  % (28078)------------------------------
% 1.37/0.55  % (28091)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (28073)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.55  % (28073)Refutation not found, incomplete strategy% (28073)------------------------------
% 1.37/0.55  % (28073)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (28073)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (28073)Memory used [KB]: 10618
% 1.37/0.55  % (28073)Time elapsed: 0.149 s
% 1.37/0.55  % (28073)------------------------------
% 1.37/0.55  % (28073)------------------------------
% 1.37/0.55  % (28082)Refutation not found, incomplete strategy% (28082)------------------------------
% 1.37/0.55  % (28082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (28082)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (28082)Memory used [KB]: 10874
% 1.37/0.55  % (28082)Time elapsed: 0.126 s
% 1.37/0.55  % (28082)------------------------------
% 1.37/0.55  % (28082)------------------------------
% 1.37/0.55  % (28083)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.56  % (28083)Refutation not found, incomplete strategy% (28083)------------------------------
% 1.37/0.56  % (28083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (28083)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (28083)Memory used [KB]: 10746
% 1.37/0.56  % (28083)Time elapsed: 0.161 s
% 1.37/0.56  % (28083)------------------------------
% 1.37/0.56  % (28083)------------------------------
% 1.37/0.56  % (28066)Refutation not found, incomplete strategy% (28066)------------------------------
% 1.37/0.56  % (28066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (28066)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (28066)Memory used [KB]: 10874
% 1.37/0.56  % (28066)Time elapsed: 0.156 s
% 1.37/0.56  % (28066)------------------------------
% 1.37/0.56  % (28066)------------------------------
% 1.37/0.59  % SZS status CounterSatisfiable for theBenchmark
% 1.37/0.59  % (28069)# SZS output start Saturation.
% 1.37/0.59  cnf(u28,axiom,
% 1.37/0.59      ~v1_xboole_0(k1_zfmisc_1(X0))).
% 1.37/0.59  
% 1.37/0.59  cnf(u56,axiom,
% 1.37/0.59      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.37/0.59  
% 1.37/0.59  cnf(u27,negated_conjecture,
% 1.37/0.59      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.37/0.59  
% 1.37/0.59  cnf(u88,axiom,
% 1.37/0.59      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.37/0.59  
% 1.37/0.59  cnf(u40,axiom,
% 1.37/0.59      ~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u43,axiom,
% 1.37/0.59      r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 1.37/0.59  
% 1.37/0.59  cnf(u68,axiom,
% 1.37/0.59      r2_hidden(sK2(X2,X3),X3) | r2_hidden(sK2(X2,X3),k1_zfmisc_1(X2)) | k1_zfmisc_1(X2) = X3).
% 1.37/0.59  
% 1.37/0.59  cnf(u70,axiom,
% 1.37/0.59      r2_hidden(sK2(X0,X1),X1) | sK2(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,X1))) | k1_zfmisc_1(X0) = X1).
% 1.37/0.59  
% 1.37/0.59  cnf(u90,axiom,
% 1.37/0.59      r2_hidden(sK2(X1,X2),X2) | k5_xboole_0(sK2(X1,X2),k7_subset_1(X1,X1,sK2(X1,X2))) = X1 | k1_zfmisc_1(X1) = X2).
% 1.37/0.59  
% 1.37/0.59  cnf(u81,axiom,
% 1.37/0.59      r2_hidden(sK2(X2,k1_zfmisc_1(X3)),k1_zfmisc_1(X2)) | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u121,axiom,
% 1.37/0.59      r2_hidden(sK2(X0,k1_zfmisc_1(X1)),k1_zfmisc_1(X0)) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1).
% 1.37/0.59  
% 1.37/0.59  cnf(u125,axiom,
% 1.37/0.59      r2_hidden(sK2(X2,k1_zfmisc_1(X3)),k1_zfmisc_1(X2)) | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3)))) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u68,axiom,
% 1.37/0.59      r2_hidden(sK2(X2,X3),X3) | r2_hidden(sK2(X2,X3),k1_zfmisc_1(X2)) | k1_zfmisc_1(X2) = X3).
% 1.37/0.59  
% 1.37/0.59  cnf(u60,axiom,
% 1.37/0.59      r2_hidden(X0,k1_zfmisc_1(X0))).
% 1.37/0.59  
% 1.37/0.59  cnf(u59,negated_conjecture,
% 1.37/0.59      r2_hidden(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.37/0.59  
% 1.37/0.59  cnf(u44,axiom,
% 1.37/0.59      ~r2_hidden(sK2(X0,X1),X1) | ~r1_tarski(sK2(X0,X1),X0) | k1_zfmisc_1(X0) = X1).
% 1.37/0.59  
% 1.37/0.59  cnf(u53,axiom,
% 1.37/0.59      ~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)).
% 1.37/0.59  
% 1.37/0.59  cnf(u69,axiom,
% 1.37/0.59      r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u81,axiom,
% 1.37/0.59      r2_hidden(sK2(X2,k1_zfmisc_1(X3)),k1_zfmisc_1(X2)) | r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u110,axiom,
% 1.37/0.59      r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X0,X0,sK2(X0,k1_zfmisc_1(X1)))) = X0).
% 1.37/0.59  
% 1.37/0.59  cnf(u117,axiom,
% 1.37/0.59      r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X3) | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X2,X2,X2,sK2(X2,k1_zfmisc_1(X3)))) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u69,axiom,
% 1.37/0.59      r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) | r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u113,axiom,
% 1.37/0.59      r1_tarski(sK2(X0,k1_zfmisc_1(X1)),X0) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1).
% 1.37/0.59  
% 1.37/0.59  cnf(u118,axiom,
% 1.37/0.59      r1_tarski(sK2(X2,k1_zfmisc_1(X3)),X2) | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3)))) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u43,axiom,
% 1.37/0.59      r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1) | k1_zfmisc_1(X0) = X1).
% 1.37/0.59  
% 1.37/0.59  cnf(u63,axiom,
% 1.37/0.59      r1_tarski(X0,X0)).
% 1.37/0.59  
% 1.37/0.59  cnf(u61,negated_conjecture,
% 1.37/0.59      r1_tarski(sK1,u1_struct_0(sK0))).
% 1.37/0.59  
% 1.37/0.59  cnf(u128,axiom,
% 1.37/0.59      ~r1_tarski(sK2(X0,X1),X0) | k1_zfmisc_1(X0) = X1 | sK2(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,X1)))).
% 1.37/0.59  
% 1.37/0.59  cnf(u54,axiom,
% 1.37/0.59      ~r1_tarski(X2,X0) | r2_hidden(X2,k1_zfmisc_1(X0))).
% 1.37/0.59  
% 1.37/0.59  cnf(u51,axiom,
% 1.37/0.59      ~r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0).
% 1.37/0.59  
% 1.37/0.59  cnf(u89,axiom,
% 1.37/0.59      ~r1_tarski(X0,X1) | k5_xboole_0(X0,k7_subset_1(X1,X1,X0)) = X1).
% 1.37/0.59  
% 1.37/0.59  cnf(u148,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1 | sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,k1_zfmisc_1(X1)))) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u155,axiom,
% 1.37/0.59      sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4)))) | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X3,k1_zfmisc_1(X4)))) | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u182,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X4,k1_zfmisc_1(X3)),sK2(X4,k1_zfmisc_1(X3)),X3) | sK2(X4,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X4,k1_zfmisc_1(X3)))) | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u177,axiom,
% 1.37/0.59      k7_subset_1(X5,X5,sK2(X6,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X6,k1_zfmisc_1(X5))) | sK2(X6,k1_zfmisc_1(X5)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X6,k1_zfmisc_1(X5)))) | k1_zfmisc_1(X5) = k1_zfmisc_1(X6)).
% 1.37/0.59  
% 1.37/0.59  cnf(u267,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X10,k1_zfmisc_1(X9)),k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9)))) = X9 | sK2(X10,k1_zfmisc_1(X9)) = k1_setfam_1(k2_enumset1(X10,X10,X10,sK2(X10,k1_zfmisc_1(X9)))) | k1_zfmisc_1(X9) = k1_zfmisc_1(X10)).
% 1.37/0.59  
% 1.37/0.59  cnf(u143,axiom,
% 1.37/0.59      sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4)))) | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4)))) = X3 | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u155,axiom,
% 1.37/0.59      sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4)))) | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X3,k1_zfmisc_1(X4)))) | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u183,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X3) | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4)))) | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u179,axiom,
% 1.37/0.59      k7_subset_1(X5,X5,sK2(X5,k1_zfmisc_1(X6))) = k5_xboole_0(X5,sK2(X5,k1_zfmisc_1(X6))) | sK2(X5,k1_zfmisc_1(X6)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X5,k1_zfmisc_1(X6)))) | k1_zfmisc_1(X5) = k1_zfmisc_1(X6)).
% 1.37/0.59  
% 1.37/0.59  cnf(u305,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2 | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3)))) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u286,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2 | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3)))) | k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X3,sK2(X2,k1_zfmisc_1(X3)))) = X3 | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u65,negated_conjecture,
% 1.37/0.59      sK1 = k1_setfam_1(k2_enumset1(sK1,sK1,sK1,u1_struct_0(sK0)))).
% 1.37/0.59  
% 1.37/0.59  cnf(u77,negated_conjecture,
% 1.37/0.59      u1_struct_0(sK0) = k5_xboole_0(sK1,k5_xboole_0(u1_struct_0(sK0),sK1))).
% 1.37/0.59  
% 1.37/0.59  cnf(u66,axiom,
% 1.37/0.59      k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0).
% 1.37/0.59  
% 1.37/0.59  cnf(u190,axiom,
% 1.37/0.59      k7_subset_1(X9,X9,sK2(X10,k1_zfmisc_1(X9))) = k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9))) | k1_xboole_0 = k7_subset_1(sK2(X10,k1_zfmisc_1(X9)),sK2(X10,k1_zfmisc_1(X9)),X10) | k1_zfmisc_1(X9) = k1_zfmisc_1(X10)).
% 1.37/0.59  
% 1.37/0.59  cnf(u171,axiom,
% 1.37/0.59      k7_subset_1(X2,X2,sK2(X3,k1_zfmisc_1(X2))) = k5_xboole_0(X2,sK2(X3,k1_zfmisc_1(X2))) | k5_xboole_0(sK2(X3,k1_zfmisc_1(X2)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X2)))) = X3 | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u177,axiom,
% 1.37/0.59      k7_subset_1(X5,X5,sK2(X6,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X6,k1_zfmisc_1(X5))) | sK2(X6,k1_zfmisc_1(X5)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X6,k1_zfmisc_1(X5)))) | k1_zfmisc_1(X5) = k1_zfmisc_1(X6)).
% 1.37/0.59  
% 1.37/0.59  cnf(u263,axiom,
% 1.37/0.59      k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X11,sK2(X11,k1_zfmisc_1(X12))) | k7_subset_1(X12,X12,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X12,sK2(X11,k1_zfmisc_1(X12))) | k1_zfmisc_1(X11) = k1_zfmisc_1(X12)).
% 1.37/0.59  
% 1.37/0.59  cnf(u309,axiom,
% 1.37/0.59      k7_subset_1(X15,X15,sK2(X16,k1_zfmisc_1(X15))) = k5_xboole_0(X15,sK2(X16,k1_zfmisc_1(X15))) | k5_xboole_0(sK2(X16,k1_zfmisc_1(X15)),k5_xboole_0(X16,sK2(X16,k1_zfmisc_1(X15)))) = X16 | k1_zfmisc_1(X15) = k1_zfmisc_1(X16)).
% 1.37/0.59  
% 1.37/0.59  cnf(u185,axiom,
% 1.37/0.59      k7_subset_1(X8,X8,sK2(X8,k1_zfmisc_1(X9))) = k5_xboole_0(X8,sK2(X8,k1_zfmisc_1(X9))) | k1_xboole_0 = k7_subset_1(sK2(X8,k1_zfmisc_1(X9)),sK2(X8,k1_zfmisc_1(X9)),X9) | k1_zfmisc_1(X8) = k1_zfmisc_1(X9)).
% 1.37/0.59  
% 1.37/0.59  cnf(u174,axiom,
% 1.37/0.59      k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4))) = k5_xboole_0(X3,sK2(X3,k1_zfmisc_1(X4))) | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X4,X4,sK2(X3,k1_zfmisc_1(X4)))) = X4 | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u271,axiom,
% 1.37/0.59      k7_subset_1(X13,X13,sK2(X13,k1_zfmisc_1(X14))) = k5_xboole_0(X13,sK2(X13,k1_zfmisc_1(X14))) | k5_xboole_0(sK2(X13,k1_zfmisc_1(X14)),k5_xboole_0(X14,sK2(X13,k1_zfmisc_1(X14)))) = X14 | k1_zfmisc_1(X14) = k1_zfmisc_1(X13)).
% 1.37/0.59  
% 1.37/0.59  cnf(u179,axiom,
% 1.37/0.59      k7_subset_1(X5,X5,sK2(X5,k1_zfmisc_1(X6))) = k5_xboole_0(X5,sK2(X5,k1_zfmisc_1(X6))) | sK2(X5,k1_zfmisc_1(X6)) = k1_setfam_1(k2_enumset1(X6,X6,X6,sK2(X5,k1_zfmisc_1(X6)))) | k1_zfmisc_1(X5) = k1_zfmisc_1(X6)).
% 1.37/0.59  
% 1.37/0.59  cnf(u263,axiom,
% 1.37/0.59      k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X11,sK2(X11,k1_zfmisc_1(X12))) | k7_subset_1(X12,X12,sK2(X11,k1_zfmisc_1(X12))) = k5_xboole_0(X12,sK2(X11,k1_zfmisc_1(X12))) | k1_zfmisc_1(X11) = k1_zfmisc_1(X12)).
% 1.37/0.59  
% 1.37/0.59  cnf(u97,axiom,
% 1.37/0.59      k7_subset_1(X0,X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))).
% 1.37/0.59  
% 1.37/0.59  cnf(u91,negated_conjecture,
% 1.37/0.59      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.37/0.59  
% 1.37/0.59  cnf(u29,axiom,
% 1.37/0.59      k2_subset_1(X0) = X0).
% 1.37/0.59  
% 1.37/0.59  cnf(u49,axiom,
% 1.37/0.59      k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)).
% 1.37/0.59  
% 1.37/0.59  cnf(u175,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X1) | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2 | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)).
% 1.37/0.59  
% 1.37/0.59  cnf(u186,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X6) | k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X7) | k1_zfmisc_1(X6) = k1_zfmisc_1(X7)).
% 1.37/0.59  
% 1.37/0.59  cnf(u183,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X3,k1_zfmisc_1(X4)),sK2(X3,k1_zfmisc_1(X4)),X3) | sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4)))) | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u190,axiom,
% 1.37/0.59      k7_subset_1(X9,X9,sK2(X10,k1_zfmisc_1(X9))) = k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9))) | k1_xboole_0 = k7_subset_1(sK2(X10,k1_zfmisc_1(X9)),sK2(X10,k1_zfmisc_1(X9)),X10) | k1_zfmisc_1(X9) = k1_zfmisc_1(X10)).
% 1.37/0.59  
% 1.37/0.59  cnf(u209,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X5,k1_zfmisc_1(X4)),k5_xboole_0(X4,sK2(X5,k1_zfmisc_1(X4)))) = X4 | k1_xboole_0 = k7_subset_1(sK2(X5,k1_zfmisc_1(X4)),sK2(X5,k1_zfmisc_1(X4)),X5) | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u172,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X0)),sK2(X1,k1_zfmisc_1(X0)),X0) | k5_xboole_0(sK2(X1,k1_zfmisc_1(X0)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X0)))) = X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u182,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X4,k1_zfmisc_1(X3)),sK2(X4,k1_zfmisc_1(X3)),X3) | sK2(X4,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X4,k1_zfmisc_1(X3)))) | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u186,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X6) | k1_xboole_0 = k7_subset_1(sK2(X6,k1_zfmisc_1(X7)),sK2(X6,k1_zfmisc_1(X7)),X7) | k1_zfmisc_1(X6) = k1_zfmisc_1(X7)).
% 1.37/0.59  
% 1.37/0.59  cnf(u185,axiom,
% 1.37/0.59      k7_subset_1(X8,X8,sK2(X8,k1_zfmisc_1(X9))) = k5_xboole_0(X8,sK2(X8,k1_zfmisc_1(X9))) | k1_xboole_0 = k7_subset_1(sK2(X8,k1_zfmisc_1(X9)),sK2(X8,k1_zfmisc_1(X9)),X9) | k1_zfmisc_1(X8) = k1_zfmisc_1(X9)).
% 1.37/0.59  
% 1.37/0.59  cnf(u200,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0 | k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u101,negated_conjecture,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK1,sK1,u1_struct_0(sK0))).
% 1.37/0.59  
% 1.37/0.59  cnf(u25,negated_conjecture,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.37/0.59  
% 1.37/0.59  cnf(u102,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 1.37/0.59  
% 1.37/0.59  cnf(u30,axiom,
% 1.37/0.59      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 1.37/0.59  
% 1.37/0.59  cnf(u286,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2 | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3)))) | k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X3,sK2(X2,k1_zfmisc_1(X3)))) = X3 | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u285,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X4,sK2(X4,k1_zfmisc_1(X5)))) = X4 | k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5)))) = X5 | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) | k7_subset_1(X5,X5,sK2(X4,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5)))).
% 1.37/0.59  
% 1.37/0.59  cnf(u283,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X12,sK2(X12,k1_zfmisc_1(X13)))) = X12 | k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X13,sK2(X12,k1_zfmisc_1(X13)))) = X13 | k1_zfmisc_1(X12) = k1_zfmisc_1(X13)).
% 1.37/0.59  
% 1.37/0.59  cnf(u271,axiom,
% 1.37/0.59      k7_subset_1(X13,X13,sK2(X13,k1_zfmisc_1(X14))) = k5_xboole_0(X13,sK2(X13,k1_zfmisc_1(X14))) | k5_xboole_0(sK2(X13,k1_zfmisc_1(X14)),k5_xboole_0(X14,sK2(X13,k1_zfmisc_1(X14)))) = X14 | k1_zfmisc_1(X14) = k1_zfmisc_1(X13)).
% 1.37/0.59  
% 1.37/0.59  cnf(u267,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X10,k1_zfmisc_1(X9)),k5_xboole_0(X9,sK2(X10,k1_zfmisc_1(X9)))) = X9 | sK2(X10,k1_zfmisc_1(X9)) = k1_setfam_1(k2_enumset1(X10,X10,X10,sK2(X10,k1_zfmisc_1(X9)))) | k1_zfmisc_1(X9) = k1_zfmisc_1(X10)).
% 1.37/0.59  
% 1.37/0.59  cnf(u220,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k5_xboole_0(X8,sK2(X9,k1_zfmisc_1(X8)))) = X8 | k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k7_subset_1(X9,X9,sK2(X9,k1_zfmisc_1(X8)))) = X9 | k1_zfmisc_1(X8) = k1_zfmisc_1(X9) | sK2(X9,k1_zfmisc_1(X8)) = k1_setfam_1(k2_enumset1(X9,X9,X9,sK2(X9,k1_zfmisc_1(X8))))).
% 1.37/0.59  
% 1.37/0.59  cnf(u219,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k5_xboole_0(X10,sK2(X11,k1_zfmisc_1(X10)))) = X10 | k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X10)))) = X11 | k1_zfmisc_1(X10) = k1_zfmisc_1(X11)).
% 1.37/0.59  
% 1.37/0.59  cnf(u209,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X5,k1_zfmisc_1(X4)),k5_xboole_0(X4,sK2(X5,k1_zfmisc_1(X4)))) = X4 | k1_xboole_0 = k7_subset_1(sK2(X5,k1_zfmisc_1(X4)),sK2(X5,k1_zfmisc_1(X4)),X5) | k1_zfmisc_1(X5) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u309,axiom,
% 1.37/0.59      k7_subset_1(X15,X15,sK2(X16,k1_zfmisc_1(X15))) = k5_xboole_0(X15,sK2(X16,k1_zfmisc_1(X15))) | k5_xboole_0(sK2(X16,k1_zfmisc_1(X15)),k5_xboole_0(X16,sK2(X16,k1_zfmisc_1(X15)))) = X16 | k1_zfmisc_1(X15) = k1_zfmisc_1(X16)).
% 1.37/0.59  
% 1.37/0.59  cnf(u305,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2 | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3)))) | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u286,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X2,sK2(X2,k1_zfmisc_1(X3)))) = X2 | sK2(X2,k1_zfmisc_1(X3)) = k1_setfam_1(k2_enumset1(X3,X3,X3,sK2(X2,k1_zfmisc_1(X3)))) | k5_xboole_0(sK2(X2,k1_zfmisc_1(X3)),k5_xboole_0(X3,sK2(X2,k1_zfmisc_1(X3)))) = X3 | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u285,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X4,sK2(X4,k1_zfmisc_1(X5)))) = X4 | k5_xboole_0(sK2(X4,k1_zfmisc_1(X5)),k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5)))) = X5 | k1_zfmisc_1(X5) = k1_zfmisc_1(X4) | k7_subset_1(X5,X5,sK2(X4,k1_zfmisc_1(X5))) = k5_xboole_0(X5,sK2(X4,k1_zfmisc_1(X5)))).
% 1.37/0.59  
% 1.37/0.59  cnf(u283,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X12,sK2(X12,k1_zfmisc_1(X13)))) = X12 | k5_xboole_0(sK2(X12,k1_zfmisc_1(X13)),k5_xboole_0(X13,sK2(X12,k1_zfmisc_1(X13)))) = X13 | k1_zfmisc_1(X12) = k1_zfmisc_1(X13)).
% 1.37/0.59  
% 1.37/0.59  cnf(u243,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0 | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u200,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0 | k1_xboole_0 = k7_subset_1(sK2(X0,k1_zfmisc_1(X1)),sK2(X0,k1_zfmisc_1(X1)),X1) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u139,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X2)))) = X1 | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2 | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)).
% 1.37/0.59  
% 1.37/0.59  cnf(u148,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1 | sK2(X0,k1_zfmisc_1(X1)) = k1_setfam_1(k2_enumset1(X0,X0,X0,sK2(X0,k1_zfmisc_1(X1)))) | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u175,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X2)),sK2(X1,k1_zfmisc_1(X2)),X1) | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2 | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)).
% 1.37/0.59  
% 1.37/0.59  cnf(u174,axiom,
% 1.37/0.59      k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4))) = k5_xboole_0(X3,sK2(X3,k1_zfmisc_1(X4))) | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X4,X4,sK2(X3,k1_zfmisc_1(X4)))) = X4 | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u243,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k5_xboole_0(X0,sK2(X0,k1_zfmisc_1(X1)))) = X0 | k5_xboole_0(sK2(X0,k1_zfmisc_1(X1)),k7_subset_1(X1,X1,sK2(X0,k1_zfmisc_1(X1)))) = X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u139,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X2)))) = X1 | k5_xboole_0(sK2(X1,k1_zfmisc_1(X2)),k7_subset_1(X2,X2,sK2(X1,k1_zfmisc_1(X2)))) = X2 | k1_zfmisc_1(X1) = k1_zfmisc_1(X2)).
% 1.37/0.59  
% 1.37/0.59  cnf(u143,axiom,
% 1.37/0.59      sK2(X3,k1_zfmisc_1(X4)) = k1_setfam_1(k2_enumset1(X4,X4,X4,sK2(X3,k1_zfmisc_1(X4)))) | k5_xboole_0(sK2(X3,k1_zfmisc_1(X4)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X4)))) = X3 | k1_zfmisc_1(X3) = k1_zfmisc_1(X4)).
% 1.37/0.59  
% 1.37/0.59  cnf(u172,axiom,
% 1.37/0.59      k1_xboole_0 = k7_subset_1(sK2(X1,k1_zfmisc_1(X0)),sK2(X1,k1_zfmisc_1(X0)),X0) | k5_xboole_0(sK2(X1,k1_zfmisc_1(X0)),k7_subset_1(X1,X1,sK2(X1,k1_zfmisc_1(X0)))) = X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u171,axiom,
% 1.37/0.59      k7_subset_1(X2,X2,sK2(X3,k1_zfmisc_1(X2))) = k5_xboole_0(X2,sK2(X3,k1_zfmisc_1(X2))) | k5_xboole_0(sK2(X3,k1_zfmisc_1(X2)),k7_subset_1(X3,X3,sK2(X3,k1_zfmisc_1(X2)))) = X3 | k1_zfmisc_1(X2) = k1_zfmisc_1(X3)).
% 1.37/0.59  
% 1.37/0.59  cnf(u219,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k5_xboole_0(X10,sK2(X11,k1_zfmisc_1(X10)))) = X10 | k5_xboole_0(sK2(X11,k1_zfmisc_1(X10)),k7_subset_1(X11,X11,sK2(X11,k1_zfmisc_1(X10)))) = X11 | k1_zfmisc_1(X10) = k1_zfmisc_1(X11)).
% 1.37/0.59  
% 1.37/0.59  cnf(u220,axiom,
% 1.37/0.59      k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k5_xboole_0(X8,sK2(X9,k1_zfmisc_1(X8)))) = X8 | k5_xboole_0(sK2(X9,k1_zfmisc_1(X8)),k7_subset_1(X9,X9,sK2(X9,k1_zfmisc_1(X8)))) = X9 | k1_zfmisc_1(X8) = k1_zfmisc_1(X9) | sK2(X9,k1_zfmisc_1(X8)) = k1_setfam_1(k2_enumset1(X9,X9,X9,sK2(X9,k1_zfmisc_1(X8))))).
% 1.37/0.59  
% 1.37/0.59  cnf(u106,negated_conjecture,
% 1.37/0.59      k5_xboole_0(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 1.37/0.59  
% 1.37/0.59  cnf(u87,axiom,
% 1.37/0.59      k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_subset_1(X1,X1,X2)).
% 1.37/0.59  
% 1.37/0.59  cnf(u31,axiom,
% 1.37/0.59      k5_xboole_0(X0,k1_xboole_0) = X0).
% 1.37/0.59  
% 1.37/0.59  cnf(u55,negated_conjecture,
% 1.37/0.59      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.37/0.59  
% 1.37/0.59  % (28069)# SZS output end Saturation.
% 1.37/0.59  % (28069)------------------------------
% 1.37/0.59  % (28069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.59  % (28069)Termination reason: Satisfiable
% 1.37/0.59  
% 1.37/0.59  % (28069)Memory used [KB]: 6396
% 1.37/0.59  % (28069)Time elapsed: 0.156 s
% 1.37/0.59  % (28069)------------------------------
% 1.37/0.59  % (28069)------------------------------
% 1.37/0.59  % (28062)Success in time 0.224 s
%------------------------------------------------------------------------------
