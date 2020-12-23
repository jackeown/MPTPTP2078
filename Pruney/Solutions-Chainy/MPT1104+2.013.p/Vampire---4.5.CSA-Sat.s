%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:52 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :  206 ( 206 expanded)
%              Number of leaves         :  206 ( 206 expanded)
%              Depth                    :    0
%              Number of atoms          :  355 ( 355 expanded)
%              Number of equality atoms :  152 ( 152 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u82,axiom,
    ( m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0)) )).

cnf(u65,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u81,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u80,negated_conjecture,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u39,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u141,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_xboole_0(X1,sK2) )).

cnf(u140,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ r1_xboole_0(X0,sK2) )).

cnf(u135,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK2)) = k2_xboole_0(X3,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u125,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(X2,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u124,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X1,sK2) = k2_xboole_0(X1,sK2) )).

cnf(u123,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1) )).

cnf(u121,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X2,k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_xboole_0(X2,sK1) )).

cnf(u120,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,sK2)
    | r1_xboole_0(X1,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u119,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,sK1)
    | r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u113,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X2,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ r1_xboole_0(X2,sK1) )).

cnf(u112,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X1,sK2)
    | ~ r1_xboole_0(X1,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u111,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,sK1)
    | ~ r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u199,axiom,
    ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
    | ~ r1_tarski(X5,k4_xboole_0(X6,X6))
    | r1_xboole_0(X5,X6) )).

cnf(u198,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | r1_tarski(X3,k4_xboole_0(X4,X4))
    | ~ r1_xboole_0(X3,X4) )).

cnf(u187,axiom,
    ( ~ m1_subset_1(X10,k1_zfmisc_1(X9))
    | k4_subset_1(X9,X10,k4_xboole_0(X9,X9)) = k2_xboole_0(X10,k4_xboole_0(X9,X9)) )).

cnf(u126,axiom,
    ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
    | k4_subset_1(X3,X4,X3) = k2_xboole_0(X4,X3) )).

cnf(u122,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | ~ r1_tarski(X3,X4)
    | r1_xboole_0(X3,k4_xboole_0(X4,X4)) )).

cnf(u114,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(X4))
    | r1_tarski(X3,X4)
    | ~ r1_xboole_0(X3,k4_xboole_0(X4,X4)) )).

cnf(u66,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 )).

cnf(u61,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u60,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u56,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X2)
    | r1_xboole_0(X1,k3_subset_1(X0,X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
    | r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )).

cnf(u53,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u52,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )).

cnf(u51,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) )).

cnf(u276,negated_conjecture,
    ( r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u263,negated_conjecture,
    ( r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u63,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u324,negated_conjecture,
    ( ~ r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u278,negated_conjecture,
    ( ~ r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_xboole_0(sK2,sK2) )).

cnf(u228,negated_conjecture,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u155,negated_conjecture,
    ( ~ r1_tarski(sK2,sK1)
    | r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u323,negated_conjecture,
    ( ~ r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u264,negated_conjecture,
    ( ~ r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_xboole_0(sK1,sK1) )).

cnf(u227,negated_conjecture,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u160,negated_conjecture,
    ( ~ r1_tarski(sK1,sK2)
    | r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u281,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u268,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u164,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK2)
    | r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u158,negated_conjecture,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u232,axiom,
    ( ~ r1_tarski(k4_xboole_0(X1,X1),X1)
    | r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) )).

cnf(u191,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2)
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u163,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK2)
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u162,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK2)
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u283,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK2)
    | sK2 = k4_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u192,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1)
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u157,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK1)
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u284,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK1)
    | sK1 = k4_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u156,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u230,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u229,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u282,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2) )).

cnf(u269,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) )).

cnf(u325,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u279,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK2) )).

cnf(u326,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u267,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK1) )).

cnf(u327,axiom,
    ( ~ r1_tarski(X0,k4_xboole_0(X0,X0))
    | r1_xboole_0(X0,X0) )).

cnf(u59,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u165,negated_conjecture,
    ( r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u67,negated_conjecture,
    ( r1_xboole_0(sK2,sK1) )).

cnf(u159,negated_conjecture,
    ( r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u42,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u305,axiom,
    ( r1_xboole_0(k4_xboole_0(X2,X2),X2) )).

cnf(u245,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) )).

cnf(u202,negated_conjecture,
    ( r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) )).

cnf(u233,axiom,
    ( r1_xboole_0(X0,k4_xboole_0(X0,X0)) )).

cnf(u318,negated_conjecture,
    ( ~ r1_xboole_0(sK2,u1_struct_0(sK0))
    | r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u271,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK2)
    | r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u222,negated_conjecture,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) )).

cnf(u145,negated_conjecture,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_tarski(sK2,sK1) )).

cnf(u317,negated_conjecture,
    ( ~ r1_xboole_0(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u257,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK1)
    | r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u221,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) )).

cnf(u149,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_tarski(sK1,sK2) )).

cnf(u274,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),sK2)
    | r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u261,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),sK1)
    | r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u153,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_tarski(u1_struct_0(sK0),sK2) )).

cnf(u148,negated_conjecture,
    ( ~ r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_tarski(u1_struct_0(sK0),sK1) )).

cnf(u275,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2)
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u272,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK2)
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u262,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1)
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u260,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK1)
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u320,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u319,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u226,axiom,
    ( ~ r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))
    | r1_tarski(k4_xboole_0(X1,X1),X1) )).

cnf(u224,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) )).

cnf(u223,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )).

cnf(u193,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2) )).

cnf(u152,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) )).

cnf(u151,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK2) )).

cnf(u194,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) )).

cnf(u147,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK1) )).

cnf(u146,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))
    | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) )).

cnf(u178,negated_conjecture,
    ( ~ r1_xboole_0(X0,sK2)
    | k2_struct_0(sK0) != k2_xboole_0(X0,sK2)
    | sK1 = X0 )).

cnf(u253,negated_conjecture,
    ( ~ r1_xboole_0(X0,sK2)
    | k4_xboole_0(u1_struct_0(sK0),sK2) = X0
    | u1_struct_0(sK0) != k2_xboole_0(X0,sK2) )).

cnf(u220,negated_conjecture,
    ( ~ r1_xboole_0(X1,sK1)
    | sK2 = X1
    | k2_struct_0(sK0) != k2_xboole_0(X1,sK1) )).

cnf(u248,negated_conjecture,
    ( ~ r1_xboole_0(X0,sK1)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = X0
    | u1_struct_0(sK0) != k2_xboole_0(X0,sK1) )).

cnf(u306,axiom,
    ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X1))
    | X0 = X1
    | k2_xboole_0(X0,k4_xboole_0(X1,X1)) != X1 )).

cnf(u302,negated_conjecture,
    ( ~ r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK2))
    | sK2 = X0
    | u1_struct_0(sK0) != k2_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u292,negated_conjecture,
    ( ~ r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | sK1 = X0
    | u1_struct_0(sK0) != k2_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u50,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) )).

cnf(u62,axiom,
    ( ~ r1_xboole_0(X2,X1)
    | X0 = X2
    | ~ r1_xboole_0(X0,X1)
    | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) )).

cnf(u350,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X1,X1) = X0
    | k2_xboole_0(X0,X1) != X1 )).

cnf(u321,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | r1_tarski(X0,k4_xboole_0(X0,X0)) )).

cnf(u138,negated_conjecture,
    ( sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u87,negated_conjecture,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u97,negated_conjecture,
    ( sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u86,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u177,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u219,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

cnf(u41,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u301,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u291,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u179,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) )).

cnf(u171,negated_conjecture,
    ( u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) )).

cnf(u142,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),sK2) )).

cnf(u105,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK1) )).

cnf(u104,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u103,negated_conjecture,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u186,axiom,
    ( k7_subset_1(X7,k4_xboole_0(X7,X7),X8) = k4_xboole_0(k4_xboole_0(X7,X7),X8) )).

cnf(u134,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X2) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),X2) )).

cnf(u92,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0) )).

cnf(u89,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u238,axiom,
    ( k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) )).

cnf(u173,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u166,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u216,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u215,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u214,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u213,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u212,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u211,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),sK1) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u241,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) = k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u240,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u303,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u298,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

% (15340)Refutation not found, incomplete strategy% (15340)------------------------------
% (15340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
cnf(u294,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u293,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u287,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u200,axiom,
    ( k4_subset_1(X11,k4_xboole_0(X11,X11),X11) = X11 )).

cnf(u106,axiom,
    ( k4_subset_1(X0,X0,k4_xboole_0(X0,X0)) = X0 )).

cnf(u88,axiom,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 )).

cnf(u79,axiom,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) )).

cnf(u78,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u77,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u44,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u46,axiom,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

cnf(u334,axiom,
    ( k4_subset_1(X1,k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) )).

cnf(u330,negated_conjecture,
    ( k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u286,negated_conjecture,
    ( k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u329,negated_conjecture,
    ( k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u295,negated_conjecture,
    ( k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u299,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u289,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u332,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u331,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u297,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u235,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

cnf(u234,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

cnf(u71,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0)) )).

cnf(u48,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) )).

cnf(u209,axiom,
    ( k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) )).

cnf(u243,axiom,
    ( k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 )).

cnf(u205,axiom,
    ( k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) )).

cnf(u69,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) )).

cnf(u47,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u196,axiom,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 )).

cnf(u91,axiom,
    ( k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3) )).

cnf(u90,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1) )).

cnf(u307,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) )).

cnf(u49,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u399,negated_conjecture,
    ( sK2 != k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2))
    | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2) )).

cnf(u373,negated_conjecture,
    ( sK2 != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2)
    | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2) )).

cnf(u375,negated_conjecture,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | sK1 = k4_xboole_0(sK2,sK2) )).

cnf(u389,negated_conjecture,
    ( sK1 != u1_struct_0(sK0)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1) )).

cnf(u396,negated_conjecture,
    ( sK1 != k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1) )).

cnf(u385,negated_conjecture,
    ( sK1 != k2_xboole_0(sK1,sK2)
    | sK2 = k4_xboole_0(sK1,sK1) )).

cnf(u372,negated_conjecture,
    ( sK1 != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1) )).

cnf(u377,negated_conjecture,
    ( sK1 != k2_xboole_0(sK2,sK1)
    | sK2 = k4_xboole_0(sK1,sK1) )).

cnf(u357,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | sK2 = k4_xboole_0(sK1,sK1) )).

cnf(u361,negated_conjecture,
    ( k2_struct_0(sK0) != sK2
    | sK1 = k4_xboole_0(sK2,sK2) )).

cnf(u348,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK2,sK2),sK2)
    | sK1 = k4_xboole_0(sK2,sK2) )).

cnf(u347,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK1,sK1),sK1)
    | sK2 = k4_xboole_0(sK1,sK1) )).

cnf(u393,negated_conjecture,
    ( u1_struct_0(sK0) != sK2
    | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2) )).

cnf(u252,negated_conjecture,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | sK1 = k4_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u256,negated_conjecture,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | sK2 = k4_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u364,negated_conjecture,
    ( u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK2,sK2),sK2)
    | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2) )).

cnf(u346,negated_conjecture,
    ( u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK1,sK1),sK1)
    | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1) )).

cnf(u369,negated_conjecture,
    ( u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)))
    | sK2 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u367,negated_conjecture,
    ( u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)))
    | sK1 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u345,negated_conjecture,
    ( u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)),k4_xboole_0(u1_struct_0(sK0),sK2))
    | sK2 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u344,negated_conjecture,
    ( u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1))
    | sK1 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u381,negated_conjecture,
    ( u1_struct_0(sK0) != k4_xboole_0(u1_struct_0(sK0),sK2)
    | sK2 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u380,negated_conjecture,
    ( u1_struct_0(sK0) != k4_xboole_0(u1_struct_0(sK0),sK1)
    | sK1 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 )).

cnf(u382,axiom,
    ( k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) != X0
    | k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = X0 )).

cnf(u354,axiom,
    ( k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)) != X1
    | k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = X1 )).

cnf(u379,axiom,
    ( k4_xboole_0(X0,X0) != X0
    | k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:22:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.46  % (15327)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.47  % (15335)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.50  % (15315)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (15315)Refutation not found, incomplete strategy% (15315)------------------------------
% 0.20/0.50  % (15315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (15315)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (15315)Memory used [KB]: 1791
% 0.20/0.50  % (15315)Time elapsed: 0.113 s
% 0.20/0.50  % (15315)------------------------------
% 0.20/0.50  % (15315)------------------------------
% 0.20/0.50  % (15325)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (15329)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (15324)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (15322)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (15319)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (15332)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (15321)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (15328)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (15337)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (15339)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (15318)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (15317)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (15336)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (15340)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (15316)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (15331)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (15323)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (15330)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (15343)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (15324)Refutation not found, incomplete strategy% (15324)------------------------------
% 0.20/0.53  % (15324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15324)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15324)Memory used [KB]: 10746
% 0.20/0.53  % (15324)Time elapsed: 0.127 s
% 0.20/0.53  % (15324)------------------------------
% 0.20/0.53  % (15324)------------------------------
% 0.20/0.53  % (15314)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (15320)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (15342)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (15338)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (15330)Refutation not found, incomplete strategy% (15330)------------------------------
% 0.20/0.53  % (15330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15342)Refutation not found, incomplete strategy% (15342)------------------------------
% 0.20/0.53  % (15342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (15342)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15342)Memory used [KB]: 10746
% 0.20/0.53  % (15342)Time elapsed: 0.140 s
% 0.20/0.53  % (15342)------------------------------
% 0.20/0.53  % (15342)------------------------------
% 0.20/0.53  % (15330)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (15330)Memory used [KB]: 10618
% 0.20/0.53  % (15330)Time elapsed: 0.143 s
% 0.20/0.53  % (15330)------------------------------
% 0.20/0.53  % (15330)------------------------------
% 0.20/0.54  % (15334)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (15341)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (15339)Refutation not found, incomplete strategy% (15339)------------------------------
% 0.20/0.54  % (15339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (15339)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (15339)Memory used [KB]: 6396
% 0.20/0.54  % (15339)Time elapsed: 0.155 s
% 0.20/0.54  % (15339)------------------------------
% 0.20/0.54  % (15339)------------------------------
% 0.20/0.54  % (15326)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (15333)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.56  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.56  % (15321)# SZS output start Saturation.
% 0.20/0.56  cnf(u82,axiom,
% 0.20/0.56      m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u65,axiom,
% 0.20/0.56      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u81,negated_conjecture,
% 0.20/0.56      m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u80,negated_conjecture,
% 0.20/0.56      m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u40,negated_conjecture,
% 0.20/0.56      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u39,negated_conjecture,
% 0.20/0.56      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u141,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_xboole_0(X1,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u140,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k4_xboole_0(u1_struct_0(sK0),sK2)) | ~r1_xboole_0(X0,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u135,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X3,k4_xboole_0(u1_struct_0(sK0),sK2)) = k2_xboole_0(X3,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u125,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(X2,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u124,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X1,sK2) = k2_xboole_0(X1,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u123,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u121,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_xboole_0(X2,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u120,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X1,sK2) | r1_xboole_0(X1,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u119,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u113,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X2,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~r1_xboole_0(X2,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u112,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X1,sK2) | ~r1_xboole_0(X1,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u111,negated_conjecture,
% 0.20/0.56      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,sK1) | ~r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u199,axiom,
% 0.20/0.56      ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~r1_tarski(X5,k4_xboole_0(X6,X6)) | r1_xboole_0(X5,X6)).
% 0.20/0.56  
% 0.20/0.56  cnf(u198,axiom,
% 0.20/0.56      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | r1_tarski(X3,k4_xboole_0(X4,X4)) | ~r1_xboole_0(X3,X4)).
% 0.20/0.56  
% 0.20/0.56  cnf(u187,axiom,
% 0.20/0.56      ~m1_subset_1(X10,k1_zfmisc_1(X9)) | k4_subset_1(X9,X10,k4_xboole_0(X9,X9)) = k2_xboole_0(X10,k4_xboole_0(X9,X9))).
% 0.20/0.56  
% 0.20/0.56  cnf(u126,axiom,
% 0.20/0.56      ~m1_subset_1(X4,k1_zfmisc_1(X3)) | k4_subset_1(X3,X4,X3) = k2_xboole_0(X4,X3)).
% 0.20/0.56  
% 0.20/0.56  cnf(u122,axiom,
% 0.20/0.56      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | ~r1_tarski(X3,X4) | r1_xboole_0(X3,k4_xboole_0(X4,X4))).
% 0.20/0.56  
% 0.20/0.56  cnf(u114,axiom,
% 0.20/0.56      ~m1_subset_1(X3,k1_zfmisc_1(X4)) | r1_tarski(X3,X4) | ~r1_xboole_0(X3,k4_xboole_0(X4,X4))).
% 0.20/0.56  
% 0.20/0.56  cnf(u66,axiom,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0).
% 0.20/0.56  
% 0.20/0.56  cnf(u61,axiom,
% 0.20/0.56      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u60,axiom,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u56,axiom,
% 0.20/0.56      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X2) | r1_xboole_0(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u55,axiom,
% 0.20/0.56      ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r1_xboole_0(X1,k3_subset_1(X0,X2)) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u53,axiom,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.20/0.56  
% 0.20/0.56  cnf(u52,axiom,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u51,axiom,
% 0.20/0.56      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u276,negated_conjecture,
% 0.20/0.56      r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u263,negated_conjecture,
% 0.20/0.56      r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u63,axiom,
% 0.20/0.56      r1_tarski(X1,X1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u324,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_xboole_0(sK2,u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u278,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_xboole_0(sK2,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u228,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK2,u1_struct_0(sK0)) | r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u155,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK2,sK1) | r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u323,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u264,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_xboole_0(sK1,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u227,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK1,u1_struct_0(sK0)) | r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u160,negated_conjecture,
% 0.20/0.56      ~r1_tarski(sK1,sK2) | r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u281,negated_conjecture,
% 0.20/0.56      ~r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_xboole_0(u1_struct_0(sK0),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u268,negated_conjecture,
% 0.20/0.56      ~r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_xboole_0(u1_struct_0(sK0),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u164,negated_conjecture,
% 0.20/0.56      ~r1_tarski(u1_struct_0(sK0),sK2) | r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u158,negated_conjecture,
% 0.20/0.56      ~r1_tarski(u1_struct_0(sK0),sK1) | r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u232,axiom,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(X1,X1),X1) | r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u191,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u163,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u162,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK2) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u283,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK2) | sK2 = k4_xboole_0(u1_struct_0(sK0),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u192,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u157,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK1) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u284,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK1) | sK1 = k4_xboole_0(u1_struct_0(sK0),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u156,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u230,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u229,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u282,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u269,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u325,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u279,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u326,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u267,negated_conjecture,
% 0.20/0.56      ~r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u327,axiom,
% 0.20/0.56      ~r1_tarski(X0,k4_xboole_0(X0,X0)) | r1_xboole_0(X0,X0)).
% 0.20/0.56  
% 0.20/0.56  cnf(u59,axiom,
% 0.20/0.56      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u165,negated_conjecture,
% 0.20/0.56      r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u67,negated_conjecture,
% 0.20/0.56      r1_xboole_0(sK2,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u159,negated_conjecture,
% 0.20/0.56      r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u42,negated_conjecture,
% 0.20/0.56      r1_xboole_0(sK1,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u305,axiom,
% 0.20/0.56      r1_xboole_0(k4_xboole_0(X2,X2),X2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u245,negated_conjecture,
% 0.20/0.56      r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u202,negated_conjecture,
% 0.20/0.56      r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u233,axiom,
% 0.20/0.56      r1_xboole_0(X0,k4_xboole_0(X0,X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u318,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK2,u1_struct_0(sK0)) | r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u271,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK2,sK2) | r1_tarski(sK2,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u222,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_tarski(sK2,u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u145,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_tarski(sK2,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u317,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u257,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK1,sK1) | r1_tarski(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u221,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_tarski(sK1,u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u149,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_tarski(sK1,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u274,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(u1_struct_0(sK0),sK2) | r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u261,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(u1_struct_0(sK0),sK1) | r1_tarski(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u153,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_tarski(u1_struct_0(sK0),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u148,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_tarski(u1_struct_0(sK0),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u275,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u272,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK2) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u262,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u260,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK1) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u320,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u319,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u226,axiom,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) | r1_tarski(k4_xboole_0(X1,X1),X1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u224,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u223,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u193,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u152,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u151,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u194,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u147,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK2),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u146,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) | r1_tarski(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u178,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(X0,sK2) | k2_struct_0(sK0) != k2_xboole_0(X0,sK2) | sK1 = X0).
% 0.20/0.56  
% 0.20/0.56  cnf(u253,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(X0,sK2) | k4_xboole_0(u1_struct_0(sK0),sK2) = X0 | u1_struct_0(sK0) != k2_xboole_0(X0,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u220,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(X1,sK1) | sK2 = X1 | k2_struct_0(sK0) != k2_xboole_0(X1,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u248,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(X0,sK1) | k4_xboole_0(u1_struct_0(sK0),sK1) = X0 | u1_struct_0(sK0) != k2_xboole_0(X0,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u306,axiom,
% 0.20/0.56      ~r1_xboole_0(X0,k4_xboole_0(X1,X1)) | X0 = X1 | k2_xboole_0(X0,k4_xboole_0(X1,X1)) != X1).
% 0.20/0.56  
% 0.20/0.56  cnf(u302,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK2)) | sK2 = X0 | u1_struct_0(sK0) != k2_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u292,negated_conjecture,
% 0.20/0.56      ~r1_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1)) | sK1 = X0 | u1_struct_0(sK0) != k2_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u50,axiom,
% 0.20/0.56      ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)).
% 0.20/0.56  
% 0.20/0.56  cnf(u62,axiom,
% 0.20/0.56      ~r1_xboole_0(X2,X1) | X0 = X2 | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u350,axiom,
% 0.20/0.56      ~r1_xboole_0(X0,X1) | k4_xboole_0(X1,X1) = X0 | k2_xboole_0(X0,X1) != X1).
% 0.20/0.56  
% 0.20/0.56  cnf(u321,axiom,
% 0.20/0.56      ~r1_xboole_0(X0,X0) | r1_tarski(X0,k4_xboole_0(X0,X0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u138,negated_conjecture,
% 0.20/0.56      sK2 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u87,negated_conjecture,
% 0.20/0.56      sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u97,negated_conjecture,
% 0.20/0.56      sK1 = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u86,negated_conjecture,
% 0.20/0.56      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u177,negated_conjecture,
% 0.20/0.56      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u219,negated_conjecture,
% 0.20/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u41,negated_conjecture,
% 0.20/0.56      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u301,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u291,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u179,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u171,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u142,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u105,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u104,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u103,negated_conjecture,
% 0.20/0.56      u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u186,axiom,
% 0.20/0.56      k7_subset_1(X7,k4_xboole_0(X7,X7),X8) = k4_xboole_0(k4_xboole_0(X7,X7),X8)).
% 0.20/0.56  
% 0.20/0.56  cnf(u134,negated_conjecture,
% 0.20/0.56      k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),X2) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),X2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u92,negated_conjecture,
% 0.20/0.56      k7_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),X0)).
% 0.20/0.56  
% 0.20/0.56  cnf(u89,negated_conjecture,
% 0.20/0.56      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.20/0.56  
% 0.20/0.56  cnf(u238,axiom,
% 0.20/0.56      k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0)).
% 0.20/0.56  
% 0.20/0.56  cnf(u173,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.20/0.56  
% 0.20/0.56  cnf(u166,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.20/0.56  
% 0.20/0.56  cnf(u216,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u215,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.20/0.56  
% 0.20/0.56  cnf(u214,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK2) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u213,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),sK2) = k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u212,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u211,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),sK1) = k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u241,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) = k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.56  cnf(u240,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) = k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.56  
% 0.20/0.56  cnf(u303,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK2)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.56  
% 0.20/0.56  cnf(u298,negated_conjecture,
% 0.20/0.56      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.56  
% 0.20/0.57  % (15340)Refutation not found, incomplete strategy% (15340)------------------------------
% 0.20/0.57  % (15340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  cnf(u294,negated_conjecture,
% 0.20/0.57      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u293,negated_conjecture,
% 0.20/0.57      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u287,negated_conjecture,
% 0.20/0.57      k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u200,axiom,
% 0.20/0.57      k4_subset_1(X11,k4_xboole_0(X11,X11),X11) = X11).
% 0.20/0.57  
% 0.20/0.57  cnf(u106,axiom,
% 0.20/0.57      k4_subset_1(X0,X0,k4_xboole_0(X0,X0)) = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u88,axiom,
% 0.20/0.57      k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u79,axiom,
% 0.20/0.57      k3_subset_1(X0,X0) = k4_xboole_0(X0,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u78,negated_conjecture,
% 0.20/0.57      k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u77,negated_conjecture,
% 0.20/0.57      k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u44,axiom,
% 0.20/0.57      k2_subset_1(X0) = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u46,axiom,
% 0.20/0.57      k2_tarski(X0,X1) = k2_tarski(X1,X0)).
% 0.20/0.57  
% 0.20/0.57  cnf(u334,axiom,
% 0.20/0.57      k4_subset_1(X1,k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u330,negated_conjecture,
% 0.20/0.57      k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u286,negated_conjecture,
% 0.20/0.57      k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u329,negated_conjecture,
% 0.20/0.57      k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u295,negated_conjecture,
% 0.20/0.57      k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),sK1,k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u299,negated_conjecture,
% 0.20/0.57      k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u289,negated_conjecture,
% 0.20/0.57      k2_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u332,negated_conjecture,
% 0.20/0.57      k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u331,negated_conjecture,
% 0.20/0.57      k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.57  
% 0.20/0.57  cnf(u297,negated_conjecture,
% 0.20/0.57      k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u235,negated_conjecture,
% 0.20/0.57      k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u234,negated_conjecture,
% 0.20/0.57      k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u71,axiom,
% 0.20/0.57      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X1,X0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u48,axiom,
% 0.20/0.57      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u209,axiom,
% 0.20/0.57      k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u243,axiom,
% 0.20/0.57      k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1).
% 0.20/0.57  
% 0.20/0.57  cnf(u205,axiom,
% 0.20/0.57      k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u69,axiom,
% 0.20/0.57      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u47,axiom,
% 0.20/0.57      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u196,axiom,
% 0.20/0.57      k4_xboole_0(X1,k4_xboole_0(X1,X1)) = X1).
% 0.20/0.57  
% 0.20/0.57  cnf(u91,axiom,
% 0.20/0.57      k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3)).
% 0.20/0.57  
% 0.20/0.57  cnf(u90,negated_conjecture,
% 0.20/0.57      k7_subset_1(u1_struct_0(sK0),sK2,X1) = k4_xboole_0(sK2,X1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u307,axiom,
% 0.20/0.57      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))).
% 0.20/0.57  
% 0.20/0.57  cnf(u49,axiom,
% 0.20/0.57      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u399,negated_conjecture,
% 0.20/0.57      sK2 != k2_xboole_0(sK2,k4_xboole_0(u1_struct_0(sK0),sK2)) | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u373,negated_conjecture,
% 0.20/0.57      sK2 != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),sK2) | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u375,negated_conjecture,
% 0.20/0.57      sK2 != k2_xboole_0(sK1,sK2) | sK1 = k4_xboole_0(sK2,sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u389,negated_conjecture,
% 0.20/0.57      sK1 != u1_struct_0(sK0) | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u396,negated_conjecture,
% 0.20/0.57      sK1 != k2_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u385,negated_conjecture,
% 0.20/0.57      sK1 != k2_xboole_0(sK1,sK2) | sK2 = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u372,negated_conjecture,
% 0.20/0.57      sK1 != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),sK1) | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u377,negated_conjecture,
% 0.20/0.57      sK1 != k2_xboole_0(sK2,sK1) | sK2 = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u357,negated_conjecture,
% 0.20/0.57      sK1 != k2_struct_0(sK0) | sK2 = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u361,negated_conjecture,
% 0.20/0.57      k2_struct_0(sK0) != sK2 | sK1 = k4_xboole_0(sK2,sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u348,negated_conjecture,
% 0.20/0.57      k2_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) | sK1 = k4_xboole_0(sK2,sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u347,negated_conjecture,
% 0.20/0.57      k2_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK1,sK1),sK1) | sK2 = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u393,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != sK2 | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u252,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_struct_0(sK0) | sK1 = k4_xboole_0(u1_struct_0(sK0),sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u256,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_struct_0(sK0) | sK2 = k4_xboole_0(u1_struct_0(sK0),sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u364,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK2,sK2),sK2) | k4_xboole_0(u1_struct_0(sK0),sK2) = k4_xboole_0(sK2,sK2)).
% 0.20/0.57  
% 0.20/0.57  cnf(u346,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(sK1,sK1),sK1) | k4_xboole_0(u1_struct_0(sK0),sK1) = k4_xboole_0(sK1,sK1)).
% 0.20/0.57  
% 0.20/0.57  cnf(u369,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2))) | sK2 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u367,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))) | sK1 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u345,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2)),k4_xboole_0(u1_struct_0(sK0),sK2)) | sK2 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u344,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k2_xboole_0(k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1)),k4_xboole_0(u1_struct_0(sK0),sK1)) | sK1 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u381,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k4_xboole_0(u1_struct_0(sK0),sK2) | sK2 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK2),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.20/0.57  
% 0.20/0.57  cnf(u380,negated_conjecture,
% 0.20/0.57      u1_struct_0(sK0) != k4_xboole_0(u1_struct_0(sK0),sK1) | sK1 = k4_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.20/0.57  
% 0.20/0.57  cnf(u43,negated_conjecture,
% 0.20/0.57      k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2).
% 0.20/0.57  
% 0.20/0.57  cnf(u382,axiom,
% 0.20/0.57      k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) != X0 | k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = X0).
% 0.20/0.57  
% 0.20/0.57  cnf(u354,axiom,
% 0.20/0.57      k2_xboole_0(k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)),k4_xboole_0(X1,X1)) != X1 | k4_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) = X1).
% 0.20/0.57  
% 0.20/0.57  cnf(u379,axiom,
% 0.20/0.57      k4_xboole_0(X0,X0) != X0 | k4_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) = X0).
% 0.20/0.57  
% 0.20/0.57  % (15321)# SZS output end Saturation.
% 0.20/0.57  % (15321)------------------------------
% 0.20/0.57  % (15321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (15321)Termination reason: Satisfiable
% 0.20/0.57  
% 0.20/0.57  % (15321)Memory used [KB]: 2174
% 0.20/0.57  % (15321)Time elapsed: 0.156 s
% 0.20/0.57  % (15321)------------------------------
% 0.20/0.57  % (15321)------------------------------
% 0.20/0.57  % (15313)Success in time 0.222 s
%------------------------------------------------------------------------------
