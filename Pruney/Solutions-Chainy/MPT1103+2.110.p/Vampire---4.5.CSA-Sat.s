%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:48 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u15,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u27,axiom,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u22,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u19,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u21,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u30,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u29,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u31,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u25,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u12,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u26,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) )).

cnf(u23,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u20,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u17,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u16,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u13,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:21:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (10540)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.44  % (10540)# SZS output start Saturation.
% 0.20/0.44  cnf(u15,negated_conjecture,
% 0.20/0.44      l1_struct_0(sK0)).
% 0.20/0.44  
% 0.20/0.44  cnf(u27,axiom,
% 0.20/0.44      ~l1_struct_0(X0) | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))).
% 0.20/0.44  
% 0.20/0.44  cnf(u14,negated_conjecture,
% 0.20/0.44      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.44  
% 0.20/0.44  cnf(u22,axiom,
% 0.20/0.44      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.44  
% 0.20/0.44  cnf(u19,axiom,
% 0.20/0.44      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.20/0.44  
% 0.20/0.44  cnf(u21,axiom,
% 0.20/0.44      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.20/0.44  
% 0.20/0.44  cnf(u30,negated_conjecture,
% 0.20/0.44      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.20/0.44  
% 0.20/0.44  cnf(u29,negated_conjecture,
% 0.20/0.44      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.44  
% 0.20/0.44  cnf(u31,negated_conjecture,
% 0.20/0.44      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.44  
% 0.20/0.44  cnf(u25,axiom,
% 0.20/0.44      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.20/0.44  
% 0.20/0.44  cnf(u12,negated_conjecture,
% 0.20/0.44      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.44  
% 0.20/0.44  cnf(u26,negated_conjecture,
% 0.20/0.44      k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)).
% 0.20/0.44  
% 0.20/0.44  cnf(u23,axiom,
% 0.20/0.44      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.20/0.44  
% 0.20/0.44  cnf(u20,axiom,
% 0.20/0.44      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 0.20/0.44  
% 0.20/0.44  cnf(u17,axiom,
% 0.20/0.44      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.44  
% 0.20/0.44  cnf(u16,axiom,
% 0.20/0.44      k2_subset_1(X0) = X0).
% 0.20/0.44  
% 0.20/0.44  cnf(u13,negated_conjecture,
% 0.20/0.44      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.20/0.44  
% 0.20/0.44  % (10540)# SZS output end Saturation.
% 0.20/0.44  % (10540)------------------------------
% 0.20/0.44  % (10540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (10540)Termination reason: Satisfiable
% 0.20/0.44  
% 0.20/0.44  % (10540)Memory used [KB]: 1663
% 0.20/0.44  % (10540)Time elapsed: 0.029 s
% 0.20/0.44  % (10540)------------------------------
% 0.20/0.44  % (10540)------------------------------
% 0.20/0.44  % (10522)Success in time 0.08 s
%------------------------------------------------------------------------------
