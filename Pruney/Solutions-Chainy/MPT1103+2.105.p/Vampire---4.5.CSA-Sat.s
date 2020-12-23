%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:48 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   20 (  20 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u29,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u51,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u58,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u52,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u47,axiom,
    ( k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k7_subset_1(X0,X0,X0) )).

cnf(u61,axiom,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1)) )).

cnf(u60,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u54,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u55,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u53,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u71,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,X1) )).

cnf(u62,axiom,
    ( k7_subset_1(X1,X1,X2) = k5_xboole_0(X1,k7_subset_1(X1,X1,k7_subset_1(X1,X1,X2))) )).

cnf(u69,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u27,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u25,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u50,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (8564)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (8558)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (8564)# SZS output start Saturation.
% 0.20/0.52  cnf(u24,negated_conjecture,
% 0.20/0.52      l1_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u29,axiom,
% 0.20/0.52      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u51,axiom,
% 0.20/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u23,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u58,axiom,
% 0.20/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u52,negated_conjecture,
% 0.20/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u47,axiom,
% 0.20/0.52      k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u70,axiom,
% 0.20/0.52      k1_xboole_0 = k7_subset_1(X0,X0,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u61,axiom,
% 0.20/0.52      k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k7_subset_1(X0,X0,k7_subset_1(X0,X0,X1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u60,negated_conjecture,
% 0.20/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u54,negated_conjecture,
% 0.20/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u55,negated_conjecture,
% 0.20/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u53,negated_conjecture,
% 0.20/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u21,negated_conjecture,
% 0.20/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u71,axiom,
% 0.20/0.52      k1_xboole_0 = k5_xboole_0(X1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u62,axiom,
% 0.20/0.52      k7_subset_1(X1,X1,X2) = k5_xboole_0(X1,k7_subset_1(X1,X1,k7_subset_1(X1,X1,X2)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u69,axiom,
% 0.20/0.52      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u27,axiom,
% 0.20/0.52      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u25,axiom,
% 0.20/0.52      k2_subset_1(X0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u50,negated_conjecture,
% 0.20/0.52      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.20/0.52  
% 0.20/0.52  % (8564)# SZS output end Saturation.
% 0.20/0.52  % (8564)------------------------------
% 0.20/0.52  % (8564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8564)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (8564)Memory used [KB]: 6268
% 0.20/0.52  % (8564)Time elapsed: 0.113 s
% 0.20/0.52  % (8564)------------------------------
% 0.20/0.52  % (8564)------------------------------
% 0.20/0.52  % (8557)Success in time 0.17 s
%------------------------------------------------------------------------------
