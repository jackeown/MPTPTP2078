%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:47 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   28 (  28 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    0
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u29,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u46,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u101,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u69,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u49,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u48,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u42,axiom,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) )).

cnf(u30,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u47,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) )).

cnf(u40,axiom,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) )).

cnf(u104,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u102,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u103,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u71,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u79,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X2) )).

cnf(u84,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u78,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u21,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u68,axiom,
    ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,X2) )).

cnf(u41,axiom,
    ( k1_setfam_1(k2_tarski(X0,X0)) = X0 )).

cnf(u77,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u25,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u27,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u45,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:32:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (10345)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (10345)# SZS output start Saturation.
% 0.21/0.50  cnf(u24,negated_conjecture,
% 0.21/0.50      l1_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u29,axiom,
% 0.21/0.50      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.50  
% 0.21/0.50  cnf(u46,axiom,
% 0.21/0.50      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u23,negated_conjecture,
% 0.21/0.50      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u101,negated_conjecture,
% 0.21/0.50      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u69,axiom,
% 0.21/0.50      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u49,axiom,
% 0.21/0.50      r1_tarski(X1,X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u48,axiom,
% 0.21/0.50      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u42,axiom,
% 0.21/0.50      r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u30,axiom,
% 0.21/0.50      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u47,axiom,
% 0.21/0.50      k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u40,axiom,
% 0.21/0.50      k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u104,negated_conjecture,
% 0.21/0.50      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u102,negated_conjecture,
% 0.21/0.50      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u103,negated_conjecture,
% 0.21/0.50      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u71,negated_conjecture,
% 0.21/0.50      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u79,axiom,
% 0.21/0.50      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u84,axiom,
% 0.21/0.50      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u78,axiom,
% 0.21/0.50      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u21,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u68,axiom,
% 0.21/0.50      k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X1,X1,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u70,axiom,
% 0.21/0.50      k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))))).
% 0.21/0.50  
% 0.21/0.50  cnf(u61,axiom,
% 0.21/0.50      k1_xboole_0 = k5_xboole_0(X2,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u41,axiom,
% 0.21/0.50      k1_setfam_1(k2_tarski(X0,X0)) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u77,axiom,
% 0.21/0.50      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u25,axiom,
% 0.21/0.50      k2_subset_1(X0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u27,axiom,
% 0.21/0.50      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u45,negated_conjecture,
% 0.21/0.50      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 0.21/0.50  
% 0.21/0.50  % (10345)# SZS output end Saturation.
% 0.21/0.50  % (10345)------------------------------
% 0.21/0.50  % (10345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10345)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (10345)Memory used [KB]: 6268
% 0.21/0.50  % (10345)Time elapsed: 0.089 s
% 0.21/0.50  % (10345)------------------------------
% 0.21/0.50  % (10345)------------------------------
% 0.21/0.51  % (10338)Success in time 0.142 s
%------------------------------------------------------------------------------
