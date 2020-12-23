%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:41 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   32 (  32 expanded)
%              Number of leaves         :   32 (  32 expanded)
%              Depth                    :    0
%              Number of atoms          :   46 (  46 expanded)
%              Number of equality atoms :   31 (  31 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u78,axiom,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) )).

cnf(u51,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u25,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u83,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
    | ~ l1_struct_0(X0) )).

cnf(u48,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u35,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u55,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u39,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u42,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u42_001,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 )).

cnf(u82,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u81,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u109,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u89,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u85,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u43,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u84,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0)))) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k5_xboole_0(X2,X2) )).

cnf(u53,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u34,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u91,axiom,
    ( k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X2) )).

cnf(u94,axiom,
    ( k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2))) )).

cnf(u90,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u29,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u74,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2) )).

cnf(u52,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u54,axiom,
    ( k3_xboole_0(X1,X1) = X1 )).

cnf(u80,negated_conjecture,
    ( k2_struct_0(sK0) != sK1 )).

cnf(u76,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | k2_struct_0(sK0) != sK1 )).

cnf(u50,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | k2_struct_0(sK0) != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:48:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (12954)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.52  % (12954)# SZS output start Saturation.
% 0.20/0.52  cnf(u24,negated_conjecture,
% 0.20/0.52      l1_struct_0(sK0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u78,axiom,
% 0.20/0.52      ~l1_struct_0(X0) | u1_struct_0(X0) = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u51,axiom,
% 0.20/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.20/0.52  
% 0.20/0.52  cnf(u25,negated_conjecture,
% 0.20/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u83,axiom,
% 0.20/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u31,axiom,
% 0.20/0.52      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~l1_struct_0(X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u48,axiom,
% 0.20/0.52      r1_tarski(X1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u35,axiom,
% 0.20/0.52      r1_tarski(k1_xboole_0,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u55,axiom,
% 0.20/0.52      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u39,axiom,
% 0.20/0.52      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u42,axiom,
% 0.20/0.52      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u42,axiom,
% 0.20/0.52      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u82,negated_conjecture,
% 0.20/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 0.20/0.52  
% 0.20/0.52  cnf(u81,negated_conjecture,
% 0.20/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.20/0.52  
% 0.20/0.52  cnf(u109,negated_conjecture,
% 0.20/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u89,axiom,
% 0.20/0.52      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u85,negated_conjecture,
% 0.20/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u43,axiom,
% 0.20/0.52      k2_subset_1(X0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u84,axiom,
% 0.20/0.52      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k7_subset_1(X1,X1,X0))))).
% 0.20/0.52  
% 0.20/0.52  cnf(u70,axiom,
% 0.20/0.52      k1_xboole_0 = k5_xboole_0(X2,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u53,axiom,
% 0.20/0.52      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u34,axiom,
% 0.20/0.52      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.52  
% 0.20/0.52  cnf(u91,axiom,
% 0.20/0.52      k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u94,axiom,
% 0.20/0.52      k1_xboole_0 = k7_subset_1(X2,X2,k5_xboole_0(X2,k7_subset_1(X3,X3,X2)))).
% 0.20/0.52  
% 0.20/0.52  cnf(u90,axiom,
% 0.20/0.52      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 0.20/0.52  
% 0.20/0.52  cnf(u29,negated_conjecture,
% 0.20/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.20/0.52  
% 0.20/0.52  cnf(u74,axiom,
% 0.20/0.52      k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X1,X1,X2)).
% 0.20/0.52  
% 0.20/0.52  cnf(u52,axiom,
% 0.20/0.52      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.52  
% 0.20/0.52  cnf(u54,axiom,
% 0.20/0.52      k3_xboole_0(X1,X1) = X1).
% 0.20/0.52  
% 0.20/0.52  cnf(u80,negated_conjecture,
% 0.20/0.52      k2_struct_0(sK0) != sK1).
% 0.20/0.52  
% 0.20/0.52  cnf(u76,negated_conjecture,
% 0.20/0.52      k1_xboole_0 != k5_xboole_0(sK1,sK1) | k2_struct_0(sK0) != sK1).
% 0.20/0.52  
% 0.20/0.52  cnf(u50,negated_conjecture,
% 0.20/0.52      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) | k2_struct_0(sK0) != sK1).
% 0.20/0.52  
% 0.20/0.52  % (12954)# SZS output end Saturation.
% 0.20/0.52  % (12954)------------------------------
% 0.20/0.52  % (12954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12954)Termination reason: Satisfiable
% 0.20/0.52  
% 0.20/0.52  % (12954)Memory used [KB]: 1791
% 0.20/0.52  % (12954)Time elapsed: 0.089 s
% 0.20/0.52  % (12954)------------------------------
% 0.20/0.52  % (12954)------------------------------
% 0.20/0.53  % (12950)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (12948)Success in time 0.169 s
%------------------------------------------------------------------------------
