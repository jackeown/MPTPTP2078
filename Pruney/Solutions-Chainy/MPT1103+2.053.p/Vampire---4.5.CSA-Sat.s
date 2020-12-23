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
% DateTime   : Thu Dec  3 13:08:41 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   39 (  39 expanded)
%              Number of leaves         :   39 (  39 expanded)
%              Depth                    :    0
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :   37 (  37 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u25,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u36,axiom,
    ( ~ l1_struct_0(X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u48,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u26,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u60,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u46,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u31,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u56,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u41,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u44,axiom,
    ( ~ r1_tarski(X1,X0)
    | X0 = X1
    | ~ r1_tarski(X0,X1) )).

cnf(u71,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | k2_struct_0(sK0) = sK1 )).

cnf(u61,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u62,negated_conjecture,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) )).

cnf(u58,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u32,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u66,axiom,
    ( k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) )).

cnf(u89,axiom,
    ( k2_xboole_0(X0,X0) = X0 )).

cnf(u73,axiom,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 )).

cnf(u69,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) )).

cnf(u53,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) )).

cnf(u39,axiom,
    ( k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) )).

cnf(u30,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) = sK1 )).

cnf(u94,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u50,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u70,axiom,
    ( k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) )).

cnf(u64,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

cnf(u79,axiom,
    ( k1_xboole_0 = k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2)) )).

cnf(u90,axiom,
    ( k1_xboole_0 = k4_xboole_0(X1,X1) )).

cnf(u37,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u83,axiom,
    ( k5_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2)) )).

cnf(u34,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u51,axiom,
    ( k3_xboole_0(X1,X1) = X1 )).

cnf(u38,axiom,
    ( k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

cnf(u59,axiom,
    ( k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u55,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u40,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | k2_struct_0(sK0) != sK1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n018.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 09:56:11 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.51  % (28426)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (28419)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (28420)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (28420)Refutation not found, incomplete strategy% (28420)------------------------------
% 0.21/0.52  % (28420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28420)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28420)Memory used [KB]: 1663
% 0.21/0.52  % (28420)Time elapsed: 0.115 s
% 0.21/0.52  % (28420)------------------------------
% 0.21/0.52  % (28420)------------------------------
% 0.21/0.52  % (28426)# SZS output start Saturation.
% 0.21/0.52  cnf(u25,negated_conjecture,
% 0.21/0.52      l1_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u36,axiom,
% 0.21/0.52      ~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u48,axiom,
% 0.21/0.52      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u26,negated_conjecture,
% 0.21/0.52      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u60,negated_conjecture,
% 0.21/0.52      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u45,axiom,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u46,axiom,
% 0.21/0.52      r1_tarski(X1,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u31,axiom,
% 0.21/0.52      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u56,axiom,
% 0.21/0.52      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u41,axiom,
% 0.21/0.52      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u44,axiom,
% 0.21/0.52      ~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u71,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | k2_struct_0(sK0) = sK1).
% 0.21/0.52  
% 0.21/0.52  cnf(u61,negated_conjecture,
% 0.21/0.52      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u62,negated_conjecture,
% 0.21/0.52      u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))).
% 0.21/0.52  
% 0.21/0.52  cnf(u58,negated_conjecture,
% 0.21/0.52      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u32,axiom,
% 0.21/0.52      k2_subset_1(X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u66,axiom,
% 0.21/0.52      k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u89,axiom,
% 0.21/0.52      k2_xboole_0(X0,X0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u73,axiom,
% 0.21/0.52      k2_xboole_0(X1,k1_xboole_0) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u69,axiom,
% 0.21/0.52      k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u53,axiom,
% 0.21/0.52      k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u39,axiom,
% 0.21/0.52      k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u30,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) = sK1).
% 0.21/0.52  
% 0.21/0.52  cnf(u94,axiom,
% 0.21/0.52      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u50,axiom,
% 0.21/0.52      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u33,axiom,
% 0.21/0.52      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u70,axiom,
% 0.21/0.52      k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u64,axiom,
% 0.21/0.52      k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u79,axiom,
% 0.21/0.52      k1_xboole_0 = k4_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2))).
% 0.21/0.52  
% 0.21/0.52  cnf(u90,axiom,
% 0.21/0.52      k1_xboole_0 = k4_xboole_0(X1,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u37,axiom,
% 0.21/0.52      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u83,axiom,
% 0.21/0.52      k5_xboole_0(k1_xboole_0,X2) = k2_xboole_0(k5_xboole_0(k1_xboole_0,X2),k5_xboole_0(k1_xboole_0,X2))).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,axiom,
% 0.21/0.52      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u51,axiom,
% 0.21/0.52      k3_xboole_0(X1,X1) = X1).
% 0.21/0.52  
% 0.21/0.52  cnf(u38,axiom,
% 0.21/0.52      k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u59,axiom,
% 0.21/0.52      k4_xboole_0(X1,X2) = k7_subset_1(X1,X1,X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u55,axiom,
% 0.21/0.52      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u40,axiom,
% 0.21/0.52      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u27,negated_conjecture,
% 0.21/0.52      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | k2_struct_0(sK0) != sK1).
% 0.21/0.52  
% 0.21/0.52  % (28426)# SZS output end Saturation.
% 0.21/0.52  % (28426)------------------------------
% 0.21/0.52  % (28426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28426)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (28426)Memory used [KB]: 1791
% 0.21/0.52  % (28426)Time elapsed: 0.114 s
% 0.21/0.52  % (28426)------------------------------
% 0.21/0.52  % (28426)------------------------------
% 0.21/0.53  % (28418)Success in time 0.168 s
%------------------------------------------------------------------------------
