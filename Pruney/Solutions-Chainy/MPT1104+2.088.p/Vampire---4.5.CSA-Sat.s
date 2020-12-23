%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:01 EST 2020

% Result     : CounterSatisfiable 0.17s
% Output     : Saturation 0.17s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   43 (  43 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u31,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u46,negated_conjecture,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2) )).

cnf(u47,negated_conjecture,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3) )).

cnf(u27,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u29,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u30,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u45,axiom,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0) )).

cnf(u21,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u26,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u40,negated_conjecture,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2)) )).

cnf(u55,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u41,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u54,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u20,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u44,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3) )).

cnf(u43,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2) )).

cnf(u56,axiom,
    ( k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0) )).

cnf(u58,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u57,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u51,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

cnf(u53,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u48,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

cnf(u50,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u49,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u35,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u34,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2) )).

cnf(u39,axiom,
    ( k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 )).

cnf(u33,axiom,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) )).

cnf(u24,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u42,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u22,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : run_vampire %s %d
% 0.09/0.30  % Computer   : n006.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.17/0.43  % (846)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.17/0.43  % (848)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.17/0.44  % (856)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.17/0.44  % (854)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.17/0.44  % (852)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.17/0.44  % (848)Refutation not found, incomplete strategy% (848)------------------------------
% 0.17/0.44  % (848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.44  % SZS status CounterSatisfiable for theBenchmark
% 0.17/0.44  % (848)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.44  
% 0.17/0.44  % (848)Memory used [KB]: 10618
% 0.17/0.44  % (848)Time elapsed: 0.067 s
% 0.17/0.44  % (848)------------------------------
% 0.17/0.44  % (848)------------------------------
% 0.17/0.44  % (844)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.17/0.45  % (852)Refutation not found, incomplete strategy% (852)------------------------------
% 0.17/0.45  % (852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.45  % (856)# SZS output start Saturation.
% 0.17/0.45  cnf(u23,negated_conjecture,
% 0.17/0.45      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.17/0.45  
% 0.17/0.45  cnf(u19,negated_conjecture,
% 0.17/0.45      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.17/0.45  
% 0.17/0.45  cnf(u31,axiom,
% 0.17/0.45      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.17/0.45  
% 0.17/0.45  cnf(u46,negated_conjecture,
% 0.17/0.45      ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u47,negated_conjecture,
% 0.17/0.45      ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X3) = k2_xboole_0(sK1,X3)).
% 0.17/0.45  
% 0.17/0.45  cnf(u27,axiom,
% 0.17/0.45      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)).
% 0.17/0.45  
% 0.17/0.45  cnf(u28,axiom,
% 0.17/0.45      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.17/0.45  
% 0.17/0.45  cnf(u29,axiom,
% 0.17/0.45      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u30,axiom,
% 0.17/0.45      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u45,axiom,
% 0.17/0.45      ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k4_subset_1(X1,X1,X0) = k2_xboole_0(X1,X0)).
% 0.17/0.45  
% 0.17/0.45  cnf(u21,negated_conjecture,
% 0.17/0.45      r1_xboole_0(sK1,sK2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u26,axiom,
% 0.17/0.45      ~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 0.17/0.45  
% 0.17/0.45  cnf(u40,negated_conjecture,
% 0.17/0.45      sK2 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK2))).
% 0.17/0.45  
% 0.17/0.45  cnf(u55,negated_conjecture,
% 0.17/0.45      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u41,negated_conjecture,
% 0.17/0.45      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.17/0.45  
% 0.17/0.45  cnf(u54,negated_conjecture,
% 0.17/0.45      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u20,negated_conjecture,
% 0.17/0.45      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u44,negated_conjecture,
% 0.17/0.45      k7_subset_1(u1_struct_0(sK0),sK1,X3) = k4_xboole_0(sK1,X3)).
% 0.17/0.45  
% 0.17/0.45  cnf(u43,negated_conjecture,
% 0.17/0.45      k7_subset_1(u1_struct_0(sK0),sK2,X2) = k4_xboole_0(sK2,X2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u56,axiom,
% 0.17/0.45      k4_subset_1(X0,X0,X0) = k2_xboole_0(X0,X0)).
% 0.17/0.45  
% 0.17/0.45  cnf(u58,negated_conjecture,
% 0.17/0.45      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(u1_struct_0(sK0),sK1)).
% 0.17/0.45  
% 0.17/0.45  cnf(u57,negated_conjecture,
% 0.17/0.45      k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(u1_struct_0(sK0),sK2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u51,negated_conjecture,
% 0.17/0.45      k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) = k2_xboole_0(sK1,u1_struct_0(sK0))).
% 0.17/0.45  
% 0.17/0.45  cnf(u53,negated_conjecture,
% 0.17/0.45      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.17/0.45  
% 0.17/0.45  cnf(u48,negated_conjecture,
% 0.17/0.45      k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) = k2_xboole_0(sK2,u1_struct_0(sK0))).
% 0.17/0.45  
% 0.17/0.45  cnf(u50,negated_conjecture,
% 0.17/0.45      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.17/0.45  
% 0.17/0.45  cnf(u49,negated_conjecture,
% 0.17/0.45      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u35,negated_conjecture,
% 0.17/0.45      k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)).
% 0.17/0.45  
% 0.17/0.45  cnf(u34,negated_conjecture,
% 0.17/0.45      k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)).
% 0.17/0.45  
% 0.17/0.45  cnf(u39,axiom,
% 0.17/0.45      k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0).
% 0.17/0.45  
% 0.17/0.45  cnf(u33,axiom,
% 0.17/0.45      k3_subset_1(X0,X0) = k4_xboole_0(X0,X0)).
% 0.17/0.45  
% 0.17/0.45  cnf(u24,axiom,
% 0.17/0.45      k2_subset_1(X0) = X0).
% 0.17/0.45  
% 0.17/0.45  cnf(u42,axiom,
% 0.17/0.45      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.17/0.45  
% 0.17/0.45  cnf(u22,negated_conjecture,
% 0.17/0.45      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.17/0.45  
% 0.17/0.45  % (856)# SZS output end Saturation.
% 0.17/0.45  % (856)------------------------------
% 0.17/0.45  % (856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.45  % (856)Termination reason: Satisfiable
% 0.17/0.45  
% 0.17/0.45  % (856)Memory used [KB]: 1663
% 0.17/0.45  % (856)Time elapsed: 0.069 s
% 0.17/0.45  % (856)------------------------------
% 0.17/0.45  % (856)------------------------------
% 0.17/0.45  % (838)Success in time 0.132 s
%------------------------------------------------------------------------------
