%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:45 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u27,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u21,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )).

cnf(u25,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u26,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u41,axiom,
    ( k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3) )).

cnf(u17,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u39,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u36,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u40,axiom,
    ( k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1) )).

cnf(u42,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4) )).

cnf(u31,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u37,axiom,
    ( k1_xboole_0 = k4_xboole_0(X1,X1) )).

cnf(u32,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u22,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u20,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u18,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (12849)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.43  % (12849)Refutation not found, incomplete strategy% (12849)------------------------------
% 0.22/0.43  % (12849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (12849)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.43  
% 0.22/0.43  % (12849)Memory used [KB]: 10618
% 0.22/0.43  % (12849)Time elapsed: 0.005 s
% 0.22/0.43  % (12849)------------------------------
% 0.22/0.43  % (12849)------------------------------
% 0.22/0.47  % (12857)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.47  % (12857)# SZS output start Saturation.
% 0.22/0.47  cnf(u19,negated_conjecture,
% 0.22/0.47      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.47  
% 0.22/0.47  cnf(u27,axiom,
% 0.22/0.47      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u21,axiom,
% 0.22/0.47      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 0.22/0.47  
% 0.22/0.47  cnf(u24,axiom,
% 0.22/0.47      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u25,axiom,
% 0.22/0.47      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.22/0.47  
% 0.22/0.47  cnf(u26,axiom,
% 0.22/0.47      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.47  
% 0.22/0.47  cnf(u41,axiom,
% 0.22/0.47      k7_subset_1(X2,X2,X3) = k4_xboole_0(X2,X3)).
% 0.22/0.47  
% 0.22/0.47  cnf(u17,negated_conjecture,
% 0.22/0.47      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u39,negated_conjecture,
% 0.22/0.47      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.22/0.47  
% 0.22/0.47  cnf(u36,axiom,
% 0.22/0.47      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.22/0.47  
% 0.22/0.47  cnf(u40,axiom,
% 0.22/0.47      k7_subset_1(X0,k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,X1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u42,negated_conjecture,
% 0.22/0.47      k7_subset_1(u1_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4)).
% 0.22/0.47  
% 0.22/0.47  cnf(u31,negated_conjecture,
% 0.22/0.47      k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u37,axiom,
% 0.22/0.47      k1_xboole_0 = k4_xboole_0(X1,X1)).
% 0.22/0.47  
% 0.22/0.47  cnf(u32,axiom,
% 0.22/0.47      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.22/0.47  
% 0.22/0.47  cnf(u22,axiom,
% 0.22/0.47      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.47  
% 0.22/0.47  cnf(u20,axiom,
% 0.22/0.47      k2_subset_1(X0) = X0).
% 0.22/0.47  
% 0.22/0.47  cnf(u18,negated_conjecture,
% 0.22/0.47      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.22/0.47  
% 0.22/0.47  % (12857)# SZS output end Saturation.
% 0.22/0.47  % (12857)------------------------------
% 0.22/0.47  % (12857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12857)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (12857)Memory used [KB]: 1663
% 0.22/0.47  % (12857)Time elapsed: 0.044 s
% 0.22/0.47  % (12857)------------------------------
% 0.22/0.47  % (12857)------------------------------
% 0.22/0.47  % (12839)Success in time 0.106 s
%------------------------------------------------------------------------------
