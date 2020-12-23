%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:45 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u25,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u24,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u35,axiom,
    ( k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u15,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u34,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) )).

cnf(u30,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u36,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) )).

cnf(u29,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) )).

cnf(u26,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u21,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u33,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u19,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u18,axiom,
    ( k2_subset_1(X0) = X0 )).

cnf(u16,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (20226)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (20212)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (20218)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (20212)Refutation not found, incomplete strategy% (20212)------------------------------
% 0.22/0.49  % (20212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20225)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (20212)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20212)Memory used [KB]: 6140
% 0.22/0.50  % (20212)Time elapsed: 0.063 s
% 0.22/0.50  % (20212)------------------------------
% 0.22/0.50  % (20212)------------------------------
% 0.22/0.50  % (20221)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (20218)Refutation not found, incomplete strategy% (20218)------------------------------
% 0.22/0.50  % (20218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20218)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20218)Memory used [KB]: 10618
% 0.22/0.50  % (20218)Time elapsed: 0.084 s
% 0.22/0.50  % (20218)------------------------------
% 0.22/0.50  % (20218)------------------------------
% 0.22/0.51  % (20221)Refutation not found, incomplete strategy% (20221)------------------------------
% 0.22/0.51  % (20221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20221)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (20221)Memory used [KB]: 10618
% 0.22/0.51  % (20221)Time elapsed: 0.081 s
% 0.22/0.51  % (20221)------------------------------
% 0.22/0.51  % (20221)------------------------------
% 0.22/0.51  % (20229)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (20229)# SZS output start Saturation.
% 0.22/0.51  cnf(u17,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,axiom,
% 0.22/0.51      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u23,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u35,axiom,
% 0.22/0.51      k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u34,negated_conjecture,
% 0.22/0.51      sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u30,axiom,
% 0.22/0.51      k1_xboole_0 = k3_subset_1(X0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u36,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u29,negated_conjecture,
% 0.22/0.51      k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)).
% 0.22/0.51  
% 0.22/0.51  cnf(u26,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u21,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u33,axiom,
% 0.22/0.51      k3_subset_1(X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u19,axiom,
% 0.22/0.51      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u18,axiom,
% 0.22/0.51      k2_subset_1(X0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u16,negated_conjecture,
% 0.22/0.51      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  % (20229)# SZS output end Saturation.
% 0.22/0.51  % (20229)------------------------------
% 0.22/0.51  % (20229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20229)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (20229)Memory used [KB]: 1663
% 0.22/0.51  % (20229)Time elapsed: 0.083 s
% 0.22/0.51  % (20229)------------------------------
% 0.22/0.51  % (20229)------------------------------
% 0.22/0.51  % (20211)Success in time 0.148 s
%------------------------------------------------------------------------------
