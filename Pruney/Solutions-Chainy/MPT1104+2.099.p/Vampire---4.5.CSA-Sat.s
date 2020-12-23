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
% DateTime   : Thu Dec  3 13:09:03 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   21 (  21 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    0
%              Number of atoms          :   29 (  29 expanded)
%              Number of equality atoms :   17 (  17 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u19,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u18,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u27,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0) )).

cnf(u28,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1) )).

cnf(u20,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u22,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u23,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) )).

cnf(u16,negated_conjecture,
    ( r1_xboole_0(sK1,sK2) )).

cnf(u21,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 )).

cnf(u31,negated_conjecture,
    ( sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2)) )).

cnf(u38,negated_conjecture,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

cnf(u32,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u37,negated_conjecture,
    ( k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

cnf(u15,negated_conjecture,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

cnf(u26,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1) )).

cnf(u25,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

cnf(u36,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

cnf(u34,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) )).

cnf(u33,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

cnf(u17,negated_conjecture,
    ( sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (11750)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (11752)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (11758)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (11749)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (11749)Refutation not found, incomplete strategy% (11749)------------------------------
% 0.21/0.49  % (11749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11749)Memory used [KB]: 1663
% 0.21/0.49  % (11749)Time elapsed: 0.059 s
% 0.21/0.49  % (11749)------------------------------
% 0.21/0.49  % (11749)------------------------------
% 0.21/0.49  % (11764)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (11758)Refutation not found, incomplete strategy% (11758)------------------------------
% 0.21/0.49  % (11758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (11758)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (11758)Memory used [KB]: 1663
% 0.21/0.49  % (11758)Time elapsed: 0.068 s
% 0.21/0.49  % (11758)------------------------------
% 0.21/0.49  % (11758)------------------------------
% 0.21/0.50  % (11754)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  % (11759)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (11761)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (11754)Refutation not found, incomplete strategy% (11754)------------------------------
% 0.21/0.50  % (11754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11754)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11754)Memory used [KB]: 10618
% 0.21/0.50  % (11754)Time elapsed: 0.073 s
% 0.21/0.50  % (11754)------------------------------
% 0.21/0.50  % (11754)------------------------------
% 0.21/0.50  % (11763)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (11764)Refutation not found, incomplete strategy% (11764)------------------------------
% 0.21/0.50  % (11764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (11764)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (11764)Memory used [KB]: 6140
% 0.21/0.50  % (11764)Time elapsed: 0.075 s
% 0.21/0.50  % (11764)------------------------------
% 0.21/0.50  % (11764)------------------------------
% 0.21/0.50  % (11765)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (11763)Refutation not found, incomplete strategy% (11763)------------------------------
% 0.21/0.51  % (11763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11763)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11763)Memory used [KB]: 1663
% 0.21/0.51  % (11763)Time elapsed: 0.087 s
% 0.21/0.51  % (11763)------------------------------
% 0.21/0.51  % (11763)------------------------------
% 0.21/0.51  % (11762)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (11747)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.51  % (11762)# SZS output start Saturation.
% 0.21/0.51  cnf(u19,negated_conjecture,
% 0.21/0.51      l1_struct_0(sK0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u18,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u14,negated_conjecture,
% 0.21/0.51      m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.21/0.51  
% 0.21/0.51  cnf(u27,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X0) = k2_xboole_0(sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u28,negated_conjecture,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X1) = k2_xboole_0(sK1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u20,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.21/0.51  
% 0.21/0.51  cnf(u22,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u23,axiom,
% 0.21/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u16,negated_conjecture,
% 0.21/0.51      r1_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u21,axiom,
% 0.21/0.51      ~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0).
% 0.21/0.51  
% 0.21/0.51  cnf(u31,negated_conjecture,
% 0.21/0.51      sK2 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK2))).
% 0.21/0.51  
% 0.21/0.51  cnf(u38,negated_conjecture,
% 0.21/0.51      sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u32,negated_conjecture,
% 0.21/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.21/0.51  
% 0.21/0.51  cnf(u37,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u15,negated_conjecture,
% 0.21/0.51      k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u26,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u25,negated_conjecture,
% 0.21/0.51      k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)).
% 0.21/0.51  
% 0.21/0.51  cnf(u36,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u34,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1)).
% 0.21/0.51  
% 0.21/0.51  cnf(u33,negated_conjecture,
% 0.21/0.51      k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)).
% 0.21/0.51  
% 0.21/0.51  cnf(u17,negated_conjecture,
% 0.21/0.51      sK2 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)).
% 0.21/0.51  
% 0.21/0.51  % (11762)# SZS output end Saturation.
% 0.21/0.51  % (11762)------------------------------
% 0.21/0.51  % (11762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11762)Termination reason: Satisfiable
% 0.21/0.51  
% 0.21/0.51  % (11762)Memory used [KB]: 1663
% 0.21/0.51  % (11762)Time elapsed: 0.096 s
% 0.21/0.51  % (11762)------------------------------
% 0.21/0.51  % (11762)------------------------------
% 0.21/0.51  % (11739)Success in time 0.146 s
%------------------------------------------------------------------------------
