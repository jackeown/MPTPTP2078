%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:44 EST 2020

% Result     : CounterSatisfiable 1.68s
% Output     : Saturation 1.68s
% Verified   : 
% Statistics : Number of clauses        :   22 (  22 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   21 (  21 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u40,axiom,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) )).

cnf(u25,axiom,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )).

cnf(u22,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u31,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 )).

cnf(u55,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1) )).

cnf(u54,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2) )).

cnf(u41,negated_conjecture,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) )).

cnf(u79,axiom,
    ( k7_subset_1(X0,X0,k1_xboole_0) = X0 )).

cnf(u52,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X2))) )).

cnf(u57,axiom,
    ( k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0) )).

cnf(u56,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0) )).

cnf(u76,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) )).

cnf(u46,negated_conjecture,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) )).

cnf(u35,axiom,
    ( k3_subset_1(X0,k1_xboole_0) = X0 )).

cnf(u50,axiom,
    ( k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1))) )).

cnf(u44,axiom,
    ( k1_xboole_0 = k3_subset_1(X0,X0) )).

cnf(u80,axiom,
    ( k1_xboole_0 = k7_subset_1(X1,X1,X1) )).

cnf(u58,axiom,
    ( k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,k1_xboole_0) )).

cnf(u20,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u53,axiom,
    ( k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4))) )).

cnf(u49,axiom,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 )).

cnf(u39,negated_conjecture,
    ( sK1 != k2_struct_0(sK0)
    | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:40:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 1.37/0.56  % (10627)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.57  % (10615)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.57  % (10605)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.57  % (10607)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.57  % (10607)Refutation not found, incomplete strategy% (10607)------------------------------
% 1.37/0.57  % (10607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (10614)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.57  % (10607)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.58  % (10607)Memory used [KB]: 6268
% 1.37/0.58  % (10607)Time elapsed: 0.160 s
% 1.37/0.58  % (10607)------------------------------
% 1.37/0.58  % (10607)------------------------------
% 1.37/0.58  % (10629)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.58  % (10615)Refutation not found, incomplete strategy% (10615)------------------------------
% 1.37/0.58  % (10615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (10615)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (10615)Memory used [KB]: 6140
% 1.37/0.58  % (10615)Time elapsed: 0.002 s
% 1.37/0.58  % (10615)------------------------------
% 1.37/0.58  % (10615)------------------------------
% 1.37/0.58  % (10605)Refutation not found, incomplete strategy% (10605)------------------------------
% 1.37/0.58  % (10605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (10621)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.68/0.58  % (10627)Refutation not found, incomplete strategy% (10627)------------------------------
% 1.68/0.58  % (10627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.58  % (10627)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (10627)Memory used [KB]: 10746
% 1.68/0.58  % (10627)Time elapsed: 0.170 s
% 1.68/0.58  % (10627)------------------------------
% 1.68/0.58  % (10627)------------------------------
% 1.68/0.58  % (10605)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.58  
% 1.68/0.58  % (10605)Memory used [KB]: 6268
% 1.68/0.58  % (10605)Time elapsed: 0.148 s
% 1.68/0.58  % (10605)------------------------------
% 1.68/0.58  % (10605)------------------------------
% 1.68/0.58  % (10613)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.68/0.58  % (10606)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.68/0.58  % (10630)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.68/0.59  % (10630)Refutation not found, incomplete strategy% (10630)------------------------------
% 1.68/0.59  % (10630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (10630)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (10630)Memory used [KB]: 1791
% 1.68/0.59  % (10630)Time elapsed: 0.171 s
% 1.68/0.59  % (10630)------------------------------
% 1.68/0.59  % (10630)------------------------------
% 1.68/0.59  % (10621)Refutation not found, incomplete strategy% (10621)------------------------------
% 1.68/0.59  % (10621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (10621)Termination reason: Refutation not found, incomplete strategy
% 1.68/0.59  
% 1.68/0.59  % (10621)Memory used [KB]: 1663
% 1.68/0.59  % (10621)Time elapsed: 0.159 s
% 1.68/0.59  % (10621)------------------------------
% 1.68/0.59  % (10621)------------------------------
% 1.68/0.59  % SZS status CounterSatisfiable for theBenchmark
% 1.68/0.59  % (10606)# SZS output start Saturation.
% 1.68/0.59  cnf(u40,axiom,
% 1.68/0.59      m1_subset_1(X0,k1_zfmisc_1(X0))).
% 1.68/0.59  
% 1.68/0.59  cnf(u25,axiom,
% 1.68/0.59      m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))).
% 1.68/0.59  
% 1.68/0.59  cnf(u22,negated_conjecture,
% 1.68/0.59      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 1.68/0.59  
% 1.68/0.59  cnf(u31,axiom,
% 1.68/0.59      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1).
% 1.68/0.59  
% 1.68/0.59  cnf(u55,axiom,
% 1.68/0.59      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k7_subset_1(X0,X0,X1)).
% 1.68/0.59  
% 1.68/0.59  cnf(u54,axiom,
% 1.68/0.59      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k7_subset_1(X1,X1,X2)).
% 1.68/0.59  
% 1.68/0.59  cnf(u41,negated_conjecture,
% 1.68/0.59      sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))).
% 1.68/0.59  
% 1.68/0.59  cnf(u79,axiom,
% 1.68/0.59      k7_subset_1(X0,X0,k1_xboole_0) = X0).
% 1.68/0.59  
% 1.68/0.59  cnf(u52,axiom,
% 1.68/0.59      k7_subset_1(X1,k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X2)))).
% 1.68/0.59  
% 1.68/0.59  cnf(u57,axiom,
% 1.68/0.59      k7_subset_1(X1,k1_xboole_0,X0) = k7_subset_1(X2,k1_xboole_0,X0)).
% 1.68/0.59  
% 1.68/0.59  cnf(u56,negated_conjecture,
% 1.68/0.59      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k7_subset_1(sK1,sK1,X0)).
% 1.68/0.59  
% 1.68/0.59  cnf(u76,negated_conjecture,
% 1.68/0.59      k3_subset_1(u1_struct_0(sK0),sK1) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)).
% 1.68/0.59  
% 1.68/0.59  cnf(u46,negated_conjecture,
% 1.68/0.59      k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))).
% 1.68/0.59  
% 1.68/0.59  cnf(u35,axiom,
% 1.68/0.59      k3_subset_1(X0,k1_xboole_0) = X0).
% 1.68/0.59  
% 1.68/0.59  cnf(u50,axiom,
% 1.68/0.59      k1_xboole_0 = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X1)))).
% 1.68/0.59  
% 1.68/0.59  cnf(u44,axiom,
% 1.68/0.59      k1_xboole_0 = k3_subset_1(X0,X0)).
% 1.68/0.59  
% 1.68/0.59  cnf(u80,axiom,
% 1.68/0.59      k1_xboole_0 = k7_subset_1(X1,X1,X1)).
% 1.68/0.59  
% 1.68/0.59  cnf(u58,axiom,
% 1.68/0.59      k1_xboole_0 = k7_subset_1(X3,k1_xboole_0,k1_xboole_0)).
% 1.68/0.59  
% 1.68/0.59  cnf(u20,negated_conjecture,
% 1.68/0.59      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 1.68/0.59  
% 1.68/0.59  cnf(u53,axiom,
% 1.68/0.59      k7_subset_1(X3,X3,X4) = k5_xboole_0(X3,k1_setfam_1(k2_tarski(X3,X4)))).
% 1.68/0.59  
% 1.68/0.59  cnf(u49,axiom,
% 1.68/0.59      k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0).
% 1.68/0.59  
% 1.68/0.59  cnf(u39,negated_conjecture,
% 1.68/0.59      sK1 != k2_struct_0(sK0) | k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),sK1,sK1)).
% 1.68/0.59  
% 1.68/0.59  % (10606)# SZS output end Saturation.
% 1.68/0.59  % (10606)------------------------------
% 1.68/0.59  % (10606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.68/0.59  % (10606)Termination reason: Satisfiable
% 1.68/0.59  
% 1.68/0.59  % (10606)Memory used [KB]: 6268
% 1.68/0.59  % (10606)Time elapsed: 0.093 s
% 1.68/0.59  % (10606)------------------------------
% 1.68/0.59  % (10606)------------------------------
% 1.68/0.60  % (10603)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.68/0.60  % (10602)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.68/0.60  % (10608)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.68/0.60  % (10599)Success in time 0.241 s
%------------------------------------------------------------------------------
