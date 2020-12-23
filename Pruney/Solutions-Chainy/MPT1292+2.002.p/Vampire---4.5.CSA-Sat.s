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
% DateTime   : Thu Dec  3 13:13:11 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   33 (  33 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u24,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u23,negated_conjecture,
    ( ~ v2_struct_0(sK0) )).

cnf(u44,negated_conjecture,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) )).

cnf(u37,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )).

cnf(u40,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(X1) )).

cnf(u41,axiom,
    ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X3) )).

cnf(u28,axiom,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X2) )).

cnf(u39,negated_conjecture,
    ( r1_tarski(u1_struct_0(sK0),k1_xboole_0) )).

cnf(u30,axiom,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) )).

cnf(u36,negated_conjecture,
    ( m1_setfam_1(k1_xboole_0,u1_struct_0(sK0)) )).

cnf(u29,axiom,
    ( ~ m1_setfam_1(X1,X0)
    | r1_tarski(X0,k3_tarski(X1)) )).

cnf(u27,axiom,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0)
    | v2_struct_0(X0) )).

cnf(u26,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u45,negated_conjecture,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK0)) )).

cnf(u35,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) )).

cnf(u34,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) )).

cnf(u25,axiom,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0) )).

cnf(u22,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u31,axiom,
    ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:39:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (30153)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (30164)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (30162)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (30163)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (30162)Refutation not found, incomplete strategy% (30162)------------------------------
% 0.21/0.49  % (30162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30162)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30162)Memory used [KB]: 1535
% 0.21/0.49  % (30162)Time elapsed: 0.070 s
% 0.21/0.49  % (30162)------------------------------
% 0.21/0.49  % (30162)------------------------------
% 0.21/0.49  % (30151)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (30164)Refutation not found, incomplete strategy% (30164)------------------------------
% 0.21/0.49  % (30164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (30164)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (30164)Memory used [KB]: 6140
% 0.21/0.49  % (30164)Time elapsed: 0.004 s
% 0.21/0.49  % (30164)------------------------------
% 0.21/0.49  % (30164)------------------------------
% 0.21/0.49  % (30156)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (30155)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (30155)Refutation not found, incomplete strategy% (30155)------------------------------
% 0.21/0.50  % (30155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30155)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (30155)Memory used [KB]: 10618
% 0.21/0.50  % (30155)Time elapsed: 0.067 s
% 0.21/0.50  % (30155)------------------------------
% 0.21/0.50  % (30155)------------------------------
% 0.21/0.50  % (30169)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (30149)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (30166)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (30149)Refutation not found, incomplete strategy% (30149)------------------------------
% 0.21/0.51  % (30149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30149)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30149)Memory used [KB]: 6140
% 0.21/0.51  % (30149)Time elapsed: 0.092 s
% 0.21/0.51  % (30149)------------------------------
% 0.21/0.51  % (30149)------------------------------
% 0.21/0.51  % (30154)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (30152)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (30150)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (30154)Refutation not found, incomplete strategy% (30154)------------------------------
% 0.21/0.51  % (30154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30154)Memory used [KB]: 6140
% 0.21/0.51  % (30154)Time elapsed: 0.095 s
% 0.21/0.51  % (30154)------------------------------
% 0.21/0.51  % (30154)------------------------------
% 0.21/0.51  % (30152)Refutation not found, incomplete strategy% (30152)------------------------------
% 0.21/0.51  % (30152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30152)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30152)Memory used [KB]: 10618
% 0.21/0.51  % (30152)Time elapsed: 0.093 s
% 0.21/0.51  % (30152)------------------------------
% 0.21/0.51  % (30152)------------------------------
% 0.21/0.51  % (30150)Refutation not found, incomplete strategy% (30150)------------------------------
% 0.21/0.51  % (30150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30150)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30150)Memory used [KB]: 10618
% 0.21/0.51  % (30150)Time elapsed: 0.091 s
% 0.21/0.51  % (30150)------------------------------
% 0.21/0.51  % (30150)------------------------------
% 0.21/0.51  % (30161)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (30151)Refutation not found, incomplete strategy% (30151)------------------------------
% 0.21/0.51  % (30151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30151)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30151)Memory used [KB]: 10618
% 0.21/0.51  % (30151)Time elapsed: 0.095 s
% 0.21/0.51  % (30151)------------------------------
% 0.21/0.51  % (30151)------------------------------
% 0.21/0.51  % (30161)Refutation not found, incomplete strategy% (30161)------------------------------
% 0.21/0.51  % (30161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30161)Memory used [KB]: 6012
% 0.21/0.51  % (30161)Time elapsed: 0.001 s
% 0.21/0.51  % (30161)------------------------------
% 0.21/0.51  % (30161)------------------------------
% 0.21/0.51  % (30165)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (30169)Refutation not found, incomplete strategy% (30169)------------------------------
% 0.21/0.51  % (30169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30169)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30169)Memory used [KB]: 10490
% 0.21/0.51  % (30169)Time elapsed: 0.095 s
% 0.21/0.51  % (30169)------------------------------
% 0.21/0.51  % (30169)------------------------------
% 0.21/0.51  % (30167)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (30160)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (30158)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (30167)Refutation not found, incomplete strategy% (30167)------------------------------
% 0.21/0.51  % (30167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30167)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30167)Memory used [KB]: 1663
% 0.21/0.51  % (30167)Time elapsed: 0.097 s
% 0.21/0.51  % (30167)------------------------------
% 0.21/0.51  % (30167)------------------------------
% 0.21/0.51  % (30160)Refutation not found, incomplete strategy% (30160)------------------------------
% 0.21/0.51  % (30160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30160)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30160)Memory used [KB]: 10618
% 0.21/0.51  % (30160)Time elapsed: 0.098 s
% 0.21/0.51  % (30160)------------------------------
% 0.21/0.51  % (30160)------------------------------
% 0.21/0.51  % (30165)Refutation not found, incomplete strategy% (30165)------------------------------
% 0.21/0.51  % (30165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30165)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30165)Memory used [KB]: 10618
% 0.21/0.51  % (30165)Time elapsed: 0.098 s
% 0.21/0.51  % (30165)------------------------------
% 0.21/0.51  % (30165)------------------------------
% 0.21/0.51  % (30158)Refutation not found, incomplete strategy% (30158)------------------------------
% 0.21/0.51  % (30158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30158)Memory used [KB]: 10618
% 0.21/0.51  % (30158)Time elapsed: 0.098 s
% 0.21/0.51  % (30158)------------------------------
% 0.21/0.51  % (30158)------------------------------
% 0.21/0.52  % (30157)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.52  % (30159)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (30166)# SZS output start Saturation.
% 0.21/0.52  cnf(u24,negated_conjecture,
% 0.21/0.52      l1_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u23,negated_conjecture,
% 0.21/0.52      ~v2_struct_0(sK0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u44,negated_conjecture,
% 0.21/0.52      m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u37,negated_conjecture,
% 0.21/0.52      m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))).
% 0.21/0.52  
% 0.21/0.52  cnf(u40,axiom,
% 0.21/0.52      ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u41,axiom,
% 0.21/0.52      ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(X2) | v1_xboole_0(X3)).
% 0.21/0.52  
% 0.21/0.52  cnf(u28,axiom,
% 0.21/0.52      ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)).
% 0.21/0.52  
% 0.21/0.52  cnf(u39,negated_conjecture,
% 0.21/0.52      r1_tarski(u1_struct_0(sK0),k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u30,axiom,
% 0.21/0.52      ~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u36,negated_conjecture,
% 0.21/0.52      m1_setfam_1(k1_xboole_0,u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u29,axiom,
% 0.21/0.52      ~m1_setfam_1(X1,X0) | r1_tarski(X0,k3_tarski(X1))).
% 0.21/0.52  
% 0.21/0.52  cnf(u27,axiom,
% 0.21/0.52      ~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u26,axiom,
% 0.21/0.52      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.21/0.52  
% 0.21/0.52  cnf(u45,negated_conjecture,
% 0.21/0.52      ~v1_xboole_0(X0) | v1_xboole_0(u1_struct_0(sK0))).
% 0.21/0.52  
% 0.21/0.52  cnf(u35,axiom,
% 0.21/0.52      k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)).
% 0.21/0.52  
% 0.21/0.52  cnf(u34,axiom,
% 0.21/0.52      k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u25,axiom,
% 0.21/0.52      k1_xboole_0 = k3_tarski(k1_xboole_0)).
% 0.21/0.52  
% 0.21/0.52  cnf(u22,negated_conjecture,
% 0.21/0.52      k1_xboole_0 = sK1).
% 0.21/0.52  
% 0.21/0.52  cnf(u31,axiom,
% 0.21/0.52      k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0).
% 0.21/0.52  
% 0.21/0.52  % (30166)# SZS output end Saturation.
% 0.21/0.52  % (30166)------------------------------
% 0.21/0.52  % (30166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30166)Termination reason: Satisfiable
% 0.21/0.52  
% 0.21/0.52  % (30166)Memory used [KB]: 1663
% 0.21/0.52  % (30166)Time elapsed: 0.106 s
% 0.21/0.52  % (30166)------------------------------
% 0.21/0.52  % (30166)------------------------------
% 0.21/0.52  % (30168)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (30148)Success in time 0.154 s
%------------------------------------------------------------------------------
