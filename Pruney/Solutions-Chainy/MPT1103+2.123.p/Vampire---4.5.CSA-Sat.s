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
% DateTime   : Thu Dec  3 13:08:50 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u14,negated_conjecture,
    ( l1_struct_0(sK0) )).

cnf(u13,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

cnf(u17,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_struct_0(X0)
    | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 )).

cnf(u19,axiom,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) )).

cnf(u25,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0)
    | sK1 = k2_struct_0(sK0) )).

cnf(u24,negated_conjecture,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) )).

cnf(u11,negated_conjecture,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 = k2_struct_0(sK0) )).

cnf(u22,negated_conjecture,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

cnf(u20,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u18,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

cnf(u16,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u15,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u12,negated_conjecture,
    ( k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)
    | sK1 != k2_struct_0(sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:33:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (7542)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.46  % (7558)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.46  % (7542)Refutation not found, incomplete strategy% (7542)------------------------------
% 0.22/0.46  % (7542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (7542)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (7542)Memory used [KB]: 10618
% 0.22/0.46  % (7542)Time elapsed: 0.049 s
% 0.22/0.46  % (7542)------------------------------
% 0.22/0.46  % (7542)------------------------------
% 0.22/0.47  % (7544)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (7544)Refutation not found, incomplete strategy% (7544)------------------------------
% 0.22/0.47  % (7544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7558)Refutation not found, incomplete strategy% (7558)------------------------------
% 0.22/0.48  % (7558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7558)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7558)Memory used [KB]: 1663
% 0.22/0.48  % (7558)Time elapsed: 0.070 s
% 0.22/0.48  % (7558)------------------------------
% 0.22/0.48  % (7558)------------------------------
% 0.22/0.48  % (7549)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (7549)Refutation not found, incomplete strategy% (7549)------------------------------
% 0.22/0.48  % (7549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7549)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7549)Memory used [KB]: 10618
% 0.22/0.48  % (7549)Time elapsed: 0.080 s
% 0.22/0.48  % (7549)------------------------------
% 0.22/0.48  % (7549)------------------------------
% 0.22/0.48  % (7552)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (7552)Refutation not found, incomplete strategy% (7552)------------------------------
% 0.22/0.48  % (7552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7552)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7552)Memory used [KB]: 6012
% 0.22/0.48  % (7552)Time elapsed: 0.003 s
% 0.22/0.48  % (7552)------------------------------
% 0.22/0.48  % (7552)------------------------------
% 0.22/0.48  % (7544)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7544)Memory used [KB]: 1663
% 0.22/0.48  % (7544)Time elapsed: 0.050 s
% 0.22/0.48  % (7544)------------------------------
% 0.22/0.48  % (7544)------------------------------
% 0.22/0.49  % (7553)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (7553)Refutation not found, incomplete strategy% (7553)------------------------------
% 0.22/0.49  % (7553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7553)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (7553)Memory used [KB]: 1663
% 0.22/0.49  % (7553)Time elapsed: 0.035 s
% 0.22/0.49  % (7553)------------------------------
% 0.22/0.49  % (7553)------------------------------
% 0.22/0.50  % (7551)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (7547)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (7551)Refutation not found, incomplete strategy% (7551)------------------------------
% 0.22/0.50  % (7551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7551)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7551)Memory used [KB]: 10618
% 0.22/0.50  % (7551)Time elapsed: 0.066 s
% 0.22/0.50  % (7551)------------------------------
% 0.22/0.50  % (7551)------------------------------
% 0.22/0.50  % (7545)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (7550)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (7560)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (7550)Refutation not found, incomplete strategy% (7550)------------------------------
% 0.22/0.50  % (7550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7550)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7550)Memory used [KB]: 6140
% 0.22/0.50  % (7550)Time elapsed: 0.085 s
% 0.22/0.50  % (7550)------------------------------
% 0.22/0.50  % (7550)------------------------------
% 0.22/0.50  % (7560)Refutation not found, incomplete strategy% (7560)------------------------------
% 0.22/0.50  % (7560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7560)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7560)Memory used [KB]: 10490
% 0.22/0.50  % (7560)Time elapsed: 0.068 s
% 0.22/0.50  % (7560)------------------------------
% 0.22/0.50  % (7560)------------------------------
% 0.22/0.50  % (7543)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (7543)Refutation not found, incomplete strategy% (7543)------------------------------
% 0.22/0.50  % (7543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7543)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7543)Memory used [KB]: 10618
% 0.22/0.50  % (7543)Time elapsed: 0.090 s
% 0.22/0.50  % (7543)------------------------------
% 0.22/0.50  % (7543)------------------------------
% 0.22/0.50  % (7541)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (7555)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (7540)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (7555)Refutation not found, incomplete strategy% (7555)------------------------------
% 0.22/0.51  % (7555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7555)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7555)Memory used [KB]: 6140
% 0.22/0.51  % (7555)Time elapsed: 0.098 s
% 0.22/0.51  % (7555)------------------------------
% 0.22/0.51  % (7555)------------------------------
% 0.22/0.51  % (7554)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (7540)Refutation not found, incomplete strategy% (7540)------------------------------
% 0.22/0.51  % (7540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7540)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7540)Memory used [KB]: 6140
% 0.22/0.51  % (7540)Time elapsed: 0.093 s
% 0.22/0.51  % (7540)------------------------------
% 0.22/0.51  % (7540)------------------------------
% 0.22/0.51  % (7541)Refutation not found, incomplete strategy% (7541)------------------------------
% 0.22/0.51  % (7541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7541)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (7541)Memory used [KB]: 10618
% 0.22/0.51  % (7541)Time elapsed: 0.094 s
% 0.22/0.51  % (7541)------------------------------
% 0.22/0.51  % (7541)------------------------------
% 0.22/0.51  % (7557)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.51  % (7557)# SZS output start Saturation.
% 0.22/0.51  cnf(u14,negated_conjecture,
% 0.22/0.51      l1_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u13,negated_conjecture,
% 0.22/0.51      m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))).
% 0.22/0.51  
% 0.22/0.51  cnf(u17,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1).
% 0.22/0.51  
% 0.22/0.51  cnf(u19,axiom,
% 0.22/0.51      ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)).
% 0.22/0.51  
% 0.22/0.51  cnf(u25,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k1_xboole_0) | sK1 = k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u24,negated_conjecture,
% 0.22/0.51      sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u11,negated_conjecture,
% 0.22/0.51      k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 = k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u22,negated_conjecture,
% 0.22/0.51      k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u20,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.22/0.51  
% 0.22/0.51  cnf(u18,axiom,
% 0.22/0.51      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 0.22/0.51  
% 0.22/0.51  cnf(u16,axiom,
% 0.22/0.51      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u15,axiom,
% 0.22/0.51      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.51  
% 0.22/0.51  cnf(u12,negated_conjecture,
% 0.22/0.51      k1_xboole_0 != k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) | sK1 != k2_struct_0(sK0)).
% 0.22/0.51  
% 0.22/0.51  % (7557)# SZS output end Saturation.
% 0.22/0.51  % (7557)------------------------------
% 0.22/0.51  % (7557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7557)Termination reason: Satisfiable
% 0.22/0.51  
% 0.22/0.51  % (7557)Memory used [KB]: 1663
% 0.22/0.51  % (7557)Time elapsed: 0.095 s
% 0.22/0.51  % (7557)------------------------------
% 0.22/0.51  % (7557)------------------------------
% 0.22/0.51  % (7539)Success in time 0.147 s
%------------------------------------------------------------------------------
