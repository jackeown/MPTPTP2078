%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:37 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u10,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u12,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u11,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u8,negated_conjecture,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1) )).

cnf(u9,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (8722)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.45  % (8722)Refutation not found, incomplete strategy% (8722)------------------------------
% 0.22/0.45  % (8722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (8722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (8722)Memory used [KB]: 10490
% 0.22/0.45  % (8722)Time elapsed: 0.042 s
% 0.22/0.45  % (8722)------------------------------
% 0.22/0.45  % (8722)------------------------------
% 0.22/0.47  % (8720)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (8719)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (8720)Refutation not found, incomplete strategy% (8720)------------------------------
% 0.22/0.47  % (8720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (8720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (8720)Memory used [KB]: 10490
% 0.22/0.47  % (8720)Time elapsed: 0.058 s
% 0.22/0.47  % (8720)------------------------------
% 0.22/0.47  % (8720)------------------------------
% 0.22/0.47  % (8719)Refutation not found, incomplete strategy% (8719)------------------------------
% 0.22/0.47  % (8719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (8719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (8719)Memory used [KB]: 6140
% 0.22/0.47  % (8719)Time elapsed: 0.041 s
% 0.22/0.47  % (8719)------------------------------
% 0.22/0.47  % (8719)------------------------------
% 0.22/0.48  % (8737)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (8737)Refutation not found, incomplete strategy% (8737)------------------------------
% 0.22/0.48  % (8737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8737)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (8737)Memory used [KB]: 1535
% 0.22/0.48  % (8737)Time elapsed: 0.071 s
% 0.22/0.48  % (8737)------------------------------
% 0.22/0.48  % (8737)------------------------------
% 0.22/0.49  % (8723)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (8735)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (8734)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (8723)Refutation not found, incomplete strategy% (8723)------------------------------
% 0.22/0.49  % (8723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8723)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8723)Memory used [KB]: 1535
% 0.22/0.49  % (8723)Time elapsed: 0.061 s
% 0.22/0.49  % (8723)------------------------------
% 0.22/0.49  % (8723)------------------------------
% 0.22/0.49  % (8734)Refutation not found, incomplete strategy% (8734)------------------------------
% 0.22/0.49  % (8734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8734)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8734)Memory used [KB]: 6012
% 0.22/0.49  % (8734)Time elapsed: 0.066 s
% 0.22/0.49  % (8734)------------------------------
% 0.22/0.49  % (8734)------------------------------
% 0.22/0.49  % (8725)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (8732)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (8728)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (8735)Refutation not found, incomplete strategy% (8735)------------------------------
% 0.22/0.49  % (8735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8735)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8735)Memory used [KB]: 10618
% 0.22/0.49  % (8735)Time elapsed: 0.062 s
% 0.22/0.49  % (8735)------------------------------
% 0.22/0.49  % (8735)------------------------------
% 0.22/0.49  % (8732)Refutation not found, incomplete strategy% (8732)------------------------------
% 0.22/0.49  % (8732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8732)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8732)Memory used [KB]: 1535
% 0.22/0.49  % (8732)Time elapsed: 0.061 s
% 0.22/0.49  % (8732)------------------------------
% 0.22/0.49  % (8732)------------------------------
% 0.22/0.49  % (8721)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (8728)Refutation not found, incomplete strategy% (8728)------------------------------
% 0.22/0.49  % (8728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8728)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8728)Memory used [KB]: 10490
% 0.22/0.49  % (8728)Time elapsed: 0.079 s
% 0.22/0.49  % (8728)------------------------------
% 0.22/0.49  % (8728)------------------------------
% 0.22/0.49  % (8726)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (8721)Refutation not found, incomplete strategy% (8721)------------------------------
% 0.22/0.49  % (8721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8721)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8721)Memory used [KB]: 10490
% 0.22/0.49  % (8721)Time elapsed: 0.070 s
% 0.22/0.49  % (8721)------------------------------
% 0.22/0.49  % (8721)------------------------------
% 0.22/0.49  % (8727)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.50  % (8724)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (8739)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (8729)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (8739)Refutation not found, incomplete strategy% (8739)------------------------------
% 0.22/0.50  % (8739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8729)Refutation not found, incomplete strategy% (8729)------------------------------
% 0.22/0.50  % (8729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8729)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8729)Memory used [KB]: 6012
% 0.22/0.50  % (8729)Time elapsed: 0.081 s
% 0.22/0.50  % (8729)------------------------------
% 0.22/0.50  % (8729)------------------------------
% 0.22/0.50  % (8739)Memory used [KB]: 10490
% 0.22/0.50  % (8739)Time elapsed: 0.078 s
% 0.22/0.50  % (8739)------------------------------
% 0.22/0.50  % (8739)------------------------------
% 0.22/0.50  % (8733)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (8731)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (8725)Refutation not found, incomplete strategy% (8725)------------------------------
% 0.22/0.50  % (8725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8725)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8725)Memory used [KB]: 10490
% 0.22/0.50  % (8725)Time elapsed: 0.078 s
% 0.22/0.50  % (8725)------------------------------
% 0.22/0.50  % (8725)------------------------------
% 0.22/0.50  % (8731)Refutation not found, incomplete strategy% (8731)------------------------------
% 0.22/0.50  % (8731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8731)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8731)Memory used [KB]: 6012
% 0.22/0.50  % (8731)Time elapsed: 0.087 s
% 0.22/0.50  % (8731)------------------------------
% 0.22/0.50  % (8731)------------------------------
% 0.22/0.50  % (8736)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (8730)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (8736)# SZS output start Saturation.
% 0.22/0.50  cnf(u10,axiom,
% 0.22/0.50      v1_xboole_0(k1_xboole_0)).
% 0.22/0.50  
% 0.22/0.50  cnf(u12,axiom,
% 0.22/0.50      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.22/0.50  
% 0.22/0.50  cnf(u11,axiom,
% 0.22/0.50      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.50  
% 0.22/0.50  cnf(u8,negated_conjecture,
% 0.22/0.50      k1_xboole_0 = k2_xboole_0(sK0,sK1)).
% 0.22/0.50  
% 0.22/0.50  cnf(u9,negated_conjecture,
% 0.22/0.50      k1_xboole_0 != sK0).
% 0.22/0.50  
% 0.22/0.50  % (8736)# SZS output end Saturation.
% 0.22/0.50  % (8736)------------------------------
% 0.22/0.50  % (8736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8736)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (8736)Memory used [KB]: 1535
% 0.22/0.50  % (8736)Time elapsed: 0.088 s
% 0.22/0.50  % (8736)------------------------------
% 0.22/0.50  % (8736)------------------------------
% 0.22/0.50  % (8718)Success in time 0.132 s
%------------------------------------------------------------------------------
