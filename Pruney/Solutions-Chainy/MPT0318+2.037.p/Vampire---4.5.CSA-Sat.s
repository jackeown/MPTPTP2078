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
% DateTime   : Thu Dec  3 12:42:21 EST 2020

% Result     : CounterSatisfiable 1.40s
% Output     : Saturation 1.40s
% Verified   : 
% Statistics : Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    7 (   7 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u31,negated_conjecture,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) )).

cnf(u22,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) )).

cnf(u21,axiom,
    ( k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) )).

cnf(u14,axiom,
    ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 )).

cnf(u11,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (3011)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.48  % (3003)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.48  % (3011)Refutation not found, incomplete strategy% (3011)------------------------------
% 0.21/0.48  % (3011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3003)Refutation not found, incomplete strategy% (3003)------------------------------
% 0.21/0.48  % (3003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3011)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3011)Memory used [KB]: 1663
% 0.21/0.48  % (3011)Time elapsed: 0.069 s
% 0.21/0.48  % (3011)------------------------------
% 0.21/0.48  % (3011)------------------------------
% 0.21/0.48  % (3003)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3003)Memory used [KB]: 1663
% 0.21/0.48  % (3003)Time elapsed: 0.069 s
% 0.21/0.48  % (3003)------------------------------
% 0.21/0.48  % (3003)------------------------------
% 0.21/0.51  % (2990)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (2982)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (2982)Refutation not found, incomplete strategy% (2982)------------------------------
% 0.21/0.51  % (2982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2982)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2982)Memory used [KB]: 1663
% 0.21/0.51  % (2982)Time elapsed: 0.097 s
% 0.21/0.51  % (2982)------------------------------
% 0.21/0.51  % (2982)------------------------------
% 0.21/0.51  % (2996)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (2995)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (2993)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (2987)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (2991)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (2992)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (2987)Refutation not found, incomplete strategy% (2987)------------------------------
% 0.21/0.52  % (2987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2987)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2987)Memory used [KB]: 6140
% 0.21/0.52  % (2987)Time elapsed: 0.107 s
% 0.21/0.52  % (2987)------------------------------
% 0.21/0.52  % (2987)------------------------------
% 0.21/0.52  % (3004)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (3004)Refutation not found, incomplete strategy% (3004)------------------------------
% 0.21/0.52  % (3004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3004)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3004)Memory used [KB]: 10618
% 0.21/0.52  % (3004)Time elapsed: 0.094 s
% 0.21/0.52  % (3004)------------------------------
% 0.21/0.52  % (3004)------------------------------
% 0.21/0.53  % (3001)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (3001)Refutation not found, incomplete strategy% (3001)------------------------------
% 0.21/0.53  % (3001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3001)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3001)Memory used [KB]: 10618
% 0.21/0.53  % (3001)Time elapsed: 0.124 s
% 0.21/0.53  % (3001)------------------------------
% 0.21/0.53  % (3001)------------------------------
% 0.21/0.53  % (2990)Refutation not found, incomplete strategy% (2990)------------------------------
% 0.21/0.53  % (2990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (2990)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (2990)Memory used [KB]: 10618
% 0.21/0.53  % (2990)Time elapsed: 0.098 s
% 0.21/0.53  % (2990)------------------------------
% 0.21/0.53  % (2990)------------------------------
% 0.21/0.53  % (2986)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (2983)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (2994)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (2999)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (3000)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (3005)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (2984)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (2985)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (3005)Refutation not found, incomplete strategy% (3005)------------------------------
% 0.21/0.53  % (3005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3005)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3005)Memory used [KB]: 1663
% 0.21/0.53  % (3005)Time elapsed: 0.131 s
% 0.21/0.53  % (3005)------------------------------
% 0.21/0.53  % (3005)------------------------------
% 0.21/0.54  % (2984)Refutation not found, incomplete strategy% (2984)------------------------------
% 0.21/0.54  % (2984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2984)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2984)Memory used [KB]: 10618
% 0.21/0.54  % (2984)Time elapsed: 0.128 s
% 0.21/0.54  % (2984)------------------------------
% 0.21/0.54  % (2984)------------------------------
% 0.21/0.54  % (2985)Refutation not found, incomplete strategy% (2985)------------------------------
% 0.21/0.54  % (2985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2985)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2985)Memory used [KB]: 10618
% 0.21/0.54  % (2985)Time elapsed: 0.128 s
% 0.21/0.54  % (2985)------------------------------
% 0.21/0.54  % (2985)------------------------------
% 0.21/0.54  % (2997)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (2989)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.40/0.54  % (3006)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.54  % (3009)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.54  % (3010)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  % (3002)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.40/0.54  % (3002)Refutation not found, incomplete strategy% (3002)------------------------------
% 1.40/0.54  % (3002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (2988)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.54  % (2989)Refutation not found, incomplete strategy% (2989)------------------------------
% 1.40/0.54  % (2989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (2989)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (2989)Memory used [KB]: 6140
% 1.40/0.54  % (2989)Time elapsed: 0.142 s
% 1.40/0.54  % (2989)------------------------------
% 1.40/0.54  % (2989)------------------------------
% 1.40/0.54  % (3008)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.54  % (3007)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.40/0.55  % (2998)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.40/0.55  % (2994)Refutation not found, incomplete strategy% (2994)------------------------------
% 1.40/0.55  % (2994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (2994)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (2994)Memory used [KB]: 6140
% 1.40/0.55  % (2994)Time elapsed: 0.143 s
% 1.40/0.55  % (2994)------------------------------
% 1.40/0.55  % (2994)------------------------------
% 1.40/0.55  % (2988)# SZS output start Saturation.
% 1.40/0.55  cnf(u31,negated_conjecture,
% 1.40/0.55      k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u22,axiom,
% 1.40/0.55      k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)).
% 1.40/0.55  
% 1.40/0.55  cnf(u21,axiom,
% 1.40/0.55      k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)).
% 1.40/0.55  
% 1.40/0.55  cnf(u14,axiom,
% 1.40/0.55      k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0).
% 1.40/0.55  
% 1.40/0.55  cnf(u11,negated_conjecture,
% 1.40/0.55      k1_xboole_0 != sK0).
% 1.40/0.55  
% 1.40/0.55  % (2988)# SZS output end Saturation.
% 1.40/0.55  % (2988)------------------------------
% 1.40/0.55  % (2988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (2988)Termination reason: Satisfiable
% 1.40/0.55  
% 1.40/0.55  % (2988)Memory used [KB]: 6140
% 1.40/0.55  % (2988)Time elapsed: 0.117 s
% 1.40/0.55  % (2988)------------------------------
% 1.40/0.55  % (2988)------------------------------
% 1.40/0.55  % (3002)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (3002)Memory used [KB]: 10618
% 1.40/0.55  % (3002)Time elapsed: 0.143 s
% 1.40/0.55  % (3002)------------------------------
% 1.40/0.55  % (3002)------------------------------
% 1.40/0.55  % (2981)Success in time 0.184 s
%------------------------------------------------------------------------------
