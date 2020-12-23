%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:36 EST 2020

% Result     : CounterSatisfiable 1.55s
% Output     : Saturation 1.55s
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

cnf(u11,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u12,axiom,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

cnf(u8,negated_conjecture,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1) )).

cnf(u9,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:28:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (9389)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (9397)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (9397)Refutation not found, incomplete strategy% (9397)------------------------------
% 0.22/0.49  % (9397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9397)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (9397)Memory used [KB]: 1535
% 0.22/0.49  % (9397)Time elapsed: 0.074 s
% 0.22/0.49  % (9397)------------------------------
% 0.22/0.49  % (9397)------------------------------
% 0.22/0.50  % (9394)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (9394)Refutation not found, incomplete strategy% (9394)------------------------------
% 0.22/0.50  % (9394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (9394)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (9394)Memory used [KB]: 6012
% 0.22/0.50  % (9394)Time elapsed: 0.071 s
% 0.22/0.50  % (9394)------------------------------
% 0.22/0.50  % (9394)------------------------------
% 0.22/0.50  % (9403)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  % (9403)Refutation not found, incomplete strategy% (9403)------------------------------
% 0.22/0.51  % (9403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9390)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (9403)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9403)Memory used [KB]: 6012
% 0.22/0.51  % (9403)Time elapsed: 0.076 s
% 0.22/0.51  % (9403)------------------------------
% 0.22/0.51  % (9403)------------------------------
% 0.22/0.51  % (9386)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (9399)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (9390)Refutation not found, incomplete strategy% (9390)------------------------------
% 0.22/0.51  % (9390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9390)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9390)Memory used [KB]: 10490
% 0.22/0.51  % (9390)Time elapsed: 0.086 s
% 0.22/0.51  % (9390)------------------------------
% 0.22/0.51  % (9390)------------------------------
% 0.22/0.51  % (9386)Refutation not found, incomplete strategy% (9386)------------------------------
% 0.22/0.51  % (9386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9386)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9399)Refutation not found, incomplete strategy% (9399)------------------------------
% 0.22/0.51  % (9399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9399)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9399)Memory used [KB]: 6012
% 0.22/0.51  % (9399)Time elapsed: 0.043 s
% 0.22/0.51  % (9399)------------------------------
% 0.22/0.51  % (9399)------------------------------
% 0.22/0.51  % (9386)Memory used [KB]: 10490
% 0.22/0.51  % (9386)Time elapsed: 0.079 s
% 0.22/0.51  % (9386)------------------------------
% 0.22/0.51  % (9386)------------------------------
% 0.22/0.51  % (9395)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (9395)Refutation not found, incomplete strategy% (9395)------------------------------
% 0.22/0.51  % (9395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9395)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (9395)Memory used [KB]: 10490
% 0.22/0.51  % (9395)Time elapsed: 0.085 s
% 0.22/0.51  % (9395)------------------------------
% 0.22/0.51  % (9395)------------------------------
% 0.22/0.52  % (9391)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (9398)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % (9400)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (9404)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (9400)Refutation not found, incomplete strategy% (9400)------------------------------
% 0.22/0.52  % (9400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9400)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9400)Memory used [KB]: 10490
% 0.22/0.52  % (9400)Time elapsed: 0.098 s
% 0.22/0.52  % (9400)------------------------------
% 0.22/0.52  % (9400)------------------------------
% 0.22/0.52  % (9404)Refutation not found, incomplete strategy% (9404)------------------------------
% 0.22/0.52  % (9404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (9404)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (9404)Memory used [KB]: 10490
% 0.22/0.52  % (9404)Time elapsed: 0.097 s
% 0.22/0.52  % (9404)------------------------------
% 0.22/0.52  % (9404)------------------------------
% 0.22/0.53  % (9393)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.53  % (9393)Refutation not found, incomplete strategy% (9393)------------------------------
% 0.22/0.53  % (9393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9393)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9393)Memory used [KB]: 10490
% 0.22/0.53  % (9393)Time elapsed: 0.104 s
% 0.22/0.53  % (9393)------------------------------
% 0.22/0.53  % (9393)------------------------------
% 0.22/0.53  % (9388)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (9388)Refutation not found, incomplete strategy% (9388)------------------------------
% 0.22/0.53  % (9388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9388)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9388)Memory used [KB]: 1535
% 0.22/0.53  % (9388)Time elapsed: 0.103 s
% 0.22/0.53  % (9388)------------------------------
% 0.22/0.53  % (9388)------------------------------
% 0.22/0.53  % (9387)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (9387)Refutation not found, incomplete strategy% (9387)------------------------------
% 0.22/0.53  % (9387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (9387)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (9387)Memory used [KB]: 10490
% 0.22/0.53  % (9387)Time elapsed: 0.103 s
% 0.22/0.53  % (9387)------------------------------
% 0.22/0.53  % (9387)------------------------------
% 0.22/0.54  % (9396)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (9384)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (9396)Refutation not found, incomplete strategy% (9396)------------------------------
% 0.22/0.54  % (9396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9396)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9396)Memory used [KB]: 6012
% 0.22/0.54  % (9396)Time elapsed: 0.111 s
% 0.22/0.54  % (9396)------------------------------
% 0.22/0.54  % (9396)------------------------------
% 0.22/0.54  % (9384)Refutation not found, incomplete strategy% (9384)------------------------------
% 0.22/0.54  % (9384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9384)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9384)Memory used [KB]: 6140
% 0.22/0.54  % (9384)Time elapsed: 0.114 s
% 0.22/0.54  % (9384)------------------------------
% 0.22/0.54  % (9384)------------------------------
% 0.22/0.54  % (9392)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.54  % (9402)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.54  % (9402)Refutation not found, incomplete strategy% (9402)------------------------------
% 0.22/0.54  % (9402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9402)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9402)Memory used [KB]: 1535
% 0.22/0.54  % (9402)Time elapsed: 0.114 s
% 0.22/0.54  % (9402)------------------------------
% 0.22/0.54  % (9402)------------------------------
% 0.22/0.55  % (9385)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.55  % (9385)Refutation not found, incomplete strategy% (9385)------------------------------
% 1.55/0.55  % (9385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.55  % (9385)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.55  
% 1.55/0.55  % (9385)Memory used [KB]: 10490
% 1.55/0.55  % (9385)Time elapsed: 0.123 s
% 1.55/0.55  % (9385)------------------------------
% 1.55/0.55  % (9385)------------------------------
% 1.55/0.55  % (9401)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.55/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.55/0.55  % (9401)# SZS output start Saturation.
% 1.55/0.55  cnf(u10,axiom,
% 1.55/0.55      v1_xboole_0(k1_xboole_0)).
% 1.55/0.55  
% 1.55/0.55  cnf(u11,axiom,
% 1.55/0.55      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 1.55/0.55  
% 1.55/0.55  cnf(u12,axiom,
% 1.55/0.55      k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)).
% 1.55/0.55  
% 1.55/0.55  cnf(u8,negated_conjecture,
% 1.55/0.55      k1_xboole_0 = k2_xboole_0(sK0,sK1)).
% 1.55/0.55  
% 1.55/0.55  cnf(u9,negated_conjecture,
% 1.55/0.55      k1_xboole_0 != sK0).
% 1.55/0.55  
% 1.55/0.55  % (9401)# SZS output end Saturation.
% 1.55/0.55  % (9401)------------------------------
% 1.55/0.55  % (9401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.55  % (9401)Termination reason: Satisfiable
% 1.55/0.55  
% 1.55/0.55  % (9401)Memory used [KB]: 1535
% 1.55/0.55  % (9401)Time elapsed: 0.129 s
% 1.55/0.55  % (9401)------------------------------
% 1.55/0.55  % (9401)------------------------------
% 1.55/0.55  % (9383)Success in time 0.186 s
%------------------------------------------------------------------------------
