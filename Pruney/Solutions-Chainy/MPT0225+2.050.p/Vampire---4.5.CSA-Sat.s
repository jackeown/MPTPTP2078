%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:12 EST 2020

% Result     : CounterSatisfiable 1.29s
% Output     : Saturation 1.29s
% Verified   : 
% Statistics : Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22346)Refutation not found, incomplete strategy% (22346)------------------------------
% (22346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22346)Termination reason: Refutation not found, incomplete strategy

% (22346)Memory used [KB]: 6268
% (22346)Time elapsed: 0.109 s
% (22346)------------------------------
% (22346)------------------------------
cnf(u43,axiom,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 )).

cnf(u44,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 )).

cnf(u48,axiom,
    ( r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )).

cnf(u49,axiom,
    ( r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )).

cnf(u47,axiom,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 )).

cnf(u56,negated_conjecture,
    ( sK0 = sK1 )).

cnf(u59,negated_conjecture,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )).

cnf(u51,axiom,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
    | X0 = X1 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (22350)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.46  % (22350)Refutation not found, incomplete strategy% (22350)------------------------------
% 0.21/0.46  % (22350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22350)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (22350)Memory used [KB]: 10618
% 0.21/0.47  % (22350)Time elapsed: 0.063 s
% 0.21/0.47  % (22350)------------------------------
% 0.21/0.47  % (22350)------------------------------
% 0.21/0.47  % (22342)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.48  % (22342)Refutation not found, incomplete strategy% (22342)------------------------------
% 0.21/0.48  % (22342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (22342)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (22342)Memory used [KB]: 10746
% 0.21/0.48  % (22342)Time elapsed: 0.073 s
% 0.21/0.48  % (22342)------------------------------
% 0.21/0.48  % (22342)------------------------------
% 0.21/0.48  % (22358)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.49  % (22358)Refutation not found, incomplete strategy% (22358)------------------------------
% 0.21/0.49  % (22358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (22358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (22358)Memory used [KB]: 10746
% 0.21/0.49  % (22358)Time elapsed: 0.084 s
% 0.21/0.49  % (22358)------------------------------
% 0.21/0.49  % (22358)------------------------------
% 0.21/0.50  % (22368)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (22368)Refutation not found, incomplete strategy% (22368)------------------------------
% 0.21/0.50  % (22368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22368)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22368)Memory used [KB]: 1663
% 0.21/0.50  % (22368)Time elapsed: 0.089 s
% 0.21/0.50  % (22368)------------------------------
% 0.21/0.50  % (22368)------------------------------
% 1.14/0.51  % (22344)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.14/0.51  % (22345)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.14/0.52  % (22339)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.14/0.52  % (22360)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.14/0.53  % (22362)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.53  % (22354)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.53  % (22365)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.53  % (22362)Refutation not found, incomplete strategy% (22362)------------------------------
% 1.29/0.53  % (22362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % SZS status CounterSatisfiable for theBenchmark
% 1.29/0.53  % (22354)Refutation not found, incomplete strategy% (22354)------------------------------
% 1.29/0.53  % (22354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (22340)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (22354)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (22354)Memory used [KB]: 6140
% 1.29/0.53  % (22354)Time elapsed: 0.004 s
% 1.29/0.53  % (22354)------------------------------
% 1.29/0.53  % (22354)------------------------------
% 1.29/0.53  % (22352)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.53  % (22363)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.53  % (22363)Refutation not found, incomplete strategy% (22363)------------------------------
% 1.29/0.53  % (22363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (22363)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (22363)Memory used [KB]: 6140
% 1.29/0.53  % (22363)Time elapsed: 0.118 s
% 1.29/0.53  % (22363)------------------------------
% 1.29/0.53  % (22363)------------------------------
% 1.29/0.53  % (22353)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (22344)Refutation not found, incomplete strategy% (22344)------------------------------
% 1.29/0.53  % (22344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (22344)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (22344)Memory used [KB]: 6268
% 1.29/0.53  % (22344)Time elapsed: 0.118 s
% 1.29/0.53  % (22344)------------------------------
% 1.29/0.53  % (22344)------------------------------
% 1.29/0.54  % (22339)Refutation not found, incomplete strategy% (22339)------------------------------
% 1.29/0.54  % (22339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22339)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22339)Memory used [KB]: 1663
% 1.29/0.54  % (22339)Time elapsed: 0.116 s
% 1.29/0.54  % (22339)------------------------------
% 1.29/0.54  % (22339)------------------------------
% 1.29/0.54  % (22356)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.54  % (22360)Refutation not found, incomplete strategy% (22360)------------------------------
% 1.29/0.54  % (22360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22360)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22360)Memory used [KB]: 1663
% 1.29/0.54  % (22360)Time elapsed: 0.124 s
% 1.29/0.54  % (22360)------------------------------
% 1.29/0.54  % (22360)------------------------------
% 1.29/0.54  % (22349)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.54  % (22347)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.54  % (22356)Refutation not found, incomplete strategy% (22356)------------------------------
% 1.29/0.54  % (22356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22356)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22356)Memory used [KB]: 10618
% 1.29/0.54  % (22356)Time elapsed: 0.109 s
% 1.29/0.54  % (22356)------------------------------
% 1.29/0.54  % (22356)------------------------------
% 1.29/0.54  % (22362)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22362)Memory used [KB]: 1663
% 1.29/0.54  % (22362)Time elapsed: 0.092 s
% 1.29/0.54  % (22362)------------------------------
% 1.29/0.54  % (22362)------------------------------
% 1.29/0.54  % (22347)Refutation not found, incomplete strategy% (22347)------------------------------
% 1.29/0.54  % (22347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22347)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22347)Memory used [KB]: 10618
% 1.29/0.54  % (22347)Time elapsed: 0.130 s
% 1.29/0.54  % (22347)------------------------------
% 1.29/0.54  % (22347)------------------------------
% 1.29/0.54  % (22366)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (22346)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (22355)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.54  % (22366)Refutation not found, incomplete strategy% (22366)------------------------------
% 1.29/0.54  % (22366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22367)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  % (22366)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22366)Memory used [KB]: 6268
% 1.29/0.54  % (22366)Time elapsed: 0.124 s
% 1.29/0.54  % (22366)------------------------------
% 1.29/0.54  % (22366)------------------------------
% 1.29/0.54  % (22361)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.54  % (22345)# SZS output start Saturation.
% 1.29/0.54  % (22346)Refutation not found, incomplete strategy% (22346)------------------------------
% 1.29/0.54  % (22346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22346)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (22346)Memory used [KB]: 6268
% 1.29/0.54  % (22346)Time elapsed: 0.109 s
% 1.29/0.54  % (22346)------------------------------
% 1.29/0.54  % (22346)------------------------------
% 1.29/0.54  cnf(u43,axiom,
% 1.29/0.54      r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1).
% 1.29/0.54  
% 1.29/0.54  cnf(u44,axiom,
% 1.29/0.54      ~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0).
% 1.29/0.54  
% 1.29/0.54  cnf(u48,axiom,
% 1.29/0.54      r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))).
% 1.29/0.54  
% 1.29/0.54  cnf(u49,axiom,
% 1.29/0.54      r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))).
% 1.29/0.54  
% 1.29/0.54  cnf(u47,axiom,
% 1.29/0.54      ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0).
% 1.29/0.54  
% 1.29/0.54  cnf(u56,negated_conjecture,
% 1.29/0.54      sK0 = sK1).
% 1.29/0.54  
% 1.29/0.54  cnf(u59,negated_conjecture,
% 1.29/0.54      k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))).
% 1.29/0.54  
% 1.29/0.54  cnf(u51,axiom,
% 1.29/0.54      k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) | X0 = X1).
% 1.29/0.54  
% 1.29/0.54  % (22345)# SZS output end Saturation.
% 1.29/0.54  % (22345)------------------------------
% 1.29/0.54  % (22345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (22345)Termination reason: Satisfiable
% 1.29/0.54  
% 1.29/0.54  % (22345)Memory used [KB]: 6268
% 1.29/0.54  % (22345)Time elapsed: 0.121 s
% 1.29/0.54  % (22345)------------------------------
% 1.29/0.54  % (22345)------------------------------
% 1.29/0.54  % (22338)Success in time 0.171 s
%------------------------------------------------------------------------------
