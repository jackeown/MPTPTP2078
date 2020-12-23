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
% DateTime   : Thu Dec  3 12:29:36 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u12,negated_conjecture,
    ( r1_tarski(sK0,X0) )).

cnf(u9,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u10,axiom,
    ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
    | r1_tarski(X0,X2) )).

cnf(u7,negated_conjecture,
    ( k1_xboole_0 = k2_xboole_0(sK0,sK1) )).

cnf(u8,negated_conjecture,
    ( k1_xboole_0 != sK0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (19335)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.45  % (19335)Refutation not found, incomplete strategy% (19335)------------------------------
% 0.22/0.45  % (19335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (19335)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (19335)Memory used [KB]: 10490
% 0.22/0.45  % (19335)Time elapsed: 0.054 s
% 0.22/0.45  % (19335)------------------------------
% 0.22/0.45  % (19335)------------------------------
% 0.22/0.47  % (19338)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (19340)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (19338)Refutation not found, incomplete strategy% (19338)------------------------------
% 0.22/0.47  % (19338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19338)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (19338)Memory used [KB]: 10490
% 0.22/0.49  % (19338)Time elapsed: 0.052 s
% 0.22/0.49  % (19338)------------------------------
% 0.22/0.49  % (19338)------------------------------
% 0.22/0.49  % (19351)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (19351)Refutation not found, incomplete strategy% (19351)------------------------------
% 0.22/0.49  % (19351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19351)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (19351)Memory used [KB]: 6012
% 0.22/0.49  % (19351)Time elapsed: 0.088 s
% 0.22/0.49  % (19351)------------------------------
% 0.22/0.49  % (19351)------------------------------
% 0.22/0.49  % (19344)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (19344)Refutation not found, incomplete strategy% (19344)------------------------------
% 0.22/0.49  % (19344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (19344)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (19344)Memory used [KB]: 6012
% 0.22/0.49  % (19344)Time elapsed: 0.002 s
% 0.22/0.49  % (19344)------------------------------
% 0.22/0.49  % (19344)------------------------------
% 0.22/0.50  % (19346)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (19336)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (19336)Refutation not found, incomplete strategy% (19336)------------------------------
% 0.22/0.51  % (19336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19336)Memory used [KB]: 1535
% 0.22/0.51  % (19336)Time elapsed: 0.072 s
% 0.22/0.51  % (19336)------------------------------
% 0.22/0.51  % (19336)------------------------------
% 0.22/0.51  % (19352)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (19352)Refutation not found, incomplete strategy% (19352)------------------------------
% 0.22/0.51  % (19352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19352)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19352)Memory used [KB]: 10490
% 0.22/0.51  % (19352)Time elapsed: 0.107 s
% 0.22/0.51  % (19333)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (19352)------------------------------
% 0.22/0.51  % (19352)------------------------------
% 0.22/0.51  % (19333)Refutation not found, incomplete strategy% (19333)------------------------------
% 0.22/0.51  % (19333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19333)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19333)Memory used [KB]: 10490
% 0.22/0.51  % (19333)Time elapsed: 0.068 s
% 0.22/0.51  % (19333)------------------------------
% 0.22/0.51  % (19333)------------------------------
% 0.22/0.51  % (19350)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (19350)Refutation not found, incomplete strategy% (19350)------------------------------
% 0.22/0.51  % (19350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19350)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19350)Memory used [KB]: 1535
% 0.22/0.51  % (19350)Time elapsed: 0.064 s
% 0.22/0.51  % (19350)------------------------------
% 0.22/0.51  % (19350)------------------------------
% 0.22/0.51  % (19331)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (19337)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (19331)Refutation not found, incomplete strategy% (19331)------------------------------
% 0.22/0.51  % (19331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19331)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19331)Memory used [KB]: 6140
% 0.22/0.51  % (19331)Time elapsed: 0.098 s
% 0.22/0.51  % (19331)------------------------------
% 0.22/0.51  % (19331)------------------------------
% 0.22/0.51  % (19343)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (19343)Refutation not found, incomplete strategy% (19343)------------------------------
% 0.22/0.52  % (19343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19343)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19343)Memory used [KB]: 10490
% 0.22/0.52  % (19343)Time elapsed: 0.079 s
% 0.22/0.52  % (19343)------------------------------
% 0.22/0.52  % (19343)------------------------------
% 0.22/0.52  % (19345)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.52  % (19339)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (19342)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (19345)Refutation not found, incomplete strategy% (19345)------------------------------
% 0.22/0.52  % (19345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19345)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19345)Memory used [KB]: 1535
% 0.22/0.52  % (19345)Time elapsed: 0.080 s
% 0.22/0.52  % (19345)------------------------------
% 0.22/0.52  % (19345)------------------------------
% 0.22/0.52  % (19342)Refutation not found, incomplete strategy% (19342)------------------------------
% 0.22/0.52  % (19342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19342)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19342)Memory used [KB]: 6012
% 0.22/0.52  % (19342)Time elapsed: 0.084 s
% 0.22/0.52  % (19342)------------------------------
% 0.22/0.52  % (19342)------------------------------
% 0.22/0.52  % (19349)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (19349)# SZS output start Saturation.
% 0.22/0.52  cnf(u12,negated_conjecture,
% 0.22/0.52      r1_tarski(sK0,X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u9,axiom,
% 0.22/0.52      r1_tarski(k1_xboole_0,X0)).
% 0.22/0.52  
% 0.22/0.52  cnf(u10,axiom,
% 0.22/0.52      ~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)).
% 0.22/0.52  
% 0.22/0.52  cnf(u7,negated_conjecture,
% 0.22/0.52      k1_xboole_0 = k2_xboole_0(sK0,sK1)).
% 0.22/0.52  
% 0.22/0.52  cnf(u8,negated_conjecture,
% 0.22/0.52      k1_xboole_0 != sK0).
% 0.22/0.52  
% 0.22/0.52  % (19349)# SZS output end Saturation.
% 0.22/0.52  % (19349)------------------------------
% 0.22/0.52  % (19349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19349)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (19349)Memory used [KB]: 1535
% 0.22/0.52  % (19349)Time elapsed: 0.109 s
% 0.22/0.52  % (19349)------------------------------
% 0.22/0.52  % (19349)------------------------------
% 0.22/0.52  % (19330)Success in time 0.162 s
%------------------------------------------------------------------------------
