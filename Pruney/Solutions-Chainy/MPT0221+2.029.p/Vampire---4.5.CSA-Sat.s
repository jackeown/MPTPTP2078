%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:49 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :    8 (   8 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u33,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u18,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u35,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u20,axiom,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 )).

cnf(u38,negated_conjecture,
    ( k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

cnf(u34,axiom,
    ( k1_xboole_0 = sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (27490)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.49  % (27474)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (27466)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (27463)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.49  % (27470)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.49  % (27466)Refutation not found, incomplete strategy% (27466)------------------------------
% 0.20/0.49  % (27466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27466)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (27466)Memory used [KB]: 6140
% 0.20/0.49  % (27466)Time elapsed: 0.098 s
% 0.20/0.49  % (27466)------------------------------
% 0.20/0.49  % (27466)------------------------------
% 0.20/0.50  % (27470)Refutation not found, incomplete strategy% (27470)------------------------------
% 0.20/0.50  % (27470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27470)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27470)Memory used [KB]: 10618
% 0.20/0.50  % (27470)Time elapsed: 0.097 s
% 0.20/0.50  % (27470)------------------------------
% 0.20/0.50  % (27470)------------------------------
% 0.20/0.50  % (27488)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.50  % (27474)Refutation not found, incomplete strategy% (27474)------------------------------
% 0.20/0.50  % (27474)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27465)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (27474)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27474)Memory used [KB]: 6140
% 0.20/0.50  % (27474)Time elapsed: 0.104 s
% 0.20/0.50  % (27474)------------------------------
% 0.20/0.50  % (27474)------------------------------
% 0.20/0.50  % (27480)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (27465)Refutation not found, incomplete strategy% (27465)------------------------------
% 0.20/0.50  % (27465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27465)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27465)Memory used [KB]: 10618
% 0.20/0.50  % (27465)Time elapsed: 0.084 s
% 0.20/0.50  % (27465)------------------------------
% 0.20/0.50  % (27465)------------------------------
% 0.20/0.50  % (27486)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.50  % (27464)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (27464)Refutation not found, incomplete strategy% (27464)------------------------------
% 0.20/0.50  % (27464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27464)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27464)Memory used [KB]: 10618
% 0.20/0.50  % (27464)Time elapsed: 0.110 s
% 0.20/0.50  % (27464)------------------------------
% 0.20/0.50  % (27464)------------------------------
% 0.20/0.50  % (27472)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (27479)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.51  % (27488)Refutation not found, incomplete strategy% (27488)------------------------------
% 0.20/0.51  % (27488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27488)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27488)Memory used [KB]: 10618
% 0.20/0.51  % (27488)Time elapsed: 0.109 s
% 0.20/0.51  % (27488)------------------------------
% 0.20/0.51  % (27488)------------------------------
% 0.20/0.51  % (27479)Refutation not found, incomplete strategy% (27479)------------------------------
% 0.20/0.51  % (27479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27479)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27479)Memory used [KB]: 10618
% 0.20/0.51  % (27479)Time elapsed: 0.115 s
% 0.20/0.51  % (27479)------------------------------
% 0.20/0.51  % (27479)------------------------------
% 0.20/0.51  % (27469)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (27469)Refutation not found, incomplete strategy% (27469)------------------------------
% 0.20/0.51  % (27469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27469)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27469)Memory used [KB]: 6140
% 0.20/0.51  % (27469)Time elapsed: 0.108 s
% 0.20/0.51  % (27469)------------------------------
% 0.20/0.51  % (27469)------------------------------
% 0.20/0.51  % (27472)Refutation not found, incomplete strategy% (27472)------------------------------
% 0.20/0.51  % (27472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27472)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27472)Memory used [KB]: 10618
% 0.20/0.51  % (27472)Time elapsed: 0.117 s
% 0.20/0.51  % (27472)------------------------------
% 0.20/0.51  % (27472)------------------------------
% 0.20/0.51  % (27471)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (27484)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (27473)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (27487)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (27487)Refutation not found, incomplete strategy% (27487)------------------------------
% 0.20/0.52  % (27487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27487)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27487)Memory used [KB]: 6140
% 0.20/0.52  % (27487)Time elapsed: 0.123 s
% 0.20/0.52  % (27487)------------------------------
% 0.20/0.52  % (27487)------------------------------
% 0.20/0.52  % (27473)Refutation not found, incomplete strategy% (27473)------------------------------
% 0.20/0.52  % (27473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27473)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27473)Memory used [KB]: 10618
% 0.20/0.52  % (27473)Time elapsed: 0.118 s
% 0.20/0.52  % (27473)------------------------------
% 0.20/0.52  % (27473)------------------------------
% 0.20/0.52  % (27471)Refutation not found, incomplete strategy% (27471)------------------------------
% 0.20/0.52  % (27471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27471)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27471)Memory used [KB]: 10618
% 0.20/0.52  % (27471)Time elapsed: 0.126 s
% 0.20/0.52  % (27471)------------------------------
% 0.20/0.52  % (27471)------------------------------
% 0.20/0.52  % (27462)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (27462)Refutation not found, incomplete strategy% (27462)------------------------------
% 0.20/0.52  % (27462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27462)Memory used [KB]: 1663
% 0.20/0.52  % (27462)Time elapsed: 0.118 s
% 0.20/0.52  % (27462)------------------------------
% 0.20/0.52  % (27462)------------------------------
% 0.20/0.52  % (27476)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (27486)Refutation not found, incomplete strategy% (27486)------------------------------
% 0.20/0.52  % (27486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (27486)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (27486)Memory used [KB]: 6140
% 0.20/0.52  % (27486)Time elapsed: 0.126 s
% 0.20/0.52  % (27486)------------------------------
% 0.20/0.52  % (27486)------------------------------
% 0.20/0.53  % (27468)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (27484)Refutation not found, incomplete strategy% (27484)------------------------------
% 0.20/0.53  % (27484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27484)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27484)Memory used [KB]: 10618
% 0.20/0.53  % (27484)Time elapsed: 0.089 s
% 0.20/0.53  % (27484)------------------------------
% 0.20/0.53  % (27484)------------------------------
% 0.20/0.53  % (27485)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (27468)# SZS output start Saturation.
% 0.20/0.53  cnf(u33,axiom,
% 0.20/0.53      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u18,axiom,
% 0.20/0.53      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u35,axiom,
% 0.20/0.53      v1_xboole_0(k1_xboole_0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u20,axiom,
% 0.20/0.53      ~v1_xboole_0(X0) | k1_xboole_0 = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u38,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  cnf(u34,axiom,
% 0.20/0.53      k1_xboole_0 = sK2).
% 0.20/0.53  
% 0.20/0.53  % (27468)# SZS output end Saturation.
% 0.20/0.53  % (27468)------------------------------
% 0.20/0.53  % (27468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27468)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (27468)Memory used [KB]: 6140
% 0.20/0.53  % (27468)Time elapsed: 0.113 s
% 0.20/0.53  % (27468)------------------------------
% 0.20/0.53  % (27468)------------------------------
% 0.20/0.53  % (27461)Success in time 0.173 s
%------------------------------------------------------------------------------
