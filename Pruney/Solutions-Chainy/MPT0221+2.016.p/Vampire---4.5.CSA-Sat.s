%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:47 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :    3 (   3 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    0
%              Number of atoms          :    4 (   4 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u15,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u17,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u26,negated_conjecture,
    ( k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7698)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (7705)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (7705)Refutation not found, incomplete strategy% (7705)------------------------------
% 0.20/0.50  % (7705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7705)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7705)Memory used [KB]: 10618
% 0.20/0.50  % (7705)Time elapsed: 0.092 s
% 0.20/0.50  % (7705)------------------------------
% 0.20/0.50  % (7705)------------------------------
% 0.20/0.50  % (7698)Refutation not found, incomplete strategy% (7698)------------------------------
% 0.20/0.50  % (7698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7698)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7698)Memory used [KB]: 6140
% 0.20/0.50  % (7698)Time elapsed: 0.091 s
% 0.20/0.50  % (7698)------------------------------
% 0.20/0.50  % (7698)------------------------------
% 0.20/0.50  % (7697)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.50  % (7697)Refutation not found, incomplete strategy% (7697)------------------------------
% 0.20/0.50  % (7697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7697)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7697)Memory used [KB]: 10618
% 0.20/0.50  % (7697)Time elapsed: 0.108 s
% 0.20/0.50  % (7697)------------------------------
% 0.20/0.50  % (7697)------------------------------
% 0.20/0.51  % (7696)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (7695)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (7696)Refutation not found, incomplete strategy% (7696)------------------------------
% 0.20/0.51  % (7696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7696)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7696)Memory used [KB]: 10618
% 0.20/0.51  % (7696)Time elapsed: 0.105 s
% 0.20/0.51  % (7696)------------------------------
% 0.20/0.51  % (7696)------------------------------
% 0.20/0.51  % (7690)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (7690)Refutation not found, incomplete strategy% (7690)------------------------------
% 0.20/0.51  % (7690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7690)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7690)Memory used [KB]: 6140
% 0.20/0.51  % (7690)Time elapsed: 0.118 s
% 0.20/0.51  % (7690)------------------------------
% 0.20/0.51  % (7690)------------------------------
% 0.20/0.52  % (7707)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (7714)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.52  % (7707)Refutation not found, incomplete strategy% (7707)------------------------------
% 0.20/0.52  % (7707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7707)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7707)Memory used [KB]: 1663
% 0.20/0.52  % (7707)Time elapsed: 0.115 s
% 0.20/0.52  % (7707)------------------------------
% 0.20/0.52  % (7707)------------------------------
% 0.20/0.52  % (7693)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (7710)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (7693)Refutation not found, incomplete strategy% (7693)------------------------------
% 0.20/0.52  % (7693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7710)Refutation not found, incomplete strategy% (7710)------------------------------
% 0.20/0.52  % (7710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7710)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  % (7693)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7710)Memory used [KB]: 6140
% 0.20/0.52  % (7710)Time elapsed: 0.125 s
% 0.20/0.52  
% 0.20/0.52  % (7693)Memory used [KB]: 6140
% 0.20/0.52  % (7710)------------------------------
% 0.20/0.52  % (7710)------------------------------
% 0.20/0.52  % (7693)Time elapsed: 0.128 s
% 0.20/0.52  % (7688)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (7693)------------------------------
% 0.20/0.52  % (7693)------------------------------
% 0.20/0.53  % (7709)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (7709)Refutation not found, incomplete strategy% (7709)------------------------------
% 0.20/0.53  % (7709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7709)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7709)Memory used [KB]: 1663
% 0.20/0.53  % (7689)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (7709)Time elapsed: 0.130 s
% 0.20/0.53  % (7709)------------------------------
% 0.20/0.53  % (7709)------------------------------
% 0.20/0.53  % (7706)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (7713)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (7689)Refutation not found, incomplete strategy% (7689)------------------------------
% 0.20/0.53  % (7689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7689)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7689)Memory used [KB]: 10618
% 0.20/0.53  % (7689)Time elapsed: 0.126 s
% 0.20/0.53  % (7689)------------------------------
% 0.20/0.53  % (7689)------------------------------
% 0.20/0.53  % (7713)Refutation not found, incomplete strategy% (7713)------------------------------
% 0.20/0.53  % (7713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7713)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7713)Memory used [KB]: 6140
% 0.20/0.53  % (7713)Time elapsed: 0.131 s
% 0.20/0.53  % (7713)------------------------------
% 0.20/0.53  % (7713)------------------------------
% 0.20/0.53  % (7692)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (7706)Refutation not found, incomplete strategy% (7706)------------------------------
% 0.20/0.53  % (7706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7706)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (7706)Memory used [KB]: 10618
% 0.20/0.53  % (7706)Time elapsed: 0.128 s
% 0.20/0.53  % (7706)------------------------------
% 0.20/0.53  % (7706)------------------------------
% 0.20/0.53  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.53  % (7692)# SZS output start Saturation.
% 0.20/0.53  cnf(u15,axiom,
% 0.20/0.53      r1_xboole_0(X0,k1_xboole_0)).
% 0.20/0.53  
% 0.20/0.53  cnf(u17,axiom,
% 0.20/0.53      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 0.20/0.53  
% 0.20/0.53  cnf(u26,negated_conjecture,
% 0.20/0.53      k1_xboole_0 = k2_enumset1(sK1,sK1,sK1,sK1)).
% 0.20/0.53  
% 0.20/0.53  % (7692)# SZS output end Saturation.
% 0.20/0.53  % (7692)------------------------------
% 0.20/0.53  % (7692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (7692)Termination reason: Satisfiable
% 0.20/0.53  
% 0.20/0.53  % (7692)Memory used [KB]: 6140
% 0.20/0.53  % (7692)Time elapsed: 0.100 s
% 0.20/0.53  % (7692)------------------------------
% 0.20/0.53  % (7692)------------------------------
% 0.20/0.53  % (7685)Success in time 0.173 s
%------------------------------------------------------------------------------
