%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:33 EST 2020

% Result     : CounterSatisfiable 2.89s
% Output     : Saturation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u154,axiom,
    ( ~ ! [X1,X0] :
          ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
          | r1_xboole_0(X0,X1) )
    | ! [X1,X0] :
        ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) )).

tff(u153,negated_conjecture,
    ( ~ ( k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) )
    | k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0) )).

tff(u152,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK1 )
    | k1_xboole_0 != sK1 )).

tff(u151,axiom,
    ( ~ ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u150,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))
    | k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) )).

tff(u149,axiom,
    ( ~ ! [X0] :
          ( ~ r1_xboole_0(X0,X0)
          | ~ sP0(X0) )
    | ! [X0] :
        ( ~ r1_xboole_0(X0,X0)
        | ~ sP0(X0) ) )).

tff(u148,axiom,
    ( ~ ! [X1,X0] :
          ( ~ r1_xboole_0(X0,X1)
          | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) )).

tff(u147,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK1)
    | r1_xboole_0(sK1,sK1) )).

tff(u146,axiom,
    ( ~ ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ! [X0] : r1_xboole_0(k1_xboole_0,X0) )).

tff(u145,axiom,
    ( ~ ! [X0] :
          ( ~ sP0(X0)
          | k1_xboole_0 = X0 )
    | ! [X0] :
        ( ~ sP0(X0)
        | k1_xboole_0 = X0 ) )).

tff(u144,negated_conjecture,
    ( ~ ~ sP0(k1_xboole_0)
    | ~ sP0(k1_xboole_0) )).

tff(u143,negated_conjecture,
    ( ~ ~ sP0(k4_xboole_0(sK1,k1_xboole_0))
    | ~ sP0(k4_xboole_0(sK1,k1_xboole_0)) )).

tff(u142,negated_conjecture,
    ( ~ ~ sP0(sK1)
    | ~ sP0(sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:27:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (30680)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (30672)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (30674)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (30675)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (30674)Refutation not found, incomplete strategy% (30674)------------------------------
% 0.22/0.51  % (30674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30680)Refutation not found, incomplete strategy% (30680)------------------------------
% 0.22/0.51  % (30680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (30674)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30674)Memory used [KB]: 10618
% 0.22/0.51  % (30674)Time elapsed: 0.108 s
% 0.22/0.51  % (30674)------------------------------
% 0.22/0.51  % (30674)------------------------------
% 0.22/0.51  % (30680)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (30680)Memory used [KB]: 10618
% 0.22/0.51  % (30680)Time elapsed: 0.102 s
% 0.22/0.51  % (30680)------------------------------
% 0.22/0.51  % (30680)------------------------------
% 0.22/0.52  % (30696)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.52  % (30676)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (30671)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (30671)Refutation not found, incomplete strategy% (30671)------------------------------
% 0.22/0.52  % (30671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30671)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30671)Memory used [KB]: 1663
% 0.22/0.52  % (30671)Time elapsed: 0.108 s
% 0.22/0.52  % (30671)------------------------------
% 0.22/0.52  % (30671)------------------------------
% 0.22/0.52  % (30681)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (30678)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (30681)Refutation not found, incomplete strategy% (30681)------------------------------
% 0.22/0.52  % (30681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30681)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30681)Memory used [KB]: 10618
% 0.22/0.52  % (30681)Time elapsed: 0.117 s
% 0.22/0.52  % (30681)------------------------------
% 0.22/0.52  % (30681)------------------------------
% 0.22/0.52  % (30686)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (30686)Refutation not found, incomplete strategy% (30686)------------------------------
% 0.22/0.52  % (30686)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (30686)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (30686)Memory used [KB]: 6140
% 0.22/0.52  % (30686)Time elapsed: 0.001 s
% 0.22/0.52  % (30686)------------------------------
% 0.22/0.52  % (30686)------------------------------
% 0.22/0.53  % (30691)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (30694)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (30694)Refutation not found, incomplete strategy% (30694)------------------------------
% 0.22/0.53  % (30694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (30684)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (30683)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (30679)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (30673)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (30694)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30694)Memory used [KB]: 1663
% 0.22/0.54  % (30694)Time elapsed: 0.098 s
% 0.22/0.54  % (30694)------------------------------
% 0.22/0.54  % (30694)------------------------------
% 0.22/0.54  % (30698)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (30673)Refutation not found, incomplete strategy% (30673)------------------------------
% 0.22/0.54  % (30673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30673)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30673)Memory used [KB]: 10618
% 0.22/0.54  % (30673)Time elapsed: 0.128 s
% 0.22/0.54  % (30673)------------------------------
% 0.22/0.54  % (30673)------------------------------
% 0.22/0.54  % (30690)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (30682)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (30697)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (30692)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (30690)Refutation not found, incomplete strategy% (30690)------------------------------
% 0.22/0.54  % (30690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30689)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (30699)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (30700)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (30682)Refutation not found, incomplete strategy% (30682)------------------------------
% 0.22/0.54  % (30682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30695)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (30698)Refutation not found, incomplete strategy% (30698)------------------------------
% 0.22/0.54  % (30698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30682)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30682)Memory used [KB]: 10618
% 0.22/0.54  % (30682)Time elapsed: 0.143 s
% 0.22/0.54  % (30682)------------------------------
% 0.22/0.54  % (30682)------------------------------
% 0.22/0.54  % (30679)Refutation not found, incomplete strategy% (30679)------------------------------
% 0.22/0.54  % (30679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30698)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30698)Memory used [KB]: 6140
% 0.22/0.54  % (30698)Time elapsed: 0.142 s
% 0.22/0.54  % (30698)------------------------------
% 0.22/0.54  % (30698)------------------------------
% 0.22/0.54  % (30690)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30690)Memory used [KB]: 10746
% 0.22/0.54  % (30690)Time elapsed: 0.143 s
% 0.22/0.54  % (30690)------------------------------
% 0.22/0.54  % (30690)------------------------------
% 0.22/0.55  % (30691)Refutation not found, incomplete strategy% (30691)------------------------------
% 0.22/0.55  % (30691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30691)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30691)Memory used [KB]: 10618
% 0.22/0.55  % (30691)Time elapsed: 0.143 s
% 0.22/0.55  % (30691)------------------------------
% 0.22/0.55  % (30691)------------------------------
% 0.22/0.55  % (30679)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30679)Memory used [KB]: 10618
% 0.22/0.55  % (30679)Time elapsed: 0.142 s
% 0.22/0.55  % (30679)------------------------------
% 0.22/0.55  % (30679)------------------------------
% 0.22/0.55  % (30687)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (30688)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.55  % (30677)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.55  % (30688)Refutation not found, incomplete strategy% (30688)------------------------------
% 1.58/0.55  % (30688)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.55  % (30688)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.55  
% 1.58/0.55  % (30688)Memory used [KB]: 10618
% 1.58/0.55  % (30688)Time elapsed: 0.151 s
% 1.58/0.55  % (30688)------------------------------
% 1.58/0.55  % (30688)------------------------------
% 1.58/0.57  % (30693)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.58/0.57  % (30693)Refutation not found, incomplete strategy% (30693)------------------------------
% 1.58/0.57  % (30693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (30693)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (30693)Memory used [KB]: 10618
% 1.58/0.57  % (30693)Time elapsed: 0.146 s
% 1.58/0.57  % (30693)------------------------------
% 1.58/0.57  % (30693)------------------------------
% 1.58/0.57  % (30685)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 2.15/0.66  % (30704)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.15/0.66  % (30715)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.15/0.66  % (30707)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.15/0.67  % (30705)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.15/0.69  % (30706)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.15/0.69  % (30708)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.15/0.69  % (30711)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.15/0.69  % (30713)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.15/0.69  % (30722)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.15/0.70  % (30722)Refutation not found, incomplete strategy% (30722)------------------------------
% 2.15/0.70  % (30722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.70  % (30722)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.70  
% 2.15/0.70  % (30722)Memory used [KB]: 1663
% 2.15/0.70  % (30722)Time elapsed: 0.003 s
% 2.15/0.70  % (30722)------------------------------
% 2.15/0.70  % (30722)------------------------------
% 2.15/0.70  % (30712)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.15/0.70  % (30714)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.15/0.70  % (30712)Refutation not found, incomplete strategy% (30712)------------------------------
% 2.15/0.70  % (30712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.70  % (30712)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.70  
% 2.15/0.70  % (30712)Memory used [KB]: 1663
% 2.15/0.70  % (30712)Time elapsed: 0.138 s
% 2.15/0.70  % (30712)------------------------------
% 2.15/0.70  % (30712)------------------------------
% 2.15/0.71  % (30709)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.15/0.71  % (30716)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.15/0.72  % (30710)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.63/0.73  % (30699)Refutation not found, incomplete strategy% (30699)------------------------------
% 2.63/0.73  % (30699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.63/0.73  % (30699)Termination reason: Refutation not found, incomplete strategy
% 2.63/0.73  
% 2.63/0.73  % (30699)Memory used [KB]: 6140
% 2.63/0.73  % (30699)Time elapsed: 0.314 s
% 2.63/0.73  % (30699)------------------------------
% 2.63/0.73  % (30699)------------------------------
% 2.89/0.78  % (30685)Refutation not found, incomplete strategy% (30685)------------------------------
% 2.89/0.78  % (30685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.78  % (30685)Termination reason: Refutation not found, incomplete strategy
% 2.89/0.78  
% 2.89/0.78  % (30685)Memory used [KB]: 1663
% 2.89/0.78  % (30685)Time elapsed: 0.331 s
% 2.89/0.78  % (30685)------------------------------
% 2.89/0.78  % (30685)------------------------------
% 2.89/0.80  % (30697)Refutation not found, incomplete strategy% (30697)------------------------------
% 2.89/0.80  % (30697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.80  % (30697)Termination reason: Refutation not found, incomplete strategy
% 2.89/0.80  
% 2.89/0.80  % (30697)Memory used [KB]: 12920
% 2.89/0.80  % (30697)Time elapsed: 0.383 s
% 2.89/0.80  % (30697)------------------------------
% 2.89/0.80  % (30697)------------------------------
% 2.89/0.80  % (30748)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.89/0.81  % (30749)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 2.89/0.81  % (30676)Time limit reached!
% 2.89/0.81  % (30676)------------------------------
% 2.89/0.81  % (30676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.81  % (30676)Termination reason: Time limit
% 2.89/0.81  % (30676)Termination phase: Saturation
% 2.89/0.81  
% 2.89/0.81  % (30676)Memory used [KB]: 7931
% 2.89/0.81  % (30676)Time elapsed: 0.400 s
% 2.89/0.81  % (30676)------------------------------
% 2.89/0.81  % (30676)------------------------------
% 2.89/0.81  % SZS status CounterSatisfiable for theBenchmark
% 2.89/0.81  % (30748)# SZS output start Saturation.
% 2.89/0.81  tff(u154,axiom,
% 2.89/0.81      ((~(![X1, X0] : (((k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1))))) | (![X1, X0] : (((k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)))))).
% 2.89/0.81  
% 2.89/0.81  tff(u153,negated_conjecture,
% 2.89/0.81      ((~(k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0))) | (k1_xboole_0 != k4_xboole_0(sK1,k1_xboole_0)))).
% 2.89/0.81  
% 2.89/0.81  tff(u152,negated_conjecture,
% 2.89/0.81      ((~(k1_xboole_0 != sK1)) | (k1_xboole_0 != sK1))).
% 2.89/0.81  
% 2.89/0.81  tff(u151,axiom,
% 2.89/0.81      ((~(![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))) | (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)))))).
% 2.89/0.81  
% 2.89/0.81  tff(u150,negated_conjecture,
% 2.89/0.81      ((~(k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))) | (k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))))).
% 2.89/0.81  
% 2.89/0.81  tff(u149,axiom,
% 2.89/0.81      ((~(![X0] : ((~r1_xboole_0(X0,X0) | ~sP0(X0))))) | (![X0] : ((~r1_xboole_0(X0,X0) | ~sP0(X0)))))).
% 2.89/0.81  
% 2.89/0.81  tff(u148,axiom,
% 2.89/0.81      ((~(![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) | (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)))))))).
% 2.89/0.81  
% 2.89/0.81  tff(u147,negated_conjecture,
% 2.89/0.81      ((~r1_xboole_0(sK1,sK1)) | r1_xboole_0(sK1,sK1))).
% 2.89/0.81  
% 2.89/0.81  tff(u146,axiom,
% 2.89/0.81      ((~(![X0] : (r1_xboole_0(k1_xboole_0,X0)))) | (![X0] : (r1_xboole_0(k1_xboole_0,X0))))).
% 2.89/0.81  
% 2.89/0.81  tff(u145,axiom,
% 2.89/0.81      ((~(![X0] : ((~sP0(X0) | (k1_xboole_0 = X0))))) | (![X0] : ((~sP0(X0) | (k1_xboole_0 = X0)))))).
% 2.89/0.81  
% 2.89/0.81  tff(u144,negated_conjecture,
% 2.89/0.81      ((~~sP0(k1_xboole_0)) | ~sP0(k1_xboole_0))).
% 2.89/0.81  
% 2.89/0.81  tff(u143,negated_conjecture,
% 2.89/0.81      ((~~sP0(k4_xboole_0(sK1,k1_xboole_0))) | ~sP0(k4_xboole_0(sK1,k1_xboole_0)))).
% 2.89/0.81  
% 2.89/0.81  tff(u142,negated_conjecture,
% 2.89/0.81      ((~~sP0(sK1)) | ~sP0(sK1))).
% 2.89/0.81  
% 2.89/0.81  % (30748)# SZS output end Saturation.
% 2.89/0.81  % (30748)------------------------------
% 2.89/0.81  % (30748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.89/0.81  % (30748)Termination reason: Satisfiable
% 2.89/0.81  
% 2.89/0.81  % (30748)Memory used [KB]: 10746
% 2.89/0.81  % (30748)Time elapsed: 0.052 s
% 2.89/0.81  % (30748)------------------------------
% 2.89/0.81  % (30748)------------------------------
% 2.89/0.81  % (30670)Success in time 0.461 s
%------------------------------------------------------------------------------
