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
% DateTime   : Thu Dec  3 12:39:51 EST 2020

% Result     : CounterSatisfiable 1.31s
% Output     : Saturation 1.31s
% Verified   : 
% Statistics : Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u34,axiom,
    ( r1_xboole_0(X1,k1_xboole_0) )).

cnf(u33,axiom,
    ( r1_xboole_0(k1_xboole_0,X0) )).

cnf(u28,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u20,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) )).

cnf(u16,axiom,
    ( ~ r1_xboole_0(X0,X0)
    | k1_xboole_0 = X0 )).

cnf(u22,axiom,
    ( r2_hidden(sK3(X0,X1),X1)
    | r1_xboole_0(X0,X1) )).

cnf(u21,axiom,
    ( r2_hidden(sK3(X0,X1),X0)
    | r1_xboole_0(X0,X1) )).

cnf(u32,axiom,
    ( ~ r2_hidden(X0,k1_xboole_0) )).

cnf(u46,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,sK2)) )).

cnf(u44,negated_conjecture,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK1) )).

cnf(u24,axiom,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) )).

cnf(u47,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | k1_xboole_0 = sK0 )).

cnf(u39,axiom,
    ( k1_xboole_0 != k3_tarski(k1_enumset1(X0,X1,X0))
    | k1_xboole_0 = X0 )).

cnf(u27,axiom,
    ( k1_xboole_0 != k3_tarski(k1_enumset1(X0,X0,X1))
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:20:52 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (29275)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (29267)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (29267)Refutation not found, incomplete strategy% (29267)------------------------------
% 0.22/0.52  % (29267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (29267)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (29267)Memory used [KB]: 6140
% 0.22/0.52  % (29267)Time elapsed: 0.003 s
% 0.22/0.52  % (29267)------------------------------
% 0.22/0.52  % (29267)------------------------------
% 0.22/0.52  % (29259)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (29275)Refutation not found, incomplete strategy% (29275)------------------------------
% 0.22/0.52  % (29275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29275)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29275)Memory used [KB]: 1663
% 0.22/0.53  % (29275)Time elapsed: 0.053 s
% 0.22/0.53  % (29275)------------------------------
% 0.22/0.53  % (29275)------------------------------
% 0.22/0.53  % (29259)Refutation not found, incomplete strategy% (29259)------------------------------
% 0.22/0.53  % (29259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (29259)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (29259)Memory used [KB]: 6268
% 0.22/0.53  % (29259)Time elapsed: 0.065 s
% 0.22/0.53  % (29259)------------------------------
% 0.22/0.53  % (29259)------------------------------
% 0.22/0.53  % (29254)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (29276)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.54  % (29252)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.54  % (29252)Refutation not found, incomplete strategy% (29252)------------------------------
% 1.31/0.54  % (29252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (29252)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (29252)Memory used [KB]: 1663
% 1.31/0.54  % (29252)Time elapsed: 0.113 s
% 1.31/0.54  % (29252)------------------------------
% 1.31/0.54  % (29252)------------------------------
% 1.31/0.54  % (29273)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.54  % (29272)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.55  % (29273)Refutation not found, incomplete strategy% (29273)------------------------------
% 1.31/0.55  % (29273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29273)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29273)Memory used [KB]: 1663
% 1.31/0.55  % (29273)Time elapsed: 0.130 s
% 1.31/0.55  % (29273)------------------------------
% 1.31/0.55  % (29273)------------------------------
% 1.31/0.55  % (29271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.55  % (29256)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.55  % (29258)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.55  % (29256)Refutation not found, incomplete strategy% (29256)------------------------------
% 1.31/0.55  % (29256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29256)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29256)Memory used [KB]: 6140
% 1.31/0.55  % (29256)Time elapsed: 0.125 s
% 1.31/0.55  % (29256)------------------------------
% 1.31/0.55  % (29256)------------------------------
% 1.31/0.55  % (29255)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.55  % (29270)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.55  % SZS status CounterSatisfiable for theBenchmark
% 1.31/0.55  % (29254)Refutation not found, incomplete strategy% (29254)------------------------------
% 1.31/0.55  % (29254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29281)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (29255)Refutation not found, incomplete strategy% (29255)------------------------------
% 1.31/0.55  % (29255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29264)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (29280)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.55  % (29277)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.55  % (29254)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29254)Memory used [KB]: 10618
% 1.31/0.55  % (29254)Time elapsed: 0.127 s
% 1.31/0.55  % (29254)------------------------------
% 1.31/0.55  % (29254)------------------------------
% 1.31/0.55  % (29281)Refutation not found, incomplete strategy% (29281)------------------------------
% 1.31/0.55  % (29281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29266)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.55  % (29258)# SZS output start Saturation.
% 1.31/0.55  cnf(u34,axiom,
% 1.31/0.55      r1_xboole_0(X1,k1_xboole_0)).
% 1.31/0.55  
% 1.31/0.55  cnf(u33,axiom,
% 1.31/0.55      r1_xboole_0(k1_xboole_0,X0)).
% 1.31/0.55  
% 1.31/0.55  cnf(u28,axiom,
% 1.31/0.55      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 1.31/0.55  
% 1.31/0.55  cnf(u20,axiom,
% 1.31/0.55      ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)).
% 1.31/0.55  
% 1.31/0.55  cnf(u16,axiom,
% 1.31/0.55      ~r1_xboole_0(X0,X0) | k1_xboole_0 = X0).
% 1.31/0.55  
% 1.31/0.55  cnf(u22,axiom,
% 1.31/0.55      r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)).
% 1.31/0.55  
% 1.31/0.55  cnf(u21,axiom,
% 1.31/0.55      r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)).
% 1.31/0.55  
% 1.31/0.55  cnf(u32,axiom,
% 1.31/0.55      ~r2_hidden(X0,k1_xboole_0)).
% 1.31/0.55  
% 1.31/0.55  cnf(u46,negated_conjecture,
% 1.31/0.55      k1_xboole_0 = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,sK2))).
% 1.31/0.55  
% 1.31/0.55  cnf(u44,negated_conjecture,
% 1.31/0.55      k1_xboole_0 = k1_enumset1(sK0,sK0,sK1)).
% 1.31/0.55  
% 1.31/0.55  cnf(u24,axiom,
% 1.31/0.55      k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)).
% 1.31/0.55  
% 1.31/0.55  cnf(u47,negated_conjecture,
% 1.31/0.55      k1_xboole_0 != k3_tarski(k1_xboole_0) | k1_xboole_0 = sK0).
% 1.31/0.55  
% 1.31/0.55  cnf(u39,axiom,
% 1.31/0.55      k1_xboole_0 != k3_tarski(k1_enumset1(X0,X1,X0)) | k1_xboole_0 = X0).
% 1.31/0.55  
% 1.31/0.55  cnf(u27,axiom,
% 1.31/0.55      k1_xboole_0 != k3_tarski(k1_enumset1(X0,X0,X1)) | k1_xboole_0 = X0).
% 1.31/0.55  
% 1.31/0.55  % (29258)# SZS output end Saturation.
% 1.31/0.55  % (29258)------------------------------
% 1.31/0.55  % (29258)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29258)Termination reason: Satisfiable
% 1.31/0.55  
% 1.31/0.55  % (29258)Memory used [KB]: 6140
% 1.31/0.55  % (29258)Time elapsed: 0.132 s
% 1.31/0.55  % (29258)------------------------------
% 1.31/0.55  % (29258)------------------------------
% 1.31/0.55  % (29262)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.55  % (29268)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.55  % (29264)Refutation not found, incomplete strategy% (29264)------------------------------
% 1.31/0.55  % (29264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (29281)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (29281)Memory used [KB]: 1663
% 1.31/0.55  % (29281)Time elapsed: 0.132 s
% 1.31/0.55  % (29281)------------------------------
% 1.31/0.55  % (29281)------------------------------
% 1.50/0.55  % (29279)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.56  % (29251)Success in time 0.182 s
%------------------------------------------------------------------------------
