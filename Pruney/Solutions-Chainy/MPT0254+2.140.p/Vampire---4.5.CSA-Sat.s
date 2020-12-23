%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:31 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    0
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u20,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u51,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) = k3_tarski(k1_xboole_0) )).

cnf(u49,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) )).

cnf(u47,negated_conjecture,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

cnf(u48,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) )).

cnf(u40,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) )).

cnf(u42,axiom,
    ( k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
    | k1_xboole_0 = X0 )).

cnf(u52,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | k1_xboole_0 = sK0 )).

cnf(u41,axiom,
    ( k1_xboole_0 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (29153)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.44  % (29153)Refutation not found, incomplete strategy% (29153)------------------------------
% 0.20/0.44  % (29153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (29153)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (29153)Memory used [KB]: 1663
% 0.20/0.44  % (29153)Time elapsed: 0.004 s
% 0.20/0.44  % (29153)------------------------------
% 0.20/0.44  % (29153)------------------------------
% 0.20/0.46  % (29166)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (29154)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (29162)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (29154)Refutation not found, incomplete strategy% (29154)------------------------------
% 0.20/0.46  % (29154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (29154)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (29154)Memory used [KB]: 6140
% 0.20/0.46  % (29154)Time elapsed: 0.038 s
% 0.20/0.46  % (29154)------------------------------
% 0.20/0.46  % (29154)------------------------------
% 0.20/0.46  % (29162)Refutation not found, incomplete strategy% (29162)------------------------------
% 0.20/0.46  % (29162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (29162)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (29162)Memory used [KB]: 10618
% 0.20/0.46  % (29162)Time elapsed: 0.050 s
% 0.20/0.46  % (29162)------------------------------
% 0.20/0.46  % (29162)------------------------------
% 0.20/0.47  % (29151)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (29151)# SZS output start Saturation.
% 0.20/0.47  cnf(u20,axiom,
% 0.20/0.47      v1_xboole_0(k1_xboole_0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u51,negated_conjecture,
% 0.20/0.47      k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) = k3_tarski(k1_xboole_0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u49,negated_conjecture,
% 0.20/0.47      k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))).
% 0.20/0.47  
% 0.20/0.47  cnf(u47,negated_conjecture,
% 0.20/0.47      k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)).
% 0.20/0.47  
% 0.20/0.47  cnf(u48,negated_conjecture,
% 0.20/0.47      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))).
% 0.20/0.47  
% 0.20/0.47  cnf(u40,axiom,
% 0.20/0.47      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))).
% 0.20/0.47  
% 0.20/0.47  cnf(u42,axiom,
% 0.20/0.47      k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0).
% 0.20/0.47  
% 0.20/0.47  cnf(u52,negated_conjecture,
% 0.20/0.47      k1_xboole_0 != k3_tarski(k1_xboole_0) | k1_xboole_0 = sK0).
% 0.20/0.47  
% 0.20/0.47  cnf(u41,axiom,
% 0.20/0.47      k1_xboole_0 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | k1_xboole_0 = X0).
% 0.20/0.47  
% 0.20/0.47  % (29151)# SZS output end Saturation.
% 0.20/0.47  % (29151)------------------------------
% 0.20/0.47  % (29151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (29151)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (29151)Memory used [KB]: 1663
% 0.20/0.47  % (29151)Time elapsed: 0.051 s
% 0.20/0.47  % (29151)------------------------------
% 0.20/0.47  % (29151)------------------------------
% 0.20/0.47  % (29157)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (29147)Success in time 0.112 s
%------------------------------------------------------------------------------
