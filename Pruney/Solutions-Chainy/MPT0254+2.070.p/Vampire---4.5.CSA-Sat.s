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
% DateTime   : Thu Dec  3 12:39:22 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u34,negated_conjecture,
    ( v1_xboole_0(k1_enumset1(sK0,sK0,sK0)) )).

cnf(u26,negated_conjecture,
    ( v1_xboole_0(sK1) )).

cnf(u14,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u24,axiom,
    ( ~ v1_xboole_0(k3_tarski(k1_enumset1(X1,X1,X0)))
    | v1_xboole_0(X0) )).

cnf(u29,axiom,
    ( ~ v1_xboole_0(k3_tarski(k1_enumset1(X1,X1,X0)))
    | v1_xboole_0(X1) )).

cnf(u23,axiom,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0)) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0))) )).

cnf(u22,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:13:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (20865)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.46  % (20866)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (20866)Refutation not found, incomplete strategy% (20866)------------------------------
% 0.22/0.47  % (20866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (20866)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (20866)Memory used [KB]: 10490
% 0.22/0.47  % (20866)Time elapsed: 0.005 s
% 0.22/0.47  % (20866)------------------------------
% 0.22/0.47  % (20866)------------------------------
% 0.22/0.47  % (20859)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (20862)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (20859)Refutation not found, incomplete strategy% (20859)------------------------------
% 0.22/0.48  % (20859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20859)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (20859)Memory used [KB]: 6140
% 0.22/0.48  % (20859)Time elapsed: 0.051 s
% 0.22/0.48  % (20859)------------------------------
% 0.22/0.48  % (20859)------------------------------
% 0.22/0.48  % (20867)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (20870)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (20867)# SZS output start Saturation.
% 0.22/0.48  cnf(u34,negated_conjecture,
% 0.22/0.48      v1_xboole_0(k1_enumset1(sK0,sK0,sK0))).
% 0.22/0.48  
% 0.22/0.48  cnf(u26,negated_conjecture,
% 0.22/0.48      v1_xboole_0(sK1)).
% 0.22/0.48  
% 0.22/0.48  cnf(u14,axiom,
% 0.22/0.48      v1_xboole_0(k1_xboole_0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u24,axiom,
% 0.22/0.48      ~v1_xboole_0(k3_tarski(k1_enumset1(X1,X1,X0))) | v1_xboole_0(X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u29,axiom,
% 0.22/0.48      ~v1_xboole_0(k3_tarski(k1_enumset1(X1,X1,X0))) | v1_xboole_0(X1)).
% 0.22/0.48  
% 0.22/0.48  cnf(u23,axiom,
% 0.22/0.48      k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X1,X1,X0))).
% 0.22/0.48  
% 0.22/0.48  cnf(u27,negated_conjecture,
% 0.22/0.48      k1_xboole_0 = k3_tarski(k1_enumset1(sK1,sK1,k1_enumset1(sK0,sK0,sK0)))).
% 0.22/0.48  
% 0.22/0.48  cnf(u22,negated_conjecture,
% 0.22/0.48      k1_xboole_0 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),sK1))).
% 0.22/0.48  
% 0.22/0.48  % (20867)# SZS output end Saturation.
% 0.22/0.48  % (20867)------------------------------
% 0.22/0.48  % (20867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20867)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (20867)Memory used [KB]: 1535
% 0.22/0.48  % (20867)Time elapsed: 0.051 s
% 0.22/0.48  % (20867)------------------------------
% 0.22/0.48  % (20867)------------------------------
% 0.22/0.48  % (20854)Success in time 0.117 s
%------------------------------------------------------------------------------
