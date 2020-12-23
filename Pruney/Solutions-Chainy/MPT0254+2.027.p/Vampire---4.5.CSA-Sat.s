%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:16 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u55,negated_conjecture,
    ( r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

% (23110)Refutation not found, incomplete strategy% (23110)------------------------------
% (23110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23110)Termination reason: Refutation not found, incomplete strategy

% (23110)Memory used [KB]: 1663
% (23110)Time elapsed: 0.062 s
% (23110)------------------------------
% (23110)------------------------------
cnf(u52,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u38,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u45,axiom,
    ( r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) )).

cnf(u34,axiom,
    ( r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )).

cnf(u21,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u18,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u35,axiom,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) )).

cnf(u50,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) )).

cnf(u39,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u44,axiom,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

cnf(u33,axiom,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:02:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (23108)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (23116)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (23112)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (23115)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (23120)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (23110)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (23107)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (23112)Refutation not found, incomplete strategy% (23112)------------------------------
% 0.22/0.48  % (23112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23112)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23112)Memory used [KB]: 6140
% 0.22/0.48  % (23112)Time elapsed: 0.052 s
% 0.22/0.48  % (23112)------------------------------
% 0.22/0.48  % (23112)------------------------------
% 0.22/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.48  % (23120)# SZS output start Saturation.
% 0.22/0.48  cnf(u55,negated_conjecture,
% 0.22/0.48      r1_tarski(sK0,k3_tarski(k1_xboole_0))).
% 0.22/0.48  
% 0.22/0.48  % (23110)Refutation not found, incomplete strategy% (23110)------------------------------
% 0.22/0.48  % (23110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23110)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23110)Memory used [KB]: 1663
% 0.22/0.48  % (23110)Time elapsed: 0.062 s
% 0.22/0.48  % (23110)------------------------------
% 0.22/0.48  % (23110)------------------------------
% 0.22/0.48  cnf(u52,axiom,
% 0.22/0.48      r1_tarski(k1_xboole_0,X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u38,axiom,
% 0.22/0.48      r1_tarski(X0,X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u45,axiom,
% 0.22/0.48      r1_tarski(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))).
% 0.22/0.48  
% 0.22/0.48  cnf(u34,axiom,
% 0.22/0.48      r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))).
% 0.22/0.48  
% 0.22/0.48  cnf(u21,axiom,
% 0.22/0.48      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.22/0.48  
% 0.22/0.48  cnf(u18,axiom,
% 0.22/0.48      v1_xboole_0(k1_xboole_0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u35,axiom,
% 0.22/0.48      k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u50,negated_conjecture,
% 0.22/0.48      k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)).
% 0.22/0.48  
% 0.22/0.48  cnf(u39,negated_conjecture,
% 0.22/0.48      k1_xboole_0 = sK1).
% 0.22/0.48  
% 0.22/0.48  cnf(u44,axiom,
% 0.22/0.48      k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0).
% 0.22/0.48  
% 0.22/0.48  cnf(u33,axiom,
% 0.22/0.48      k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0).
% 0.22/0.48  
% 0.22/0.48  % (23120)# SZS output end Saturation.
% 0.22/0.48  % (23120)------------------------------
% 0.22/0.48  % (23120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23120)Termination reason: Satisfiable
% 0.22/0.48  
% 0.22/0.48  % (23120)Memory used [KB]: 1663
% 0.22/0.48  % (23120)Time elapsed: 0.052 s
% 0.22/0.48  % (23120)------------------------------
% 0.22/0.48  % (23120)------------------------------
% 0.22/0.48  % (23106)Success in time 0.119 s
%------------------------------------------------------------------------------
