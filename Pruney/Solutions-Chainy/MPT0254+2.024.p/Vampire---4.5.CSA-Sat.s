%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:16 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   34 (  34 expanded)
%              Number of leaves         :   34 (  34 expanded)
%              Depth                    :    0
%              Number of atoms          :   40 (  40 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u83,negated_conjecture,
    ( r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u131,axiom,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) )).

cnf(u108,axiom,
    ( r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2) )).

cnf(u115,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u110,axiom,
    ( r1_tarski(k3_xboole_0(X6,X7),X6) )).

cnf(u116,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u70,axiom,
    ( r1_tarski(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2))) )).

cnf(u49,axiom,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )).

cnf(u35,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u25,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u112,axiom,
    ( r1_xboole_0(k1_xboole_0,X0) )).

cnf(u26,axiom,
    ( r1_xboole_0(X0,k1_xboole_0) )).

cnf(u36,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u84,negated_conjecture,
    ( sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u104,axiom,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,X1))) = X1 )).

cnf(u162,axiom,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 )).

cnf(u111,axiom,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

cnf(u51,axiom,
    ( k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 )).

cnf(u50,axiom,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) )).

cnf(u107,axiom,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) )).

cnf(u137,axiom,
    ( k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X0) )).

cnf(u27,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u59,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u80,negated_conjecture,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

cnf(u113,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u53,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u109,axiom,
    ( k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X4) )).

cnf(u120,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u69,axiom,
    ( k3_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = X0 )).

cnf(u56,axiom,
    ( k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0 )).

cnf(u65,axiom,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )).

cnf(u101,axiom,
    ( k1_xboole_0 != X1
    | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) )).

cnf(u123,axiom,
    ( k1_xboole_0 != X2
    | r1_xboole_0(X2,X2) )).

cnf(u37,axiom,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (4215)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.43  % (4215)Refutation not found, incomplete strategy% (4215)------------------------------
% 0.21/0.43  % (4215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (4215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (4215)Memory used [KB]: 10618
% 0.21/0.44  % (4215)Time elapsed: 0.005 s
% 0.21/0.44  % (4215)------------------------------
% 0.21/0.44  % (4215)------------------------------
% 0.21/0.47  % (4217)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (4217)# SZS output start Saturation.
% 0.21/0.47  cnf(u83,negated_conjecture,
% 0.21/0.47      r1_tarski(sK0,k3_tarski(k1_xboole_0))).
% 0.21/0.47  
% 0.21/0.47  cnf(u131,axiom,
% 0.21/0.47      r1_tarski(k5_xboole_0(X1,X1),X1)).
% 0.21/0.47  
% 0.21/0.47  cnf(u108,axiom,
% 0.21/0.47      r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)).
% 0.21/0.47  
% 0.21/0.47  cnf(u115,axiom,
% 0.21/0.47      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u110,axiom,
% 0.21/0.47      r1_tarski(k3_xboole_0(X6,X7),X6)).
% 0.21/0.47  
% 0.21/0.47  cnf(u116,axiom,
% 0.21/0.47      r1_tarski(X1,X1)).
% 0.21/0.47  
% 0.21/0.47  cnf(u70,axiom,
% 0.21/0.47      r1_tarski(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2)))).
% 0.21/0.47  
% 0.21/0.47  cnf(u49,axiom,
% 0.21/0.47      r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))).
% 0.21/0.47  
% 0.21/0.47  cnf(u35,axiom,
% 0.21/0.47      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u25,axiom,
% 0.21/0.47      v1_xboole_0(k1_xboole_0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u112,axiom,
% 0.21/0.47      r1_xboole_0(k1_xboole_0,X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u26,axiom,
% 0.21/0.47      r1_xboole_0(X0,k1_xboole_0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u36,axiom,
% 0.21/0.47      ~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.47  
% 0.21/0.47  cnf(u84,negated_conjecture,
% 0.21/0.47      sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.21/0.47  
% 0.21/0.47  cnf(u104,axiom,
% 0.21/0.47      k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,X1))) = X1).
% 0.21/0.47  
% 0.21/0.47  cnf(u162,axiom,
% 0.21/0.47      k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u111,axiom,
% 0.21/0.47      k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u51,axiom,
% 0.21/0.47      k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u50,axiom,
% 0.21/0.47      k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u107,axiom,
% 0.21/0.47      k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u137,axiom,
% 0.21/0.47      k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u27,axiom,
% 0.21/0.47      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u59,negated_conjecture,
% 0.21/0.47      k1_xboole_0 = sK1).
% 0.21/0.47  
% 0.21/0.47  cnf(u80,negated_conjecture,
% 0.21/0.47      k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u113,axiom,
% 0.21/0.47      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u53,axiom,
% 0.21/0.47      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u109,axiom,
% 0.21/0.47      k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X4)).
% 0.21/0.47  
% 0.21/0.47  cnf(u120,axiom,
% 0.21/0.47      k3_xboole_0(X0,X0) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u69,axiom,
% 0.21/0.47      k3_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u56,axiom,
% 0.21/0.47      k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0).
% 0.21/0.47  
% 0.21/0.47  cnf(u65,axiom,
% 0.21/0.47      k1_xboole_0 != X0 | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))).
% 0.21/0.47  
% 0.21/0.47  cnf(u101,axiom,
% 0.21/0.47      k1_xboole_0 != X1 | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))).
% 0.21/0.47  
% 0.21/0.47  cnf(u123,axiom,
% 0.21/0.47      k1_xboole_0 != X2 | r1_xboole_0(X2,X2)).
% 0.21/0.47  
% 0.21/0.47  cnf(u37,axiom,
% 0.21/0.47      k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)).
% 0.21/0.47  
% 0.21/0.47  % (4217)# SZS output end Saturation.
% 0.21/0.47  % (4217)------------------------------
% 0.21/0.47  % (4217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (4217)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (4217)Memory used [KB]: 1663
% 0.21/0.47  % (4217)Time elapsed: 0.056 s
% 0.21/0.47  % (4217)------------------------------
% 0.21/0.47  % (4217)------------------------------
% 0.21/0.47  % (4214)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (4203)Success in time 0.116 s
%------------------------------------------------------------------------------
