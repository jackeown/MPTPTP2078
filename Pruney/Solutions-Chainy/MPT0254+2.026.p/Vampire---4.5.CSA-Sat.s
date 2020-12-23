%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
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
%              Number of atoms          :   12 (  12 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u17,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u43,axiom,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

cnf(u32,axiom,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 )).

cnf(u34,axiom,
    ( k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) )).

cnf(u18,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u49,negated_conjecture,
    ( k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) )).

cnf(u38,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u51,axiom,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

cnf(u53,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u37,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u44,axiom,
    ( k1_xboole_0 = k4_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) )).

cnf(u33,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.42  % (28448)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.43  % (28453)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.43  % (28453)# SZS output start Saturation.
% 0.22/0.43  cnf(u17,axiom,
% 0.22/0.43      v1_xboole_0(k1_xboole_0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u43,axiom,
% 0.22/0.43      k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0).
% 0.22/0.43  
% 0.22/0.43  cnf(u32,axiom,
% 0.22/0.43      k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0).
% 0.22/0.43  
% 0.22/0.43  cnf(u34,axiom,
% 0.22/0.43      k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u18,axiom,
% 0.22/0.43      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.22/0.43  
% 0.22/0.43  cnf(u49,negated_conjecture,
% 0.22/0.43      k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u38,negated_conjecture,
% 0.22/0.43      k1_xboole_0 = sK1).
% 0.22/0.43  
% 0.22/0.43  cnf(u51,axiom,
% 0.22/0.43      k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u53,negated_conjecture,
% 0.22/0.43      k1_xboole_0 = k4_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.22/0.43  
% 0.22/0.43  cnf(u37,axiom,
% 0.22/0.43      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.22/0.43  
% 0.22/0.43  cnf(u44,axiom,
% 0.22/0.43      k1_xboole_0 = k4_xboole_0(X1,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1)))).
% 0.22/0.43  
% 0.22/0.43  cnf(u33,axiom,
% 0.22/0.43      k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))).
% 0.22/0.43  
% 0.22/0.43  % (28453)# SZS output end Saturation.
% 0.22/0.43  % (28453)------------------------------
% 0.22/0.43  % (28453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (28453)Termination reason: Satisfiable
% 0.22/0.43  
% 0.22/0.43  % (28453)Memory used [KB]: 1663
% 0.22/0.43  % (28453)Time elapsed: 0.005 s
% 0.22/0.43  % (28453)------------------------------
% 0.22/0.43  % (28453)------------------------------
% 0.22/0.43  % (28439)Success in time 0.065 s
%------------------------------------------------------------------------------
