%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:16 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   29 (  29 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    0
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u73,negated_conjecture,
    ( r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u103,axiom,
    ( r1_tarski(k5_xboole_0(X1,X1),X1) )).

cnf(u86,axiom,
    ( r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2) )).

cnf(u88,axiom,
    ( r1_tarski(k3_xboole_0(X6,X7),X6) )).

cnf(u91,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u54,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) )).

cnf(u92,axiom,
    ( r1_tarski(X1,X1) )).

cnf(u59,axiom,
    ( r1_tarski(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2))) )).

cnf(u45,axiom,
    ( r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )).

cnf(u33,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u23,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u74,negated_conjecture,
    ( sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u82,axiom,
    ( k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,X1))) = X1 )).

cnf(u109,axiom,
    ( k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 )).

cnf(u89,axiom,
    ( k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

cnf(u47,axiom,
    ( k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 )).

cnf(u46,axiom,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) )).

cnf(u85,axiom,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) )).

cnf(u115,axiom,
    ( k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X0) )).

cnf(u25,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u87,axiom,
    ( k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X4) )).

cnf(u96,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u58,axiom,
    ( k3_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = X0 )).

cnf(u49,axiom,
    ( k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0 )).

cnf(u52,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u69,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )).

cnf(u67,negated_conjecture,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

cnf(u95,axiom,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u24,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:46:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (31672)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (31672)# SZS output start Saturation.
% 0.20/0.48  cnf(u73,negated_conjecture,
% 0.20/0.48      r1_tarski(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u103,axiom,
% 0.20/0.48      r1_tarski(k5_xboole_0(X1,X1),X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u86,axiom,
% 0.20/0.48      r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X3)),X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u88,axiom,
% 0.20/0.48      r1_tarski(k3_xboole_0(X6,X7),X6)).
% 0.20/0.48  
% 0.20/0.48  cnf(u91,axiom,
% 0.20/0.48      r1_tarski(k1_xboole_0,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u54,negated_conjecture,
% 0.20/0.48      r1_tarski(k1_xboole_0,k1_xboole_0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u92,axiom,
% 0.20/0.48      r1_tarski(X1,X1)).
% 0.20/0.48  
% 0.20/0.48  cnf(u59,axiom,
% 0.20/0.48      r1_tarski(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2)))).
% 0.20/0.48  
% 0.20/0.48  cnf(u45,axiom,
% 0.20/0.48      r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))).
% 0.20/0.48  
% 0.20/0.48  cnf(u33,axiom,
% 0.20/0.48      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u23,axiom,
% 0.20/0.48      v1_xboole_0(k1_xboole_0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u74,negated_conjecture,
% 0.20/0.48      sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u82,axiom,
% 0.20/0.48      k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_xboole_0(X1,X1))) = X1).
% 0.20/0.48  
% 0.20/0.48  cnf(u109,axiom,
% 0.20/0.48      k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u89,axiom,
% 0.20/0.48      k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u47,axiom,
% 0.20/0.48      k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u46,axiom,
% 0.20/0.48      k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u85,axiom,
% 0.20/0.48      k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u115,axiom,
% 0.20/0.48      k5_xboole_0(X0,X0) = k3_xboole_0(k5_xboole_0(X0,X0),X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u25,axiom,
% 0.20/0.48      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u87,axiom,
% 0.20/0.48      k3_xboole_0(X4,X5) = k3_xboole_0(k3_xboole_0(X4,X5),X4)).
% 0.20/0.48  
% 0.20/0.48  cnf(u96,axiom,
% 0.20/0.48      k3_xboole_0(X0,X0) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u58,axiom,
% 0.20/0.48      k3_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u49,axiom,
% 0.20/0.48      k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0).
% 0.20/0.48  
% 0.20/0.48  cnf(u52,negated_conjecture,
% 0.20/0.48      k1_xboole_0 = sK1).
% 0.20/0.48  
% 0.20/0.48  cnf(u69,negated_conjecture,
% 0.20/0.48      k1_xboole_0 = k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))).
% 0.20/0.48  
% 0.20/0.48  cnf(u67,negated_conjecture,
% 0.20/0.48      k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u95,axiom,
% 0.20/0.48      k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u24,axiom,
% 0.20/0.48      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.48  
% 0.20/0.48  % (31672)# SZS output end Saturation.
% 0.20/0.48  % (31672)------------------------------
% 0.20/0.48  % (31672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31672)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (31672)Memory used [KB]: 1663
% 0.20/0.48  % (31672)Time elapsed: 0.053 s
% 0.20/0.48  % (31672)------------------------------
% 0.20/0.48  % (31672)------------------------------
% 0.20/0.48  % (31670)Success in time 0.122 s
%------------------------------------------------------------------------------
