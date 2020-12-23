%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:01 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   45 (  45 expanded)
%              Number of leaves         :   45 (  45 expanded)
%              Depth                    :    0
%              Number of atoms          :   76 (  76 expanded)
%              Number of equality atoms :   42 (  42 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u115,negated_conjecture,
    ( r2_hidden(sK0,X1)
    | r1_xboole_0(k1_xboole_0,X1) )).

cnf(u136,negated_conjecture,
    ( r2_hidden(sK0,X1)
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) )).

cnf(u94,negated_conjecture,
    ( r2_hidden(sK0,sK1) )).

cnf(u74,axiom,
    ( r2_hidden(X0,X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )).

cnf(u66,axiom,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) )).

cnf(u112,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,sK1) )).

cnf(u82,axiom,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) )).

cnf(u79,axiom,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

cnf(u130,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X0)
    | r1_tarski(k1_xboole_0,X0) )).

cnf(u146,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u154,negated_conjecture,
    ( r1_xboole_0(k1_xboole_0,X0)
    | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u63,axiom,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) )).

cnf(u184,axiom,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) )).

cnf(u193,axiom,
    ( r1_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) )).

cnf(u65,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 )).

cnf(u87,axiom,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )).

cnf(u131,negated_conjecture,
    ( r1_tarski(k1_xboole_0,X0)
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) )).

cnf(u113,negated_conjecture,
    ( r1_tarski(k1_xboole_0,sK1) )).

cnf(u114,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,X0)
    | r2_hidden(sK0,X0) )).

cnf(u67,axiom,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) )).

cnf(u42,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 )).

cnf(u32,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u116,negated_conjecture,
    ( sK0 = k3_tarski(k1_xboole_0) )).

cnf(u61,axiom,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 )).

cnf(u201,axiom,
    ( k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5) = k3_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),X6)),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))
    | k1_xboole_0 = k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5) )).

cnf(u179,axiom,
    ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)))
    | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) )).

cnf(u177,axiom,
    ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )).

cnf(u158,axiom,
    ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))
    | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3) )).

cnf(u195,axiom,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )).

cnf(u110,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0) )).

cnf(u111,negated_conjecture,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) )).

cnf(u109,negated_conjecture,
    ( k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

cnf(u141,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))
    | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u135,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) )).

cnf(u156,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))
    | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u77,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u62,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )).

cnf(u37,axiom,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

cnf(u35,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u212,axiom,
    ( k3_tarski(k6_enumset1(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),X7)) != k5_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),X7)),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))
    | r1_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),X7)),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))
    | k1_xboole_0 = k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6) )).

cnf(u120,negated_conjecture,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | r1_xboole_0(sK1,k1_xboole_0) )).

cnf(u78,axiom,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,X0) )).

cnf(u76,axiom,
    ( k1_xboole_0 != X0
    | r1_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )).

cnf(u69,axiom,
    ( k5_xboole_0(X1,k3_xboole_0(X2,X1)) != X1
    | r1_xboole_0(X1,X2) )).

cnf(u64,axiom,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0
    | r1_xboole_0(X0,X1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (30993)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.41  % (30993)# SZS output start Saturation.
% 0.20/0.41  cnf(u115,negated_conjecture,
% 0.20/0.41      r2_hidden(sK0,X1) | r1_xboole_0(k1_xboole_0,X1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u136,negated_conjecture,
% 0.20/0.41      r2_hidden(sK0,X1) | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))).
% 0.20/0.41  
% 0.20/0.41  cnf(u94,negated_conjecture,
% 0.20/0.41      r2_hidden(sK0,sK1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u74,axiom,
% 0.20/0.41      r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))).
% 0.20/0.41  
% 0.20/0.41  cnf(u66,axiom,
% 0.20/0.41      ~r2_hidden(X0,X1) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u112,negated_conjecture,
% 0.20/0.41      r1_xboole_0(k1_xboole_0,sK1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u82,axiom,
% 0.20/0.41      r1_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)))).
% 0.20/0.41  
% 0.20/0.41  cnf(u79,axiom,
% 0.20/0.41      r1_xboole_0(k1_xboole_0,k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u130,negated_conjecture,
% 0.20/0.41      r1_xboole_0(k1_xboole_0,X0) | r1_tarski(k1_xboole_0,X0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u146,negated_conjecture,
% 0.20/0.41      r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u154,negated_conjecture,
% 0.20/0.41      r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u63,axiom,
% 0.20/0.41      r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u184,axiom,
% 0.20/0.41      r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u193,axiom,
% 0.20/0.41      r1_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(X3,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))).
% 0.20/0.41  
% 0.20/0.41  cnf(u65,axiom,
% 0.20/0.41      ~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0).
% 0.20/0.41  
% 0.20/0.41  cnf(u87,axiom,
% 0.20/0.41      r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))).
% 0.20/0.41  
% 0.20/0.41  cnf(u131,negated_conjecture,
% 0.20/0.41      r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))).
% 0.20/0.41  
% 0.20/0.41  cnf(u113,negated_conjecture,
% 0.20/0.41      r1_tarski(k1_xboole_0,sK1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u114,negated_conjecture,
% 0.20/0.41      ~r1_tarski(k1_xboole_0,X0) | r2_hidden(sK0,X0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u67,axiom,
% 0.20/0.41      ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u42,axiom,
% 0.20/0.41      ~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0).
% 0.20/0.41  
% 0.20/0.41  cnf(u32,axiom,
% 0.20/0.41      v1_xboole_0(k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u116,negated_conjecture,
% 0.20/0.41      sK0 = k3_tarski(k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u61,axiom,
% 0.20/0.41      k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0).
% 0.20/0.41  
% 0.20/0.41  cnf(u201,axiom,
% 0.20/0.41      k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5) = k3_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),X6)),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)) | k1_xboole_0 = k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)).
% 0.20/0.41  
% 0.20/0.41  cnf(u179,axiom,
% 0.20/0.41      k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3))) | k1_xboole_0 = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)).
% 0.20/0.41  
% 0.20/0.41  cnf(u177,axiom,
% 0.20/0.41      k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = k3_xboole_0(X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))).
% 0.20/0.41  
% 0.20/0.41  cnf(u158,axiom,
% 0.20/0.41      k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),X3)).
% 0.20/0.41  
% 0.20/0.41  cnf(u195,axiom,
% 0.20/0.41      k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))).
% 0.20/0.41  
% 0.20/0.41  cnf(u110,negated_conjecture,
% 0.20/0.41      k1_xboole_0 = k3_xboole_0(sK1,k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u111,negated_conjecture,
% 0.20/0.41      k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)).
% 0.20/0.41  
% 0.20/0.41  cnf(u109,negated_conjecture,
% 0.20/0.41      k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u141,negated_conjecture,
% 0.20/0.41      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0)) | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u135,negated_conjecture,
% 0.20/0.41      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) | k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u156,negated_conjecture,
% 0.20/0.41      k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) | k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u77,axiom,
% 0.20/0.41      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u62,axiom,
% 0.20/0.41      k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))).
% 0.20/0.41  
% 0.20/0.41  cnf(u37,axiom,
% 0.20/0.41      k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u35,axiom,
% 0.20/0.41      k3_xboole_0(X0,X0) = X0).
% 0.20/0.41  
% 0.20/0.41  cnf(u212,axiom,
% 0.20/0.41      k3_tarski(k6_enumset1(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),X7)) != k5_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),X7)),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)) | r1_xboole_0(k3_tarski(k6_enumset1(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),X7)),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)) | k1_xboole_0 = k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)).
% 0.20/0.41  
% 0.20/0.41  cnf(u120,negated_conjecture,
% 0.20/0.41      sK1 != k5_xboole_0(sK1,k1_xboole_0) | r1_xboole_0(sK1,k1_xboole_0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u78,axiom,
% 0.20/0.41      k1_xboole_0 != X0 | r1_xboole_0(X0,X0)).
% 0.20/0.41  
% 0.20/0.41  cnf(u76,axiom,
% 0.20/0.41      k1_xboole_0 != X0 | r1_xboole_0(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))).
% 0.20/0.41  
% 0.20/0.41  cnf(u69,axiom,
% 0.20/0.41      k5_xboole_0(X1,k3_xboole_0(X2,X1)) != X1 | r1_xboole_0(X1,X2)).
% 0.20/0.41  
% 0.20/0.41  cnf(u64,axiom,
% 0.20/0.41      k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X0 | r1_xboole_0(X0,X1)).
% 0.20/0.41  
% 0.20/0.41  % (30993)# SZS output end Saturation.
% 0.20/0.41  % (30993)------------------------------
% 0.20/0.41  % (30993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (30993)Termination reason: Satisfiable
% 0.20/0.41  
% 0.20/0.41  % (30993)Memory used [KB]: 1663
% 0.20/0.41  % (30993)Time elapsed: 0.007 s
% 0.20/0.41  % (30993)------------------------------
% 0.20/0.41  % (30993)------------------------------
% 0.20/0.42  % (30980)Success in time 0.056 s
%------------------------------------------------------------------------------
