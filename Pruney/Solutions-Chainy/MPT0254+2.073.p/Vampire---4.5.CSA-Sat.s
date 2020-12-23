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
% DateTime   : Thu Dec  3 12:39:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u47,axiom,
    ( r1_tarski(X0,X0) )).

cnf(u42,axiom,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) )).

cnf(u33,axiom,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) )).

cnf(u20,axiom,
    ( r1_tarski(k1_xboole_0,X0) )).

cnf(u35,axiom,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 )).

cnf(u22,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u19,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u75,negated_conjecture,
    ( sK0 = k3_tarski(k1_xboole_0) )).

cnf(u70,negated_conjecture,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) )).

cnf(u66,negated_conjecture,
    ( k1_xboole_0 = sK1 )).

cnf(u38,axiom,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X1,X1,X1,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )).

cnf(u46,axiom,
    ( k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )).

cnf(u34,axiom,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) )).

cnf(u51,axiom,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 )).

cnf(u40,axiom,
    ( k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 )).

cnf(u37,axiom,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:32:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (24670)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.42  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.42  % (24670)# SZS output start Saturation.
% 0.21/0.42  cnf(u47,axiom,
% 0.21/0.42      r1_tarski(X0,X0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u42,axiom,
% 0.21/0.42      r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))).
% 0.21/0.42  
% 0.21/0.42  cnf(u33,axiom,
% 0.21/0.42      r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))).
% 0.21/0.42  
% 0.21/0.42  cnf(u20,axiom,
% 0.21/0.42      r1_tarski(k1_xboole_0,X0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u35,axiom,
% 0.21/0.42      ~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1).
% 0.21/0.42  
% 0.21/0.42  cnf(u22,axiom,
% 0.21/0.42      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.21/0.42  
% 0.21/0.42  cnf(u19,axiom,
% 0.21/0.42      v1_xboole_0(k1_xboole_0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u75,negated_conjecture,
% 0.21/0.42      sK0 = k3_tarski(k1_xboole_0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u70,negated_conjecture,
% 0.21/0.42      k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)).
% 0.21/0.42  
% 0.21/0.42  cnf(u66,negated_conjecture,
% 0.21/0.42      k1_xboole_0 = sK1).
% 0.21/0.42  
% 0.21/0.42  cnf(u38,axiom,
% 0.21/0.42      k3_tarski(k2_enumset1(X1,X1,X1,X2)) = k3_tarski(k2_enumset1(X1,X1,X1,k3_tarski(k2_enumset1(X1,X1,X1,X2))))).
% 0.21/0.42  
% 0.21/0.43  cnf(u46,axiom,
% 0.21/0.43      k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))))).
% 0.21/0.43  
% 0.21/0.43  cnf(u34,axiom,
% 0.21/0.43      k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))).
% 0.21/0.43  
% 0.21/0.43  cnf(u51,axiom,
% 0.21/0.43      k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0).
% 0.21/0.43  
% 0.21/0.43  cnf(u40,axiom,
% 0.21/0.43      k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0).
% 0.21/0.43  
% 0.21/0.43  cnf(u37,axiom,
% 0.21/0.43      k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0).
% 0.21/0.43  
% 0.21/0.43  % (24670)# SZS output end Saturation.
% 0.21/0.43  % (24670)------------------------------
% 0.21/0.43  % (24670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (24670)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (24670)Memory used [KB]: 1663
% 0.21/0.43  % (24670)Time elapsed: 0.006 s
% 0.21/0.43  % (24670)------------------------------
% 0.21/0.43  % (24670)------------------------------
% 0.21/0.43  % (24657)Success in time 0.063 s
%------------------------------------------------------------------------------
