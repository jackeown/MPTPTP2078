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
% DateTime   : Thu Dec  3 12:39:45 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :   15 (  15 expanded)
%              Depth                    :    0
%              Number of atoms          :   20 (  20 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u46,negated_conjecture,
    ( r1_tarski(sK1,k3_tarski(k1_xboole_0)) )).

cnf(u39,negated_conjecture,
    ( r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u35,negated_conjecture,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) )).

cnf(u43,axiom,
    ( r1_tarski(X2,k3_tarski(k2_enumset1(X3,X3,X3,X2))) )).

cnf(u28,axiom,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) )).

cnf(u18,axiom,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 )).

cnf(u17,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u38,negated_conjecture,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | v1_xboole_0(sK1) )).

cnf(u57,negated_conjecture,
    ( ~ v1_xboole_0(k3_tarski(k1_xboole_0))
    | v1_xboole_0(sK0) )).

cnf(u30,axiom,
    ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0)))
    | v1_xboole_0(X0) )).

cnf(u42,axiom,
    ( ~ v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0)))
    | v1_xboole_0(X1) )).

cnf(u29,axiom,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) )).

cnf(u52,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )).

cnf(u50,negated_conjecture,
    ( k1_xboole_0 = sK2 )).

cnf(u34,negated_conjecture,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (26398)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.46  % (26398)# SZS output start Saturation.
% 0.22/0.46  cnf(u46,negated_conjecture,
% 0.22/0.46      r1_tarski(sK1,k3_tarski(k1_xboole_0))).
% 0.22/0.46  
% 0.22/0.46  cnf(u39,negated_conjecture,
% 0.22/0.46      r1_tarski(sK0,k3_tarski(k1_xboole_0))).
% 0.22/0.46  
% 0.22/0.46  cnf(u35,negated_conjecture,
% 0.22/0.46      r1_tarski(k1_xboole_0,k1_xboole_0)).
% 0.22/0.46  
% 0.22/0.46  cnf(u43,axiom,
% 0.22/0.46      r1_tarski(X2,k3_tarski(k2_enumset1(X3,X3,X3,X2)))).
% 0.22/0.46  
% 0.22/0.46  cnf(u28,axiom,
% 0.22/0.46      r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))).
% 0.22/0.46  
% 0.22/0.46  cnf(u18,axiom,
% 0.22/0.46      ~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0).
% 0.22/0.46  
% 0.22/0.46  cnf(u17,axiom,
% 0.22/0.46      v1_xboole_0(k1_xboole_0)).
% 0.22/0.46  
% 0.22/0.46  cnf(u38,negated_conjecture,
% 0.22/0.46      ~v1_xboole_0(k3_tarski(k1_xboole_0)) | v1_xboole_0(sK1)).
% 0.22/0.46  
% 0.22/0.46  cnf(u57,negated_conjecture,
% 0.22/0.46      ~v1_xboole_0(k3_tarski(k1_xboole_0)) | v1_xboole_0(sK0)).
% 0.22/0.46  
% 0.22/0.46  cnf(u30,axiom,
% 0.22/0.46      ~v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0))) | v1_xboole_0(X0)).
% 0.22/0.46  
% 0.22/0.46  cnf(u42,axiom,
% 0.22/0.46      ~v1_xboole_0(k3_tarski(k2_enumset1(X1,X1,X1,X0))) | v1_xboole_0(X1)).
% 0.22/0.46  
% 0.22/0.46  cnf(u29,axiom,
% 0.22/0.46      k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))).
% 0.22/0.46  
% 0.22/0.46  cnf(u52,negated_conjecture,
% 0.22/0.46      k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))).
% 0.22/0.46  
% 0.22/0.46  cnf(u50,negated_conjecture,
% 0.22/0.46      k1_xboole_0 = sK2).
% 0.22/0.46  
% 0.22/0.46  cnf(u34,negated_conjecture,
% 0.22/0.46      k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)).
% 0.22/0.46  
% 0.22/0.47  % (26398)# SZS output end Saturation.
% 0.22/0.47  % (26398)------------------------------
% 0.22/0.47  % (26398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26398)Termination reason: Satisfiable
% 0.22/0.47  
% 0.22/0.47  % (26398)Memory used [KB]: 1663
% 0.22/0.47  % (26398)Time elapsed: 0.006 s
% 0.22/0.47  % (26398)------------------------------
% 0.22/0.47  % (26398)------------------------------
% 0.22/0.47  % (26388)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (26382)Success in time 0.105 s
%------------------------------------------------------------------------------
