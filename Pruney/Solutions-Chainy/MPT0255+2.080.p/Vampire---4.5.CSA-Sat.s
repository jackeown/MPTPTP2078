%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:45 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
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
cnf(u37,negated_conjecture,
    ( v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) )).

cnf(u29,negated_conjecture,
    ( v1_xboole_0(sK2) )).

cnf(u15,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u27,axiom,
    ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
    | v1_xboole_0(X0) )).

cnf(u32,axiom,
    ( ~ v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))
    | v1_xboole_0(X1) )).

cnf(u26,axiom,
    ( k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) )).

cnf(u30,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) )).

cnf(u25,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:34:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (28038)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.41  % (28038)# SZS output start Saturation.
% 0.21/0.41  cnf(u37,negated_conjecture,
% 0.21/0.41      v1_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1))).
% 0.21/0.41  
% 0.21/0.41  cnf(u29,negated_conjecture,
% 0.21/0.41      v1_xboole_0(sK2)).
% 0.21/0.41  
% 0.21/0.41  cnf(u15,axiom,
% 0.21/0.41      v1_xboole_0(k1_xboole_0)).
% 0.21/0.41  
% 0.21/0.41  cnf(u27,axiom,
% 0.21/0.41      ~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X0)).
% 0.21/0.41  
% 0.21/0.41  cnf(u32,axiom,
% 0.21/0.41      ~v1_xboole_0(k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) | v1_xboole_0(X1)).
% 0.21/0.41  
% 0.21/0.41  cnf(u26,axiom,
% 0.21/0.41      k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))).
% 0.21/0.41  
% 0.21/0.41  cnf(u30,negated_conjecture,
% 0.21/0.41      k1_xboole_0 = k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))).
% 0.21/0.41  
% 0.21/0.41  cnf(u25,negated_conjecture,
% 0.21/0.41      k1_xboole_0 = k3_tarski(k3_enumset1(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))).
% 0.21/0.41  
% 0.21/0.41  % (28038)# SZS output end Saturation.
% 0.21/0.41  % (28038)------------------------------
% 0.21/0.41  % (28038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (28038)Termination reason: Satisfiable
% 0.21/0.41  
% 0.21/0.41  % (28038)Memory used [KB]: 1663
% 0.21/0.41  % (28038)Time elapsed: 0.003 s
% 0.21/0.41  % (28038)------------------------------
% 0.21/0.41  % (28038)------------------------------
% 0.21/0.41  % (28024)Success in time 0.055 s
%------------------------------------------------------------------------------
