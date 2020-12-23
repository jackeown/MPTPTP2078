%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:48 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :    6 (   6 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal clause size      :    2 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u14,axiom,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 )).

cnf(u11,axiom,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u13,axiom,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) )).

cnf(u15,negated_conjecture,
    ( k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (18731)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.41  % (18731)# SZS output start Saturation.
% 0.21/0.41  cnf(u14,axiom,
% 0.21/0.41      ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0).
% 0.21/0.41  
% 0.21/0.41  cnf(u11,axiom,
% 0.21/0.41      k2_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.41  
% 0.21/0.41  cnf(u13,axiom,
% 0.21/0.41      k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)).
% 0.21/0.41  
% 0.21/0.41  cnf(u15,negated_conjecture,
% 0.21/0.41      k1_xboole_0 != k2_xboole_0(k4_xboole_0(sK0,sK0),k4_xboole_0(sK0,sK0))).
% 0.21/0.41  
% 0.21/0.41  % (18731)# SZS output end Saturation.
% 0.21/0.41  % (18731)------------------------------
% 0.21/0.41  % (18731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (18731)Termination reason: Satisfiable
% 0.21/0.41  
% 0.21/0.41  % (18731)Memory used [KB]: 1535
% 0.21/0.41  % (18731)Time elapsed: 0.002 s
% 0.21/0.41  % (18731)------------------------------
% 0.21/0.41  % (18731)------------------------------
% 0.21/0.41  % (18717)Success in time 0.055 s
%------------------------------------------------------------------------------
