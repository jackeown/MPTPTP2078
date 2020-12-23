%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:31 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :    5 (   5 expanded)
%              Number of leaves         :    5 (   5 expanded)
%              Depth                    :    0
%              Number of atoms          :    7 (   7 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u14,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u27,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) )).

cnf(u26,negated_conjecture,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) )).

cnf(u28,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | k1_xboole_0 = sK0 )).

cnf(u24,axiom,
    ( k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (7180)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (7190)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (7177)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (7177)# SZS output start Saturation.
% 0.21/0.46  cnf(u14,axiom,
% 0.21/0.46      v1_xboole_0(k1_xboole_0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u27,negated_conjecture,
% 0.21/0.46      k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u26,negated_conjecture,
% 0.21/0.46      k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u28,negated_conjecture,
% 0.21/0.46      k1_xboole_0 != k3_tarski(k1_xboole_0) | k1_xboole_0 = sK0).
% 0.21/0.46  
% 0.21/0.46  cnf(u24,axiom,
% 0.21/0.46      k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = X0).
% 0.21/0.46  
% 0.21/0.46  % (7177)# SZS output end Saturation.
% 0.21/0.46  % (7177)------------------------------
% 0.21/0.46  % (7177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7177)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (7177)Memory used [KB]: 1535
% 0.21/0.46  % (7177)Time elapsed: 0.053 s
% 0.21/0.46  % (7177)------------------------------
% 0.21/0.46  % (7177)------------------------------
% 0.21/0.46  % (7174)Success in time 0.108 s
%------------------------------------------------------------------------------
