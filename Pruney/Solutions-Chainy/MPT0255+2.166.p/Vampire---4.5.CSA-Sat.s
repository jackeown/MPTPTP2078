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
% DateTime   : Thu Dec  3 12:39:55 EST 2020

% Result     : CounterSatisfiable 0.17s
% Output     : Saturation 0.17s
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
cnf(u13,axiom,
    ( v1_xboole_0(k1_xboole_0) )).

cnf(u24,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) )).

cnf(u23,negated_conjecture,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1) )).

cnf(u25,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | k1_xboole_0 = sK0 )).

cnf(u21,axiom,
    ( k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))
    | k1_xboole_0 = X0 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n006.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:09:52 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.43  % (27758)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.17/0.43  % (27750)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.17/0.43  % (27751)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.17/0.43  % (27750)Refutation not found, incomplete strategy% (27750)------------------------------
% 0.17/0.43  % (27750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.43  % (27750)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.43  
% 0.17/0.43  % (27750)Memory used [KB]: 6140
% 0.17/0.43  % (27750)Time elapsed: 0.047 s
% 0.17/0.43  % (27750)------------------------------
% 0.17/0.43  % (27750)------------------------------
% 0.17/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.17/0.43  % (27758)# SZS output start Saturation.
% 0.17/0.43  cnf(u13,axiom,
% 0.17/0.43      v1_xboole_0(k1_xboole_0)).
% 0.17/0.43  
% 0.17/0.43  cnf(u24,negated_conjecture,
% 0.17/0.43      k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))).
% 0.17/0.43  
% 0.17/0.43  cnf(u23,negated_conjecture,
% 0.17/0.43      k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK1)).
% 0.17/0.43  
% 0.17/0.43  cnf(u25,negated_conjecture,
% 0.17/0.43      k1_xboole_0 != k3_tarski(k1_xboole_0) | k1_xboole_0 = sK0).
% 0.17/0.43  
% 0.17/0.43  cnf(u21,axiom,
% 0.17/0.43      k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1)) | k1_xboole_0 = X0).
% 0.17/0.43  
% 0.17/0.43  % (27758)# SZS output end Saturation.
% 0.17/0.43  % (27758)------------------------------
% 0.17/0.43  % (27758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.43  % (27758)Termination reason: Satisfiable
% 0.17/0.43  
% 0.17/0.43  % (27758)Memory used [KB]: 1663
% 0.17/0.43  % (27758)Time elapsed: 0.050 s
% 0.17/0.43  % (27758)------------------------------
% 0.17/0.43  % (27758)------------------------------
% 0.17/0.44  % (27744)Success in time 0.101 s
%------------------------------------------------------------------------------
