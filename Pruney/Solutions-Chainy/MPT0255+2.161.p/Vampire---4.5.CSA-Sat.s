%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:55 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   27 (  27 expanded)
%              Depth                    :    0
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   27 (  27 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u49,negated_conjecture,
    ( sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u34,axiom,
    ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) )).

cnf(u33,axiom,
    ( k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) )).

cnf(u32,axiom,
    ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) )).

cnf(u31,axiom,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) )).

cnf(u54,axiom,
    ( k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) )).

cnf(u30,axiom,
    ( k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) )).

cnf(u29,axiom,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) )).

cnf(u26,axiom,
    ( k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

cnf(u41,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) = k3_tarski(k1_xboole_0) )).

cnf(u25,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) )).

cnf(u52,axiom,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u85,axiom,
    ( k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1))) )).

cnf(u48,axiom,
    ( k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 )).

cnf(u59,axiom,
    ( k3_xboole_0(X0,X0) = X0 )).

cnf(u27,axiom,
    ( k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )).

cnf(u45,axiom,
    ( k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) )).

cnf(u28,axiom,
    ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

cnf(u23,axiom,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 )).

cnf(u36,negated_conjecture,
    ( k1_xboole_0 = k2_tarski(sK0,sK1) )).

cnf(u39,negated_conjecture,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK2) )).

cnf(u61,axiom,
    ( k1_xboole_0 = k5_xboole_0(X0,X0) )).

cnf(u53,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(sK0,sK0) )).

cnf(u22,axiom,
    ( k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

cnf(u42,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

cnf(u47,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,X0) )).

cnf(u24,axiom,
    ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:39:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (20647)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (20646)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (20649)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (20659)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (20650)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (20651)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (20657)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (20655)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (20658)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (20650)Refutation not found, incomplete strategy% (20650)------------------------------
% 0.21/0.49  % (20650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20650)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20650)Memory used [KB]: 6140
% 0.21/0.49  % (20650)Time elapsed: 0.048 s
% 0.21/0.49  % (20650)------------------------------
% 0.21/0.49  % (20650)------------------------------
% 0.21/0.49  % (20653)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (20652)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (20645)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (20648)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.50  % (20648)# SZS output start Saturation.
% 0.21/0.50  cnf(u49,negated_conjecture,
% 0.21/0.50      sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u34,axiom,
% 0.21/0.50      k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)).
% 0.21/0.50  
% 0.21/0.50  cnf(u33,axiom,
% 0.21/0.50      k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)).
% 0.21/0.50  
% 0.21/0.50  cnf(u32,axiom,
% 0.21/0.50      k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)).
% 0.21/0.50  
% 0.21/0.50  cnf(u31,axiom,
% 0.21/0.50      k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)).
% 0.21/0.50  
% 0.21/0.50  cnf(u54,axiom,
% 0.21/0.50      k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u30,axiom,
% 0.21/0.50      k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u29,axiom,
% 0.21/0.50      k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u26,axiom,
% 0.21/0.50      k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u41,negated_conjecture,
% 0.21/0.50      k2_xboole_0(sK0,sK1) = k3_tarski(k1_xboole_0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u25,axiom,
% 0.21/0.50      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u52,axiom,
% 0.21/0.50      k5_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u85,axiom,
% 0.21/0.50      k3_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k3_xboole_0(X0,X1)))).
% 0.21/0.50  
% 0.21/0.50  cnf(u48,axiom,
% 0.21/0.50      k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1).
% 0.21/0.50  
% 0.21/0.50  cnf(u59,axiom,
% 0.21/0.50      k3_xboole_0(X0,X0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u27,axiom,
% 0.21/0.50      k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u45,axiom,
% 0.21/0.50      k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))).
% 0.21/0.50  
% 0.21/0.50  cnf(u28,axiom,
% 0.21/0.50      k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))).
% 0.21/0.50  
% 0.21/0.50  cnf(u23,axiom,
% 0.21/0.50      k4_xboole_0(X0,k1_xboole_0) = X0).
% 0.21/0.50  
% 0.21/0.50  cnf(u36,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k2_tarski(sK0,sK1)).
% 0.21/0.50  
% 0.21/0.50  cnf(u39,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK2)).
% 0.21/0.50  
% 0.21/0.50  cnf(u61,axiom,
% 0.21/0.50      k1_xboole_0 = k5_xboole_0(X0,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u53,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k5_xboole_0(sK0,sK0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u22,axiom,
% 0.21/0.50      k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u42,negated_conjecture,
% 0.21/0.50      k1_xboole_0 = k4_xboole_0(sK0,k3_tarski(k1_xboole_0))).
% 0.21/0.50  
% 0.21/0.50  cnf(u47,axiom,
% 0.21/0.50      k1_xboole_0 = k4_xboole_0(X0,X0)).
% 0.21/0.50  
% 0.21/0.50  cnf(u24,axiom,
% 0.21/0.50      k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))).
% 0.21/0.50  
% 0.21/0.50  % (20648)# SZS output end Saturation.
% 0.21/0.50  % (20648)------------------------------
% 0.21/0.50  % (20648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20648)Termination reason: Satisfiable
% 0.21/0.50  
% 0.21/0.50  % (20648)Memory used [KB]: 1663
% 0.21/0.50  % (20648)Time elapsed: 0.094 s
% 0.21/0.50  % (20648)------------------------------
% 0.21/0.50  % (20648)------------------------------
% 0.21/0.51  % (20639)Success in time 0.149 s
%------------------------------------------------------------------------------
