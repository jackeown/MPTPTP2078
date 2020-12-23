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
% DateTime   : Thu Dec  3 12:39:31 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    1 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u28,axiom,
    ( k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) )).

cnf(u27,axiom,
    ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) )).

cnf(u26,axiom,
    ( k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) )).

cnf(u30,axiom,
    ( k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0) )).

cnf(u21,axiom,
    ( k2_tarski(X0,X0) = k1_tarski(X0) )).

cnf(u25,axiom,
    ( k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) )).

cnf(u24,axiom,
    ( k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) )).

cnf(u23,axiom,
    ( k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

cnf(u29,axiom,
    ( k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) )).

cnf(u22,axiom,
    ( k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) )).

cnf(u20,negated_conjecture,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) )).

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
% 0.14/0.34  % DateTime   : Tue Dec  1 19:14:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (6311)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (6307)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (6313)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (6319)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (6311)# SZS output start Saturation.
% 0.21/0.46  cnf(u28,axiom,
% 0.21/0.46      k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)).
% 0.21/0.46  
% 0.21/0.46  cnf(u27,axiom,
% 0.21/0.46      k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)).
% 0.21/0.46  
% 0.21/0.46  cnf(u26,axiom,
% 0.21/0.46      k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)).
% 0.21/0.46  
% 0.21/0.46  cnf(u30,axiom,
% 0.21/0.46      k2_tarski(X0,X1) = k1_enumset1(X1,X0,X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u21,axiom,
% 0.21/0.46      k2_tarski(X0,X0) = k1_tarski(X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u25,axiom,
% 0.21/0.46      k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)).
% 0.21/0.46  
% 0.21/0.46  cnf(u24,axiom,
% 0.21/0.46      k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u23,axiom,
% 0.21/0.46      k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u29,axiom,
% 0.21/0.46      k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))).
% 0.21/0.46  
% 0.21/0.46  cnf(u22,axiom,
% 0.21/0.46      k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))).
% 0.21/0.46  
% 0.21/0.46  cnf(u20,negated_conjecture,
% 0.21/0.46      k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)).
% 0.21/0.46  
% 0.21/0.46  % (6311)# SZS output end Saturation.
% 0.21/0.46  % (6311)------------------------------
% 0.21/0.46  % (6311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (6311)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (6311)Memory used [KB]: 1663
% 0.21/0.46  % (6311)Time elapsed: 0.057 s
% 0.21/0.46  % (6311)------------------------------
% 0.21/0.46  % (6311)------------------------------
% 0.21/0.46  % (6303)Success in time 0.107 s
%------------------------------------------------------------------------------
