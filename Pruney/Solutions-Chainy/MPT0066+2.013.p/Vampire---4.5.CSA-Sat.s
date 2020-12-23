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
% DateTime   : Thu Dec  3 12:30:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   18 (  18 expanded)
%              Depth                    :    0
%              Number of atoms          :   26 (  26 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u48,negated_conjecture,
    ( r1_tarski(sK1,sK1) )).

cnf(u37,negated_conjecture,
    ( r1_tarski(sK1,sK0) )).

cnf(u34,negated_conjecture,
    ( r1_tarski(sK0,sK0) )).

cnf(u12,negated_conjecture,
    ( r1_tarski(sK0,sK1) )).

cnf(u27,negated_conjecture,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK0,X0) )).

cnf(u35,negated_conjecture,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK1,X0) )).

cnf(u20,axiom,
    ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
    | r1_tarski(X0,X2) )).

cnf(u16,axiom,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 )).

% (7252)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
cnf(u19,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u38,negated_conjecture,
    ( r2_xboole_0(sK1,sK0) )).

cnf(u24,negated_conjecture,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1 )).

cnf(u17,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) )).

cnf(u15,axiom,
    ( ~ r2_xboole_0(X0,X0) )).

cnf(u33,negated_conjecture,
    ( sK0 = sK2 )).

cnf(u40,negated_conjecture,
    ( sK0 = k2_xboole_0(sK0,sK0) )).

cnf(u36,negated_conjecture,
    ( sK0 = k2_xboole_0(sK1,sK0) )).

cnf(u52,negated_conjecture,
    ( sK1 = k2_xboole_0(sK1,sK1) )).

cnf(u23,negated_conjecture,
    ( sK1 = k2_xboole_0(sK0,sK1) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:27:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (7260)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (7260)# SZS output start Saturation.
% 0.21/0.46  cnf(u48,negated_conjecture,
% 0.21/0.46      r1_tarski(sK1,sK1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u37,negated_conjecture,
% 0.21/0.46      r1_tarski(sK1,sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u34,negated_conjecture,
% 0.21/0.46      r1_tarski(sK0,sK0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u12,negated_conjecture,
% 0.21/0.46      r1_tarski(sK0,sK1)).
% 0.21/0.46  
% 0.21/0.46  cnf(u27,negated_conjecture,
% 0.21/0.46      ~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u35,negated_conjecture,
% 0.21/0.46      ~r1_tarski(sK0,X0) | r1_tarski(sK1,X0)).
% 0.21/0.46  
% 0.21/0.46  cnf(u20,axiom,
% 0.21/0.46      ~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)).
% 0.21/0.46  
% 0.21/0.46  cnf(u16,axiom,
% 0.21/0.46      ~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1).
% 0.21/0.46  
% 0.21/0.47  % (7252)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  cnf(u19,axiom,
% 0.21/0.47      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.21/0.47  
% 0.21/0.47  cnf(u38,negated_conjecture,
% 0.21/0.47      r2_xboole_0(sK1,sK0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u24,negated_conjecture,
% 0.21/0.47      r2_xboole_0(sK0,sK1) | sK0 = sK1).
% 0.21/0.47  
% 0.21/0.47  cnf(u17,axiom,
% 0.21/0.47      ~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.21/0.47  
% 0.21/0.47  cnf(u15,axiom,
% 0.21/0.47      ~r2_xboole_0(X0,X0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u33,negated_conjecture,
% 0.21/0.47      sK0 = sK2).
% 0.21/0.47  
% 0.21/0.47  cnf(u40,negated_conjecture,
% 0.21/0.47      sK0 = k2_xboole_0(sK0,sK0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u36,negated_conjecture,
% 0.21/0.47      sK0 = k2_xboole_0(sK1,sK0)).
% 0.21/0.47  
% 0.21/0.47  cnf(u52,negated_conjecture,
% 0.21/0.47      sK1 = k2_xboole_0(sK1,sK1)).
% 0.21/0.47  
% 0.21/0.47  cnf(u23,negated_conjecture,
% 0.21/0.47      sK1 = k2_xboole_0(sK0,sK1)).
% 0.21/0.47  
% 0.21/0.47  % (7260)# SZS output end Saturation.
% 0.21/0.47  % (7260)------------------------------
% 0.21/0.47  % (7260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7260)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (7260)Memory used [KB]: 1663
% 0.21/0.47  % (7260)Time elapsed: 0.049 s
% 0.21/0.47  % (7260)------------------------------
% 0.21/0.47  % (7260)------------------------------
% 0.21/0.47  % (7242)Success in time 0.106 s
%------------------------------------------------------------------------------
