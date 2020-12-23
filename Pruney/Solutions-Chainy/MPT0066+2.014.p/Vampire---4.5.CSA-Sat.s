%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:22 EST 2020

% Result     : CounterSatisfiable 0.19s
% Output     : Saturation 0.19s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u39,negated_conjecture,
    ( r1_tarski(sK1,sK1) )).

cnf(u30,negated_conjecture,
    ( r1_tarski(sK1,sK0) )).

cnf(u28,negated_conjecture,
    ( r1_tarski(sK0,sK0) )).

cnf(u9,negated_conjecture,
    ( r1_tarski(sK0,sK1) )).

cnf(u29,negated_conjecture,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK1,X0) )).

cnf(u19,negated_conjecture,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK0,X0) )).

cnf(u14,axiom,
    ( ~ r1_tarski(X0,X1)
    | X0 = X1
    | r2_xboole_0(X0,X1) )).

cnf(u15,axiom,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) )).

cnf(u31,negated_conjecture,
    ( r2_xboole_0(sK1,sK0) )).

cnf(u18,negated_conjecture,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1 )).

cnf(u12,axiom,
    ( ~ r2_xboole_0(X0,X1)
    | r1_tarski(X0,X1) )).

cnf(u16,axiom,
    ( ~ r2_xboole_0(X1,X1) )).

cnf(u26,negated_conjecture,
    ( sK0 = sK2 )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:49:27 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.45  % (20399)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.45  % (20391)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.45  % (20386)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.46  % (20391)Refutation not found, incomplete strategy% (20391)------------------------------
% 0.19/0.46  % (20391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (20391)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (20391)Memory used [KB]: 10618
% 0.19/0.46  % (20391)Time elapsed: 0.057 s
% 0.19/0.46  % (20391)------------------------------
% 0.19/0.46  % (20391)------------------------------
% 0.19/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.19/0.46  % (20399)# SZS output start Saturation.
% 0.19/0.46  cnf(u39,negated_conjecture,
% 0.19/0.46      r1_tarski(sK1,sK1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u30,negated_conjecture,
% 0.19/0.46      r1_tarski(sK1,sK0)).
% 0.19/0.46  
% 0.19/0.46  cnf(u28,negated_conjecture,
% 0.19/0.46      r1_tarski(sK0,sK0)).
% 0.19/0.46  
% 0.19/0.46  cnf(u9,negated_conjecture,
% 0.19/0.46      r1_tarski(sK0,sK1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u29,negated_conjecture,
% 0.19/0.46      ~r1_tarski(sK0,X0) | r1_tarski(sK1,X0)).
% 0.19/0.46  
% 0.19/0.46  cnf(u19,negated_conjecture,
% 0.19/0.46      ~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)).
% 0.19/0.46  
% 0.19/0.46  cnf(u14,axiom,
% 0.19/0.46      ~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u15,axiom,
% 0.19/0.46      ~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)).
% 0.19/0.46  
% 0.19/0.46  cnf(u31,negated_conjecture,
% 0.19/0.46      r2_xboole_0(sK1,sK0)).
% 0.19/0.46  
% 0.19/0.46  cnf(u18,negated_conjecture,
% 0.19/0.46      r2_xboole_0(sK0,sK1) | sK0 = sK1).
% 0.19/0.46  
% 0.19/0.46  cnf(u12,axiom,
% 0.19/0.46      ~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u16,axiom,
% 0.19/0.46      ~r2_xboole_0(X1,X1)).
% 0.19/0.46  
% 0.19/0.46  cnf(u26,negated_conjecture,
% 0.19/0.46      sK0 = sK2).
% 0.19/0.46  
% 0.19/0.46  % (20399)# SZS output end Saturation.
% 0.19/0.46  % (20399)------------------------------
% 0.19/0.46  % (20399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (20399)Termination reason: Satisfiable
% 0.19/0.46  
% 0.19/0.46  % (20399)Memory used [KB]: 1535
% 0.19/0.46  % (20399)Time elapsed: 0.056 s
% 0.19/0.46  % (20399)------------------------------
% 0.19/0.46  % (20399)------------------------------
% 0.19/0.46  % (20381)Success in time 0.111 s
%------------------------------------------------------------------------------
