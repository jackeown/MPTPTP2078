%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:40 EST 2020

% Result     : CounterSatisfiable 0.13s
% Output     : Saturation 0.13s
% Verified   : 
% Statistics : Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    0
%              Number of atoms          :   32 (  32 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal clause size      :    4 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u15,axiom,
    ( r1_tarski(X2,sK2(X0,X1,X2))
    | k2_xboole_0(X0,X2) = X1
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u14,axiom,
    ( r1_tarski(X0,sK2(X0,X1,X2))
    | k2_xboole_0(X0,X2) = X1
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u13,axiom,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) )).

cnf(u19,axiom,
    ( ~ r1_tarski(X3,X3)
    | ~ r1_tarski(X2,X3)
    | k2_xboole_0(X2,X3) = X3 )).

cnf(u20,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X0)
    | k2_xboole_0(X0,X1) = X0 )).

cnf(u19_001,axiom,
    ( ~ r1_tarski(X3,X3)
    | ~ r1_tarski(X2,X3)
    | k2_xboole_0(X2,X3) = X3 )).

cnf(u24,axiom,
    ( ~ r1_tarski(X0,X0)
    | k2_xboole_0(X0,X0) = X0 )).

cnf(u21,axiom,
    ( ~ r1_tarski(X0,X0)
    | k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 )).

cnf(u20_002,axiom,
    ( ~ r1_tarski(X1,X0)
    | ~ r1_tarski(X0,X0)
    | k2_xboole_0(X0,X1) = X0 )).

cnf(u25,axiom,
    ( ~ r1_tarski(X0,X0)
    | k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 )).

cnf(u16,axiom,
    ( ~ r1_tarski(X1,sK2(X0,X1,X2))
    | k2_xboole_0(X0,X2) = X1
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X0,X1) )).

cnf(u12,negated_conjecture,
    ( sK0 != k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:14:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.41  % (31438)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.13/0.41  % (31439)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.13/0.41  % (31435)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.41  % (31440)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.13/0.41  % SZS status CounterSatisfiable for theBenchmark
% 0.13/0.41  % (31435)# SZS output start Saturation.
% 0.13/0.41  cnf(u15,axiom,
% 0.13/0.41      r1_tarski(X2,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)).
% 0.13/0.41  
% 0.13/0.41  cnf(u14,axiom,
% 0.13/0.41      r1_tarski(X0,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)).
% 0.13/0.41  
% 0.13/0.41  cnf(u13,axiom,
% 0.13/0.41      r1_tarski(k3_xboole_0(X0,X1),X0)).
% 0.13/0.41  
% 0.13/0.41  cnf(u19,axiom,
% 0.13/0.41      ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3).
% 0.13/0.41  
% 0.13/0.41  cnf(u20,axiom,
% 0.13/0.41      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k2_xboole_0(X0,X1) = X0).
% 0.13/0.41  
% 0.13/0.41  cnf(u19,axiom,
% 0.13/0.41      ~r1_tarski(X3,X3) | ~r1_tarski(X2,X3) | k2_xboole_0(X2,X3) = X3).
% 0.13/0.41  
% 0.13/0.41  cnf(u24,axiom,
% 0.13/0.41      ~r1_tarski(X0,X0) | k2_xboole_0(X0,X0) = X0).
% 0.13/0.41  
% 0.13/0.41  cnf(u21,axiom,
% 0.13/0.41      ~r1_tarski(X0,X0) | k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0).
% 0.13/0.41  
% 0.13/0.41  cnf(u20,axiom,
% 0.13/0.41      ~r1_tarski(X1,X0) | ~r1_tarski(X0,X0) | k2_xboole_0(X0,X1) = X0).
% 0.13/0.41  
% 0.13/0.41  cnf(u25,axiom,
% 0.13/0.41      ~r1_tarski(X0,X0) | k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0).
% 0.13/0.41  
% 0.13/0.41  cnf(u16,axiom,
% 0.13/0.41      ~r1_tarski(X1,sK2(X0,X1,X2)) | k2_xboole_0(X0,X2) = X1 | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)).
% 0.13/0.41  
% 0.13/0.41  cnf(u12,negated_conjecture,
% 0.13/0.41      sK0 != k2_xboole_0(sK0,k3_xboole_0(sK0,sK1))).
% 0.13/0.41  
% 0.13/0.41  % (31435)# SZS output end Saturation.
% 0.13/0.41  % (31435)------------------------------
% 0.13/0.41  % (31435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (31435)Termination reason: Satisfiable
% 0.13/0.41  
% 0.13/0.41  % (31435)Memory used [KB]: 6012
% 0.13/0.41  % (31435)Time elapsed: 0.002 s
% 0.13/0.41  % (31435)------------------------------
% 0.13/0.41  % (31435)------------------------------
% 0.13/0.41  % (31430)Success in time 0.047 s
%------------------------------------------------------------------------------
