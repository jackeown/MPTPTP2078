%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:10 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :   13 (  13 expanded)
%              Depth                    :    0
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
cnf(u50,axiom,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )).

cnf(u21,negated_conjecture,
    ( r2_hidden(sK0,sK2) )).

cnf(u54,axiom,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) )).

cnf(u46,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0),sK2) )).

cnf(u42,axiom,
    ( ~ r2_hidden(X1,X2)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | ~ r2_hidden(X0,X2) )).

cnf(u40,negated_conjecture,
    ( r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) )).

cnf(u26,axiom,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X2,X1)
    | ~ r1_tarski(X2,X0)
    | v1_xboole_0(X2) )).

cnf(u41,axiom,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )).

cnf(u47,negated_conjecture,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2) )).

cnf(u43,axiom,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | r2_hidden(X1,X2) )).

cnf(u44,axiom,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
    | r2_hidden(X0,X2) )).

cnf(u45,negated_conjecture,
    ( ~ r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ r1_tarski(X0,sK2)
    | v1_xboole_0(X0) )).

cnf(u53,negated_conjecture,
    ( v1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.45  % (14572)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (14568)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (14568)Refutation not found, incomplete strategy% (14568)------------------------------
% 0.20/0.46  % (14568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (14568)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (14568)Memory used [KB]: 6012
% 0.20/0.46  % (14568)Time elapsed: 0.042 s
% 0.20/0.46  % (14568)------------------------------
% 0.20/0.46  % (14568)------------------------------
% 0.20/0.47  % (14570)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (14564)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (14577)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.48  % (14577)# SZS output start Saturation.
% 0.20/0.48  cnf(u50,axiom,
% 0.20/0.48      r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u21,negated_conjecture,
% 0.20/0.48      r2_hidden(sK0,sK2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u54,axiom,
% 0.20/0.48      ~r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))).
% 0.20/0.48  
% 0.20/0.48  cnf(u46,negated_conjecture,
% 0.20/0.48      ~r2_hidden(X0,sK2) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK0),sK2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u42,axiom,
% 0.20/0.48      ~r2_hidden(X1,X2) | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u40,negated_conjecture,
% 0.20/0.48      r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u26,axiom,
% 0.20/0.48      ~r1_xboole_0(X0,X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u41,axiom,
% 0.20/0.48      r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))).
% 0.20/0.48  
% 0.20/0.48  cnf(u47,negated_conjecture,
% 0.20/0.48      r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u43,axiom,
% 0.20/0.48      ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X1,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u44,axiom,
% 0.20/0.48      ~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)).
% 0.20/0.48  
% 0.20/0.48  cnf(u45,negated_conjecture,
% 0.20/0.48      ~r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~r1_tarski(X0,sK2) | v1_xboole_0(X0)).
% 0.20/0.48  
% 0.20/0.48  cnf(u53,negated_conjecture,
% 0.20/0.48      v1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))).
% 0.20/0.48  
% 0.20/0.48  % (14577)# SZS output end Saturation.
% 0.20/0.48  % (14577)------------------------------
% 0.20/0.48  % (14577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (14577)Termination reason: Satisfiable
% 0.20/0.48  
% 0.20/0.48  % (14577)Memory used [KB]: 1535
% 0.20/0.48  % (14577)Time elapsed: 0.052 s
% 0.20/0.48  % (14577)------------------------------
% 0.20/0.48  % (14577)------------------------------
% 0.20/0.48  % (14578)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (14559)Success in time 0.118 s
%------------------------------------------------------------------------------
