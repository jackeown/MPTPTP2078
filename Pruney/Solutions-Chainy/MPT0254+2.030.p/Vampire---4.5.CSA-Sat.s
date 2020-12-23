%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:17 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   18 (  18 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u96,axiom,
    ( ~ ! [X1,X0] :
          ( k1_xboole_0 != k3_tarski(k2_enumset1(X1,X1,X1,X0))
          | k1_xboole_0 = X0 )
    | ! [X1,X0] :
        ( k1_xboole_0 != k3_tarski(k2_enumset1(X1,X1,X1,X0))
        | k1_xboole_0 = X0 ) )).

tff(u95,axiom,
    ( ~ ! [X1,X0] :
          ( k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))
          | k1_xboole_0 = X0 )
    | ! [X1,X0] :
        ( k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))
        | k1_xboole_0 = X0 ) )).

tff(u94,negated_conjecture,
    ( ~ ( k1_xboole_0 != k3_tarski(k1_xboole_0) )
    | k1_xboole_0 != k3_tarski(k1_xboole_0) )).

tff(u93,axiom,
    ( ~ ! [X1,X0] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)
    | ! [X1,X0] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) )).

tff(u92,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK1 )).

tff(u91,negated_conjecture,
    ( k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) )).

% (6228)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
tff(u90,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 14:50:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (6225)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (6237)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (6237)Refutation not found, incomplete strategy% (6237)------------------------------
% 0.22/0.49  % (6237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (6237)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (6237)Memory used [KB]: 10618
% 0.22/0.49  % (6237)Time elapsed: 0.067 s
% 0.22/0.49  % (6237)------------------------------
% 0.22/0.49  % (6237)------------------------------
% 0.22/0.52  % (6231)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6230)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.52  % (6234)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (6232)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (6235)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.52  % (6232)# SZS output start Saturation.
% 0.22/0.52  tff(u96,axiom,
% 0.22/0.52      ((~(![X1, X0] : (((k1_xboole_0 != k3_tarski(k2_enumset1(X1,X1,X1,X0))) | (k1_xboole_0 = X0))))) | (![X1, X0] : (((k1_xboole_0 != k3_tarski(k2_enumset1(X1,X1,X1,X0))) | (k1_xboole_0 = X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u95,axiom,
% 0.22/0.52      ((~(![X1, X0] : (((k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))) | (k1_xboole_0 = X0))))) | (![X1, X0] : (((k1_xboole_0 != k3_tarski(k2_enumset1(X0,X0,X0,X1))) | (k1_xboole_0 = X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u94,negated_conjecture,
% 0.22/0.52      ((~(k1_xboole_0 != k3_tarski(k1_xboole_0))) | (k1_xboole_0 != k3_tarski(k1_xboole_0)))).
% 0.22/0.52  
% 0.22/0.52  tff(u93,axiom,
% 0.22/0.52      ((~(![X1, X0] : ((k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0))))) | (![X1, X0] : ((k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)))))).
% 0.22/0.52  
% 0.22/0.52  tff(u92,negated_conjecture,
% 0.22/0.52      ((~(k1_xboole_0 = sK1)) | (k1_xboole_0 = sK1))).
% 0.22/0.52  
% 0.22/0.52  tff(u91,negated_conjecture,
% 0.22/0.52      ((~(k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0))) | (k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)))).
% 0.22/0.52  
% 0.22/0.52  % (6228)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.52  tff(u90,negated_conjecture,
% 0.22/0.52      ((~(k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) | (k1_xboole_0 = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))).
% 0.22/0.52  
% 0.22/0.52  % (6232)# SZS output end Saturation.
% 0.22/0.52  % (6232)------------------------------
% 0.22/0.52  % (6232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6232)Termination reason: Satisfiable
% 0.22/0.52  
% 0.22/0.52  % (6232)Memory used [KB]: 6140
% 0.22/0.52  % (6232)Time elapsed: 0.072 s
% 0.22/0.52  % (6232)------------------------------
% 0.22/0.52  % (6232)------------------------------
% 0.22/0.53  % (6218)Success in time 0.166 s
%------------------------------------------------------------------------------
