%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:31 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :    6 (   6 expanded)
%              Number of leaves         :    6 (   6 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u87,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | k1_xboole_0 = X0 ) )).

tff(u86,axiom,(
    ! [X1,X0] :
      ( k1_xboole_0 != k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0))
      | k1_xboole_0 = X0 ) )).

tff(u85,negated_conjecture,
    ( ~ ( k1_xboole_0 != k3_tarski(k1_xboole_0) )
    | k1_xboole_0 != k3_tarski(k1_xboole_0) )).

tff(u84,axiom,(
    ! [X1,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) )).

tff(u83,negated_conjecture,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

tff(u82,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))
    | k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (8915)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.43  % (8905)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.45  % (8911)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.46  % (8915)# SZS output start Saturation.
% 0.21/0.46  tff(u87,axiom,
% 0.21/0.46      (![X1, X0] : (((k1_xboole_0 != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | (k1_xboole_0 = X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u86,axiom,
% 0.21/0.46      (![X1, X0] : (((k1_xboole_0 != k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0))) | (k1_xboole_0 = X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u85,negated_conjecture,
% 0.21/0.46      ((~(k1_xboole_0 != k3_tarski(k1_xboole_0))) | (k1_xboole_0 != k3_tarski(k1_xboole_0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u84,axiom,
% 0.21/0.46      (![X1, X0, X2] : ((k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0))))).
% 0.21/0.46  
% 0.21/0.46  tff(u83,negated_conjecture,
% 0.21/0.46      ((~(k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))).
% 0.21/0.46  
% 0.21/0.46  tff(u82,negated_conjecture,
% 0.21/0.46      ((~(k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)))) | (k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))))).
% 0.21/0.46  
% 0.21/0.46  % (8915)# SZS output end Saturation.
% 0.21/0.46  % (8915)------------------------------
% 0.21/0.46  % (8915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (8915)Termination reason: Satisfiable
% 0.21/0.46  
% 0.21/0.46  % (8915)Memory used [KB]: 6140
% 0.21/0.46  % (8915)Time elapsed: 0.059 s
% 0.21/0.46  % (8915)------------------------------
% 0.21/0.46  % (8915)------------------------------
% 0.21/0.47  % (8904)Success in time 0.112 s
%------------------------------------------------------------------------------
