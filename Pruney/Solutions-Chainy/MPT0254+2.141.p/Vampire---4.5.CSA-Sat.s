%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:31 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   11 (  11 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    0
%              Number of atoms          :   19 (  19 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u127,axiom,(
    ! [X1,X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) )).

tff(u126,negated_conjecture,
    ( k1_xboole_0 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

tff(u125,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))
    | k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)) )).

tff(u124,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))) )).

tff(u123,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) != k3_tarski(k1_xboole_0)
    | k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) = k3_tarski(k1_xboole_0) )).

tff(u122,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u121,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u120,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )).

tff(u119,axiom,(
    ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )).

tff(u118,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) )).

tff(u117,negated_conjecture,
    ( ~ r1_tarski(sK0,k3_tarski(k1_xboole_0))
    | r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:06:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (2580)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (2583)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (2583)# SZS output start Saturation.
% 0.20/0.47  tff(u127,axiom,
% 0.20/0.47      (![X1, X0] : ((k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u126,negated_conjecture,
% 0.20/0.47      ((~(k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (k1_xboole_0 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u125,negated_conjecture,
% 0.20/0.47      ((~(k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1)))) | (k1_xboole_0 = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u124,negated_conjecture,
% 0.20/0.47      ((~(k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0))))) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_xboole_0)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u123,negated_conjecture,
% 0.20/0.47      ((~(k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) = k3_tarski(k1_xboole_0))) | (k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))) = k3_tarski(k1_xboole_0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u122,axiom,
% 0.20/0.47      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.20/0.47  
% 0.20/0.47  tff(u121,axiom,
% 0.20/0.47      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u120,axiom,
% 0.20/0.47      (![X1, X0] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u119,axiom,
% 0.20/0.47      (![X1, X0] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u118,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(k1_xboole_0,k1_xboole_0)) | r1_tarski(k1_xboole_0,k1_xboole_0))).
% 0.20/0.47  
% 0.20/0.47  tff(u117,negated_conjecture,
% 0.20/0.47      ((~r1_tarski(sK0,k3_tarski(k1_xboole_0))) | r1_tarski(sK0,k3_tarski(k1_xboole_0)))).
% 0.20/0.47  
% 0.20/0.47  % (2583)# SZS output end Saturation.
% 0.20/0.47  % (2583)------------------------------
% 0.20/0.47  % (2583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (2583)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (2583)Memory used [KB]: 6140
% 0.20/0.47  % (2583)Time elapsed: 0.005 s
% 0.20/0.47  % (2583)------------------------------
% 0.20/0.47  % (2583)------------------------------
% 0.20/0.47  % (2581)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (2576)Success in time 0.108 s
%------------------------------------------------------------------------------
