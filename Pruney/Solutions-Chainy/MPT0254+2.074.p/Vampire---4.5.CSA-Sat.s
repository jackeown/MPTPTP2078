%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:22 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :   10 (  10 expanded)
%              Depth                    :    0
%              Number of atoms          :   17 (  17 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u131,axiom,(
    ! [X1,X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) )).

tff(u130,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )).

tff(u129,negated_conjecture,
    ( k1_xboole_0 != k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) )).

tff(u128,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK1 )).

tff(u127,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u126,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u125,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )).

tff(u124,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )).

tff(u123,negated_conjecture,
    ( ~ r1_tarski(sK0,k3_tarski(k1_xboole_0))
    | r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

tff(u122,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_xboole_0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (19326)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (19338)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (19330)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (19324)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.47  % (19338)# SZS output start Saturation.
% 0.21/0.47  tff(u131,axiom,
% 0.21/0.47      (![X1, X0] : ((k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u130,negated_conjecture,
% 0.21/0.47      ((~(k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) | (k1_xboole_0 = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u129,negated_conjecture,
% 0.21/0.47      ((~(k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u128,negated_conjecture,
% 0.21/0.47      ((~(k1_xboole_0 = sK1)) | (k1_xboole_0 = sK1))).
% 0.21/0.47  
% 0.21/0.47  tff(u127,axiom,
% 0.21/0.47      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.21/0.47  
% 0.21/0.47  tff(u126,axiom,
% 0.21/0.47      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.21/0.47  
% 0.21/0.47  tff(u125,axiom,
% 0.21/0.47      (![X1, X0] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u124,axiom,
% 0.21/0.47      (![X1, X0] : (r1_tarski(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)))))).
% 0.21/0.47  
% 0.21/0.47  tff(u123,negated_conjecture,
% 0.21/0.47      ((~r1_tarski(sK0,k3_tarski(k1_xboole_0))) | r1_tarski(sK0,k3_tarski(k1_xboole_0)))).
% 0.21/0.47  
% 0.21/0.47  tff(u122,negated_conjecture,
% 0.21/0.47      ((~r1_tarski(k1_xboole_0,k1_xboole_0)) | r1_tarski(k1_xboole_0,k1_xboole_0))).
% 0.21/0.47  
% 0.21/0.47  % (19338)# SZS output end Saturation.
% 0.21/0.47  % (19338)------------------------------
% 0.21/0.47  % (19338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19338)Termination reason: Satisfiable
% 0.21/0.47  
% 0.21/0.47  % (19338)Memory used [KB]: 10618
% 0.21/0.47  % (19338)Time elapsed: 0.063 s
% 0.21/0.47  % (19338)------------------------------
% 0.21/0.47  % (19338)------------------------------
% 0.21/0.47  % (19322)Success in time 0.115 s
%------------------------------------------------------------------------------
