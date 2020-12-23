%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:18 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  19 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    0
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u170,axiom,(
    ! [X0] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

tff(u169,axiom,(
    ! [X1] : k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1 )).

tff(u168,axiom,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 )).

tff(u167,axiom,(
    ! [X1,X0] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) )).

tff(u166,axiom,(
    ! [X1,X0] : k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )).

tff(u165,axiom,(
    ! [X3,X2] : k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k3_tarski(k2_enumset1(X2,X2,X2,k3_tarski(k2_enumset1(X2,X2,X2,X3)))) )).

tff(u164,negated_conjecture,(
    k1_xboole_0 = sK1 )).

tff(u163,negated_conjecture,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) )).

tff(u162,negated_conjecture,(
    sK0 = k3_tarski(k1_xboole_0) )).

tff(u161,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u160,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) )).

tff(u159,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u158,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u157,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X2)
      | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X2 ) )).

tff(u156,axiom,(
    ! [X3,X2] :
      ( ~ r1_tarski(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X3)
      | k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X3 ) )).

tff(u155,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u154,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u153,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) )).

tff(u152,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:18:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (13428)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (13434)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (13421)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (13444)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (13434)Refutation not found, incomplete strategy% (13434)------------------------------
% 0.20/0.54  % (13434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13434)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13434)Memory used [KB]: 1663
% 0.20/0.54  % (13434)Time elapsed: 0.047 s
% 0.20/0.54  % (13434)------------------------------
% 0.20/0.54  % (13434)------------------------------
% 0.20/0.54  % (13426)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (13444)Refutation not found, incomplete strategy% (13444)------------------------------
% 0.20/0.54  % (13444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (13444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (13444)Memory used [KB]: 10746
% 0.20/0.54  % (13444)Time elapsed: 0.127 s
% 0.20/0.54  % (13444)------------------------------
% 0.20/0.54  % (13444)------------------------------
% 0.20/0.55  % (13436)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.55  % (13426)# SZS output start Saturation.
% 0.20/0.55  tff(u170,axiom,
% 0.20/0.55      (![X0] : ((k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u169,axiom,
% 0.20/0.55      (![X1] : ((k3_tarski(k2_enumset1(X1,X1,X1,X1)) = X1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u168,axiom,
% 0.20/0.55      (![X0] : ((k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u167,axiom,
% 0.20/0.55      (![X1, X0] : ((k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u166,axiom,
% 0.20/0.55      (![X1, X0] : ((k3_tarski(k2_enumset1(X1,X1,X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u165,axiom,
% 0.20/0.55      (![X3, X2] : ((k3_tarski(k2_enumset1(X2,X2,X2,X3)) = k3_tarski(k2_enumset1(X2,X2,X2,k3_tarski(k2_enumset1(X2,X2,X2,X3)))))))).
% 0.20/0.55  
% 0.20/0.55  tff(u164,negated_conjecture,
% 0.20/0.55      (k1_xboole_0 = sK1)).
% 0.20/0.55  
% 0.20/0.55  tff(u163,negated_conjecture,
% 0.20/0.55      (k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0))).
% 0.20/0.55  
% 0.20/0.55  tff(u162,negated_conjecture,
% 0.20/0.55      (sK0 = k3_tarski(k1_xboole_0))).
% 0.20/0.55  
% 0.20/0.55  tff(u161,axiom,
% 0.20/0.55      v1_xboole_0(k1_xboole_0)).
% 0.20/0.55  
% 0.20/0.55  tff(u160,axiom,
% 0.20/0.55      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u159,axiom,
% 0.20/0.55      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.20/0.55  
% 0.20/0.55  tff(u158,axiom,
% 0.20/0.55      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.20/0.55  
% 0.20/0.55  tff(u157,axiom,
% 0.20/0.55      (![X3, X2] : ((~r1_tarski(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X2) | (k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X2))))).
% 0.20/0.55  
% 0.20/0.55  tff(u156,axiom,
% 0.20/0.55      (![X3, X2] : ((~r1_tarski(k3_tarski(k2_enumset1(X2,X2,X2,X3)),X3) | (k3_tarski(k2_enumset1(X2,X2,X2,X3)) = X3))))).
% 0.20/0.55  
% 0.20/0.55  tff(u155,axiom,
% 0.20/0.55      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.20/0.55  
% 0.20/0.55  tff(u154,axiom,
% 0.20/0.55      (![X1] : (r1_tarski(X1,X1)))).
% 0.20/0.55  
% 0.20/0.55  tff(u153,axiom,
% 0.20/0.55      (![X1, X0] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))))).
% 0.20/0.55  
% 0.20/0.55  tff(u152,axiom,
% 0.20/0.55      (![X1, X0] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))))).
% 0.20/0.55  
% 0.20/0.55  % (13426)# SZS output end Saturation.
% 0.20/0.55  % (13426)------------------------------
% 0.20/0.55  % (13426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13426)Termination reason: Satisfiable
% 0.20/0.55  
% 0.20/0.55  % (13426)Memory used [KB]: 10746
% 0.20/0.55  % (13426)Time elapsed: 0.052 s
% 0.20/0.55  % (13426)------------------------------
% 0.20/0.55  % (13426)------------------------------
% 0.20/0.55  % (13436)Refutation not found, incomplete strategy% (13436)------------------------------
% 0.20/0.55  % (13436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13436)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13436)Memory used [KB]: 10618
% 0.20/0.55  % (13436)Time elapsed: 0.138 s
% 0.20/0.55  % (13436)------------------------------
% 0.20/0.55  % (13436)------------------------------
% 0.20/0.55  % (13419)Success in time 0.188 s
%------------------------------------------------------------------------------
