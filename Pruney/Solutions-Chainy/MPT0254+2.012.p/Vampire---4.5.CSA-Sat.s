%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:14 EST 2020

% Result     : CounterSatisfiable 0.22s
% Output     : Saturation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   22 (  22 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u122,axiom,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 )).

tff(u121,axiom,(
    ! [X0] : k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

tff(u120,axiom,(
    ! [X1,X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) )).

tff(u119,negated_conjecture,(
    k1_xboole_0 = sK1 )).

tff(u118,negated_conjecture,(
    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

tff(u117,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u116,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) )).

tff(u115,axiom,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) )).

tff(u114,negated_conjecture,
    ( ~ ~ r1_tarski(k3_tarski(k1_xboole_0),sK0)
    | ~ r1_tarski(k3_tarski(k1_xboole_0),sK0) )).

tff(u113,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0 ) )).

tff(u112,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1 ) )).

tff(u111,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u110,axiom,(
    ! [X1] : r1_tarski(X1,X1) )).

tff(u109,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )).

tff(u108,axiom,(
    ! [X1,X2] : r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) )).

tff(u107,negated_conjecture,(
    r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:29:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (19003)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % SZS status CounterSatisfiable for theBenchmark
% 0.22/0.50  % (19003)# SZS output start Saturation.
% 0.22/0.50  tff(u122,axiom,
% 0.22/0.50      (![X0] : ((k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0)))).
% 0.22/0.50  
% 0.22/0.50  tff(u121,axiom,
% 0.22/0.50      (![X0] : ((k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0)))).
% 0.22/0.50  
% 0.22/0.50  tff(u120,axiom,
% 0.22/0.50      (![X1, X0] : ((k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u119,negated_conjecture,
% 0.22/0.50      (k1_xboole_0 = sK1)).
% 0.22/0.50  
% 0.22/0.50  tff(u118,negated_conjecture,
% 0.22/0.50      (k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u117,axiom,
% 0.22/0.50      v1_xboole_0(k1_xboole_0)).
% 0.22/0.50  
% 0.22/0.50  tff(u116,axiom,
% 0.22/0.50      (![X1, X0] : ((~r1_tarski(X1,X0) | (X0 = X1) | ~r1_tarski(X0,X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u115,axiom,
% 0.22/0.50      (![X0] : ((~r1_tarski(X0,k1_xboole_0) | (k1_xboole_0 = X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u114,negated_conjecture,
% 0.22/0.50      ((~~r1_tarski(k3_tarski(k1_xboole_0),sK0)) | ~r1_tarski(k3_tarski(k1_xboole_0),sK0))).
% 0.22/0.50  
% 0.22/0.50  tff(u113,axiom,
% 0.22/0.50      (![X1, X0] : ((~r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X0) | (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X0))))).
% 0.22/0.50  
% 0.22/0.50  tff(u112,axiom,
% 0.22/0.50      (![X1, X0] : ((~r1_tarski(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X1) | (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1))))).
% 0.22/0.50  
% 0.22/0.50  tff(u111,axiom,
% 0.22/0.50      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.22/0.50  
% 0.22/0.50  tff(u110,axiom,
% 0.22/0.50      (![X1] : (r1_tarski(X1,X1)))).
% 0.22/0.50  
% 0.22/0.50  tff(u109,axiom,
% 0.22/0.50      (![X1, X0] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u108,axiom,
% 0.22/0.50      (![X1, X2] : (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))))).
% 0.22/0.50  
% 0.22/0.50  tff(u107,negated_conjecture,
% 0.22/0.50      r1_tarski(sK0,k3_tarski(k1_xboole_0))).
% 0.22/0.50  
% 0.22/0.50  % (19003)# SZS output end Saturation.
% 0.22/0.50  % (19003)------------------------------
% 0.22/0.50  % (19003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (19003)Termination reason: Satisfiable
% 0.22/0.50  
% 0.22/0.50  % (19003)Memory used [KB]: 10746
% 0.22/0.50  % (19003)Time elapsed: 0.089 s
% 0.22/0.50  % (19003)------------------------------
% 0.22/0.50  % (19003)------------------------------
% 0.22/0.50  % (18996)Success in time 0.142 s
%------------------------------------------------------------------------------
