%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:39 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    0
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u101,negated_conjecture,(
    sK0 != k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)) )).

tff(u100,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u99,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u98,axiom,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 )).

tff(u97,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u96,axiom,(
    ! [X5] : r1_tarski(X5,X5) )).

tff(u95,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) )).

tff(u94,axiom,(
    ! [X9,X8] : r1_tarski(X8,k2_xboole_0(X9,X8)) )).

tff(u93,axiom,(
    ! [X1,X2] : r1_tarski(X2,k2_xboole_0(X2,X1)) )).

% (19250)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
tff(u92,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) )).

tff(u91,axiom,(
    ! [X1,X0,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) )).

tff(u90,axiom,(
    ! [X3,X2,X4] :
      ( r1_tarski(k2_xboole_0(X3,X2),k2_xboole_0(X4,X3))
      | ~ r1_tarski(X2,X4) ) )).

tff(u89,axiom,(
    ! [X3,X2,X4] :
      ( r1_tarski(k2_xboole_0(X4,X3),k2_xboole_0(X3,X2))
      | ~ r1_tarski(X4,X2) ) )).

tff(u88,axiom,(
    ! [X3,X2,X4] :
      ( r1_tarski(k2_xboole_0(X3,X4),k2_xboole_0(X3,X2))
      | ~ r1_tarski(X4,X2) ) )).

tff(u87,axiom,(
    ! [X9,X8] :
      ( r1_tarski(k2_xboole_0(X9,X8),X8)
      | ~ r1_tarski(X9,k1_xboole_0) ) )).

tff(u86,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k2_xboole_0(X2,X1),X2)
      | ~ r1_tarski(X1,k1_xboole_0) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:03:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (19246)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (19240)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.43  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.43  % (19240)# SZS output start Saturation.
% 0.21/0.43  tff(u101,negated_conjecture,
% 0.21/0.43      (sK0 != k3_xboole_0(sK0,k2_xboole_0(sK0,sK1)))).
% 0.21/0.43  
% 0.21/0.43  tff(u100,axiom,
% 0.21/0.43      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.21/0.43  
% 0.21/0.43  tff(u99,axiom,
% 0.21/0.43      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u98,axiom,
% 0.21/0.43      (![X0] : ((k2_xboole_0(k1_xboole_0,X0) = X0)))).
% 0.21/0.43  
% 0.21/0.43  tff(u97,axiom,
% 0.21/0.43      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.21/0.43  
% 0.21/0.43  tff(u96,axiom,
% 0.21/0.43      (![X5] : (r1_tarski(X5,X5)))).
% 0.21/0.43  
% 0.21/0.43  tff(u95,axiom,
% 0.21/0.43      (![X1, X0, X2] : ((r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))))).
% 0.21/0.43  
% 0.21/0.43  tff(u94,axiom,
% 0.21/0.43      (![X9, X8] : (r1_tarski(X8,k2_xboole_0(X9,X8))))).
% 0.21/0.43  
% 0.21/0.43  tff(u93,axiom,
% 0.21/0.43      (![X1, X2] : (r1_tarski(X2,k2_xboole_0(X2,X1))))).
% 0.21/0.43  
% 0.21/0.43  % (19250)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.43  tff(u92,axiom,
% 0.21/0.43      (![X1, X0, X2] : ((r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))))).
% 0.21/0.43  
% 0.21/0.43  tff(u91,axiom,
% 0.21/0.43      (![X1, X0, X2] : ((r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))))).
% 0.21/0.43  
% 0.21/0.43  tff(u90,axiom,
% 0.21/0.43      (![X3, X2, X4] : ((r1_tarski(k2_xboole_0(X3,X2),k2_xboole_0(X4,X3)) | ~r1_tarski(X2,X4))))).
% 0.21/0.43  
% 0.21/0.43  tff(u89,axiom,
% 0.21/0.43      (![X3, X2, X4] : ((r1_tarski(k2_xboole_0(X4,X3),k2_xboole_0(X3,X2)) | ~r1_tarski(X4,X2))))).
% 0.21/0.43  
% 0.21/0.43  tff(u88,axiom,
% 0.21/0.43      (![X3, X2, X4] : ((r1_tarski(k2_xboole_0(X3,X4),k2_xboole_0(X3,X2)) | ~r1_tarski(X4,X2))))).
% 0.21/0.43  
% 0.21/0.43  tff(u87,axiom,
% 0.21/0.43      (![X9, X8] : ((r1_tarski(k2_xboole_0(X9,X8),X8) | ~r1_tarski(X9,k1_xboole_0))))).
% 0.21/0.43  
% 0.21/0.43  tff(u86,axiom,
% 0.21/0.43      (![X1, X2] : ((r1_tarski(k2_xboole_0(X2,X1),X2) | ~r1_tarski(X1,k1_xboole_0))))).
% 0.21/0.43  
% 0.21/0.43  % (19240)# SZS output end Saturation.
% 0.21/0.43  % (19240)------------------------------
% 0.21/0.43  % (19240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (19240)Termination reason: Satisfiable
% 0.21/0.43  
% 0.21/0.43  % (19240)Memory used [KB]: 10618
% 0.21/0.43  % (19240)Time elapsed: 0.005 s
% 0.21/0.43  % (19240)------------------------------
% 0.21/0.43  % (19240)------------------------------
% 0.21/0.43  % (19245)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (19239)Success in time 0.071 s
%------------------------------------------------------------------------------
