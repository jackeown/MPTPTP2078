%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:17 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  52 expanded)
%              Number of leaves         :   52 (  52 expanded)
%              Depth                    :    0
%              Number of atoms          :   89 (  89 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u517,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK1 )).

tff(u516,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u515,axiom,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) )).

tff(u514,negated_conjecture,
    ( k1_xboole_0 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

tff(u513,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0 )).

tff(u512,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = X0 )).

tff(u511,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u510,axiom,(
    ! [X1,X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) )).

tff(u509,axiom,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 )).

tff(u508,axiom,(
    ! [X0] : k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

tff(u507,negated_conjecture,
    ( sK0 != k3_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

tff(u506,axiom,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) )).

tff(u505,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) )).

tff(u504,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X0))) ) )).

tff(u503,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,X0) ) )).

tff(u502,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))) ) )).

tff(u501,axiom,(
    ! [X3,X2,X4] :
      ( ~ r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))
      | ~ r2_hidden(X4,X2) ) )).

tff(u500,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3)))
      | r1_xboole_0(X3,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X3))) ) )).

tff(u499,axiom,(
    ! [X3,X2] :
      ( ~ r1_xboole_0(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2)))
      | r1_xboole_0(X2,X2) ) )).

tff(u498,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3)))
      | r1_xboole_0(X3,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X5))) ) )).

tff(u497,axiom,(
    ! [X3,X5,X4] :
      ( ~ r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3)))
      | ~ r2_hidden(X5,X3) ) )).

tff(u496,axiom,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) )).

tff(u495,negated_conjecture,
    ( ~ ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

tff(u494,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | ! [X0] : ~ r1_xboole_0(sK0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK0))) )).

tff(u493,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | ! [X0] : ~ r1_xboole_0(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))) )).

tff(u492,negated_conjecture,
    ( ~ ~ r1_xboole_0(sK0,sK0)
    | ~ r1_xboole_0(sK0,sK0) )).

tff(u491,axiom,(
    ! [X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2))
      | r1_xboole_0(X1,X2) ) )).

tff(u490,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) )).

tff(u489,axiom,(
    ! [X3,X4] :
      ( r1_xboole_0(X3,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4)))
      | ~ r1_xboole_0(X3,X3) ) )).

tff(u488,axiom,(
    ! [X5,X4] :
      ( r1_xboole_0(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X4)))
      | ~ r1_xboole_0(X4,X4) ) )).

tff(u487,axiom,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) )).

tff(u486,axiom,(
    ! [X1,X0,X2] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X2)))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u485,axiom,(
    ! [X1,X0,X2] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k3_xboole_0(X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u484,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u483,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u482,axiom,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) )).

tff(u481,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X1,X1) ) )).

tff(u480,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) )).

tff(u479,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u478,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0)
      | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ) )).

tff(u477,axiom,(
    ! [X1,X2] :
      ( r2_hidden(sK3(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))),X1)
      | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ) )).

tff(u476,axiom,(
    ! [X0] :
      ( r2_hidden(sK3(X0,X0),X0)
      | r1_xboole_0(X0,X0) ) )).

tff(u475,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0) )).

tff(u474,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | ! [X0] : r2_hidden(sK3(sK0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK0))),sK0) )).

tff(u473,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | ! [X0] : r2_hidden(sK3(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))),sK0) )).

tff(u472,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,sK0),sK0)
    | r2_hidden(sK3(sK0,sK0),sK0) )).

tff(u471,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u470,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )).

tff(u469,axiom,(
    ! [X1,X2] : r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) )).

tff(u468,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u467,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) )).

tff(u466,negated_conjecture,
    ( ~ r1_tarski(sK0,k3_tarski(k1_xboole_0))
    | r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (13659)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (13655)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (13659)Refutation not found, incomplete strategy% (13659)------------------------------
% 0.21/0.47  % (13659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13659)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (13659)Memory used [KB]: 7291
% 0.21/0.47  % (13659)Time elapsed: 0.038 s
% 0.21/0.47  % (13659)------------------------------
% 0.21/0.47  % (13659)------------------------------
% 0.21/0.47  % (13670)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (13657)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (13660)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (13657)Refutation not found, incomplete strategy% (13657)------------------------------
% 0.21/0.48  % (13657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (13657)Memory used [KB]: 1663
% 0.21/0.48  % (13657)Time elapsed: 0.056 s
% 0.21/0.48  % (13657)------------------------------
% 0.21/0.48  % (13657)------------------------------
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (13670)# SZS output start Saturation.
% 0.21/0.48  tff(u517,negated_conjecture,
% 0.21/0.48      ((~(k1_xboole_0 = sK1)) | (k1_xboole_0 = sK1))).
% 0.21/0.48  
% 0.21/0.48  tff(u516,axiom,
% 0.21/0.48      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u515,axiom,
% 0.21/0.48      (![X1] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u514,negated_conjecture,
% 0.21/0.48      ((~(k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u513,axiom,
% 0.21/0.48      (![X1, X0] : ((k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u512,axiom,
% 0.21/0.48      (![X1, X0] : ((k3_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u511,axiom,
% 0.21/0.48      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u510,axiom,
% 0.21/0.48      (![X1, X0] : ((k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u509,axiom,
% 0.21/0.48      (![X0] : ((k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u508,axiom,
% 0.21/0.48      (![X0] : ((k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u507,negated_conjecture,
% 0.21/0.48      ((~(sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)))) | (sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u506,axiom,
% 0.21/0.48      ((~v1_xboole_0(k1_xboole_0)) | v1_xboole_0(k1_xboole_0))).
% 0.21/0.48  
% 0.21/0.48  tff(u505,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k1_xboole_0 = k3_xboole_0(X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u504,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u503,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u502,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u501,axiom,
% 0.21/0.48      (![X3, X2, X4] : ((~r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))) | ~r2_hidden(X4,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u500,axiom,
% 0.21/0.48      (![X3, X5, X4] : ((~r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))) | r1_xboole_0(X3,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u499,axiom,
% 0.21/0.48      (![X3, X2] : ((~r1_xboole_0(X2,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X2))) | r1_xboole_0(X2,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u498,axiom,
% 0.21/0.48      (![X3, X5, X4] : ((~r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))) | r1_xboole_0(X3,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X5))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u497,axiom,
% 0.21/0.48      (![X3, X5, X4] : ((~r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))) | ~r2_hidden(X5,X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u496,axiom,
% 0.21/0.48      (![X0] : ((~r1_xboole_0(X0,X0) | (k1_xboole_0 = X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u495,negated_conjecture,
% 0.21/0.48      ((~~r1_xboole_0(sK0,k3_tarski(k1_xboole_0))) | ~r1_xboole_0(sK0,k3_tarski(k1_xboole_0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u494,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | (![X0] : (~r1_xboole_0(sK0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u493,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | (![X0] : (~r1_xboole_0(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u492,negated_conjecture,
% 0.21/0.48      ((~~r1_xboole_0(sK0,sK0)) | ~r1_xboole_0(sK0,sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u491,axiom,
% 0.21/0.48      (![X1, X2] : ((~r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) | r1_xboole_0(X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u490,axiom,
% 0.21/0.48      (![X0] : (r1_xboole_0(X0,k1_xboole_0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u489,axiom,
% 0.21/0.48      (![X3, X4] : ((r1_xboole_0(X3,k3_tarski(k5_enumset1(X3,X3,X3,X3,X3,X3,X4))) | ~r1_xboole_0(X3,X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u488,axiom,
% 0.21/0.48      (![X5, X4] : ((r1_xboole_0(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X4))) | ~r1_xboole_0(X4,X4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u487,axiom,
% 0.21/0.48      (![X0] : (r1_xboole_0(k1_xboole_0,X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u486,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),X2))) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u485,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((r1_xboole_0(k3_xboole_0(X0,X1),k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,k3_xboole_0(X0,X1)))) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u484,axiom,
% 0.21/0.48      (![X1, X0] : ((r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u483,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u482,axiom,
% 0.21/0.48      (![X0] : (~r2_hidden(X0,k1_xboole_0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u481,axiom,
% 0.21/0.48      (![X1, X2] : ((~r2_hidden(X2,X1) | ~r1_xboole_0(X1,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u480,axiom,
% 0.21/0.48      (![X0] : ((r2_hidden(sK2(X0),X0) | (k1_xboole_0 = X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u479,axiom,
% 0.21/0.48      (![X1, X0] : ((r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u478,axiom,
% 0.21/0.48      (![X1, X0] : ((r2_hidden(sK3(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),X0) | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u477,axiom,
% 0.21/0.48      (![X1, X2] : ((r2_hidden(sK3(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))),X1) | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u476,axiom,
% 0.21/0.48      (![X0] : ((r2_hidden(sK3(X0,X0),X0) | r1_xboole_0(X0,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u475,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u474,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | (![X0] : (r2_hidden(sK3(sK0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK0))),sK0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u473,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | (![X0] : (r2_hidden(sK3(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))),sK0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u472,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,sK0),sK0)) | r2_hidden(sK3(sK0,sK0),sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u471,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u470,axiom,
% 0.21/0.48      (![X1, X0] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u469,axiom,
% 0.21/0.48      (![X1, X2] : (r1_tarski(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u468,axiom,
% 0.21/0.48      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u467,axiom,
% 0.21/0.48      (![X0] : (r1_tarski(k1_xboole_0,X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u466,negated_conjecture,
% 0.21/0.48      ((~r1_tarski(sK0,k3_tarski(k1_xboole_0))) | r1_tarski(sK0,k3_tarski(k1_xboole_0)))).
% 0.21/0.48  
% 0.21/0.48  % (13670)# SZS output end Saturation.
% 0.21/0.48  % (13670)------------------------------
% 0.21/0.48  % (13670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (13670)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (13670)Memory used [KB]: 10874
% 0.21/0.48  % (13670)Time elapsed: 0.011 s
% 0.21/0.48  % (13670)------------------------------
% 0.21/0.48  % (13670)------------------------------
% 0.21/0.48  % (13666)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (13651)Success in time 0.119 s
%------------------------------------------------------------------------------
