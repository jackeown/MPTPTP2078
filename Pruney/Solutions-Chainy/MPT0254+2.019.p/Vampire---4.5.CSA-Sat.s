%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:15 EST 2020

% Result     : CounterSatisfiable 0.21s
% Output     : Saturation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  61 expanded)
%              Number of leaves         :   61 (  61 expanded)
%              Depth                    :    0
%              Number of atoms          :  104 ( 104 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u385,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) )).

tff(u384,axiom,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) )).

tff(u383,negated_conjecture,(
    k1_xboole_0 = sK1 )).

tff(u382,negated_conjecture,(
    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) )).

tff(u381,axiom,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 )).

tff(u380,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0 )).

tff(u379,axiom,(
    ! [X5,X4] : k3_xboole_0(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X4))) = X4 )).

tff(u378,axiom,(
    ! [X1,X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) )).

tff(u377,axiom,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 )).

tff(u376,axiom,(
    ! [X0] : k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 )).

tff(u375,negated_conjecture,(
    sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

tff(u374,axiom,(
    ! [X1,X2] :
      ( ~ v1_xboole_0(X1)
      | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ) )).

tff(u373,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ) )).

tff(u372,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | r1_xboole_0(X0,X0) ) )).

tff(u371,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) )).

tff(u370,axiom,(
    ! [X1,X0] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) )).

tff(u369,axiom,(
    ! [X3,X2] :
      ( ~ v1_xboole_0(k3_xboole_0(X2,X3))
      | r1_xboole_0(X2,X3) ) )).

tff(u368,negated_conjecture,
    ( ~ ~ v1_xboole_0(sK0)
    | ~ v1_xboole_0(sK0) )).

tff(u367,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u366,axiom,(
    ! [X1,X3,X2] :
      ( ~ r2_hidden(X3,X1)
      | ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ) )).

tff(u365,axiom,(
    ! [X0,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) )).

tff(u364,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u363,axiom,
    ( ~ ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ! [X1] : ~ r2_hidden(X1,k1_xboole_0) )).

tff(u362,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) )).

tff(u361,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u360,axiom,(
    ! [X1] :
      ( r2_hidden(sK3(X1,X1),X1)
      | r1_xboole_0(X1,X1) ) )).

tff(u359,axiom,(
    ! [X3,X2] :
      ( r2_hidden(sK3(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))),X2)
      | r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))) ) )).

tff(u358,axiom,(
    ! [X3,X4] :
      ( r2_hidden(sK3(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))),X3)
      | r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))) ) )).

tff(u357,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0) )).

tff(u356,axiom,(
    ! [X5,X7,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(k3_xboole_0(X5,X6),k3_tarski(k5_enumset1(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),X7))) ) )).

tff(u355,axiom,(
    ! [X5,X7,X6] :
      ( ~ r1_xboole_0(X5,X6)
      | r1_xboole_0(k3_xboole_0(X5,X6),k3_tarski(k5_enumset1(X7,X7,X7,X7,X7,X7,k3_xboole_0(X5,X6)))) ) )).

tff(u354,axiom,(
    ! [X1,X2] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ) )).

tff(u353,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(k3_xboole_0(X0,X1)) ) )).

tff(u352,axiom,(
    ! [X5,X4] :
      ( ~ r1_xboole_0(X4,X4)
      | r1_xboole_0(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X4))) ) )).

tff(u351,axiom,(
    ! [X3,X2] :
      ( ~ r1_xboole_0(X2,X2)
      | r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))) ) )).

tff(u350,axiom,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,X1)
      | v1_xboole_0(X1) ) )).

tff(u349,axiom,(
    ! [X3,X2] :
      ( ~ r1_xboole_0(X2,X2)
      | ~ r2_hidden(X3,X2) ) )).

tff(u348,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))
      | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))) ) )).

tff(u347,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))
      | r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))) ) )).

tff(u346,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))
      | r1_xboole_0(X1,X1) ) )).

tff(u345,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))
      | v1_xboole_0(X1) ) )).

tff(u344,axiom,(
    ! [X5,X4,X6] :
      ( ~ r1_xboole_0(X4,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X5)))
      | ~ r2_hidden(X6,X4) ) )).

tff(u343,axiom,(
    ! [X9,X7,X8] :
      ( ~ r1_xboole_0(X7,k3_tarski(k5_enumset1(X9,X9,X9,X9,X9,X9,X7)))
      | r1_xboole_0(X7,k3_tarski(k5_enumset1(X8,X8,X8,X8,X8,X8,X7))) ) )).

tff(u342,axiom,(
    ! [X5,X4,X6] :
      ( ~ r1_xboole_0(X4,k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X4)))
      | r1_xboole_0(X4,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X5))) ) )).

tff(u341,axiom,(
    ! [X5,X6] :
      ( ~ r1_xboole_0(X5,k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X5)))
      | r1_xboole_0(X5,X5) ) )).

tff(u340,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0)))
      | v1_xboole_0(X0) ) )).

tff(u339,negated_conjecture,
    ( ~ ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0))
    | ~ r1_xboole_0(sK0,k3_tarski(k1_xboole_0)) )).

tff(u338,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | ! [X0] : ~ r1_xboole_0(sK0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK0))) )).

tff(u337,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | ! [X0] : ~ r1_xboole_0(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))) )).

tff(u336,negated_conjecture,
    ( ~ r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)
    | ~ r1_xboole_0(sK0,sK0) )).

tff(u335,axiom,(
    ! [X3,X2,X4] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X3),k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,k3_xboole_0(X2,X3))))
      | r1_xboole_0(X2,X3) ) )).

tff(u334,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X0)))
      | r1_xboole_0(X1,X2) ) )).

tff(u333,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u332,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) )).

tff(u331,axiom,(
    ! [X8] : r1_xboole_0(k1_xboole_0,X8) )).

tff(u330,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u329,axiom,(
    ! [X1,X0] : r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )).

tff(u328,axiom,(
    ! [X7,X6] : r1_tarski(X6,k3_tarski(k5_enumset1(X7,X7,X7,X7,X7,X7,X6))) )).

tff(u327,axiom,(
    ! [X0] : r1_tarski(X0,X0) )).

tff(u326,axiom,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) )).

tff(u325,negated_conjecture,(
    r1_tarski(sK0,k3_tarski(k1_xboole_0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:51:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (5254)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (5255)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (5256)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (5265)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (5255)Refutation not found, incomplete strategy% (5255)------------------------------
% 0.21/0.46  % (5255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5264)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (5257)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (5256)Refutation not found, incomplete strategy% (5256)------------------------------
% 0.21/0.47  % (5256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (5256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5256)Memory used [KB]: 6268
% 0.21/0.47  % (5256)Time elapsed: 0.057 s
% 0.21/0.47  % (5256)------------------------------
% 0.21/0.47  % (5256)------------------------------
% 0.21/0.47  % (5262)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (5255)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (5255)Memory used [KB]: 1663
% 0.21/0.47  % (5255)Time elapsed: 0.058 s
% 0.21/0.47  % (5255)------------------------------
% 0.21/0.47  % (5255)------------------------------
% 0.21/0.47  % (5258)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (5267)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (5268)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % SZS status CounterSatisfiable for theBenchmark
% 0.21/0.48  % (5254)# SZS output start Saturation.
% 0.21/0.48  tff(u385,axiom,
% 0.21/0.48      (![X0] : ((k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u384,axiom,
% 0.21/0.48      (![X4] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u383,negated_conjecture,
% 0.21/0.48      (k1_xboole_0 = sK1)).
% 0.21/0.48  
% 0.21/0.48  tff(u382,negated_conjecture,
% 0.21/0.48      (k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u381,axiom,
% 0.21/0.48      (![X0] : ((k3_xboole_0(X0,X0) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u380,axiom,
% 0.21/0.48      (![X1, X0] : ((k3_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u379,axiom,
% 0.21/0.48      (![X5, X4] : ((k3_xboole_0(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X4))) = X4)))).
% 0.21/0.48  
% 0.21/0.48  tff(u378,axiom,
% 0.21/0.48      (![X1, X0] : ((k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u377,axiom,
% 0.21/0.48      (![X0] : ((k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u376,axiom,
% 0.21/0.48      (![X0] : ((k3_tarski(k5_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u375,negated_conjecture,
% 0.21/0.48      (sK0 = k3_xboole_0(sK0,k3_tarski(k1_xboole_0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u374,axiom,
% 0.21/0.48      (![X1, X2] : ((~v1_xboole_0(X1) | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u373,axiom,
% 0.21/0.48      (![X1, X0] : ((~v1_xboole_0(X0) | r1_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u372,axiom,
% 0.21/0.48      (![X0] : ((~v1_xboole_0(X0) | r1_xboole_0(X0,X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u371,axiom,
% 0.21/0.48      (![X0] : ((~v1_xboole_0(X0) | (k1_xboole_0 = X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u370,axiom,
% 0.21/0.48      (![X1, X0] : ((~v1_xboole_0(X0) | (X0 = X1) | ~v1_xboole_0(X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u369,axiom,
% 0.21/0.48      (![X3, X2] : ((~v1_xboole_0(k3_xboole_0(X2,X3)) | r1_xboole_0(X2,X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u368,negated_conjecture,
% 0.21/0.48      ((~~v1_xboole_0(sK0)) | ~v1_xboole_0(sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u367,axiom,
% 0.21/0.48      v1_xboole_0(k1_xboole_0)).
% 0.21/0.48  
% 0.21/0.48  tff(u366,axiom,
% 0.21/0.48      (![X1, X3, X2] : ((~r2_hidden(X3,X1) | ~r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u365,axiom,
% 0.21/0.48      (![X0, X2] : ((~r2_hidden(X2,X0) | ~v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u364,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u363,axiom,
% 0.21/0.48      ((~(![X1] : (~r2_hidden(X1,k1_xboole_0)))) | (![X1] : (~r2_hidden(X1,k1_xboole_0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u362,axiom,
% 0.21/0.48      (![X0] : ((r2_hidden(sK2(X0),X0) | v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u361,axiom,
% 0.21/0.48      (![X1, X0] : ((r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u360,axiom,
% 0.21/0.48      (![X1] : ((r2_hidden(sK3(X1,X1),X1) | r1_xboole_0(X1,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u359,axiom,
% 0.21/0.48      (![X3, X2] : ((r2_hidden(sK3(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))),X2) | r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u358,axiom,
% 0.21/0.48      (![X3, X4] : ((r2_hidden(sK3(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))),X3) | r1_xboole_0(X3,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u357,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u356,axiom,
% 0.21/0.48      (![X5, X7, X6] : ((~r1_xboole_0(X5,X6) | r1_xboole_0(k3_xboole_0(X5,X6),k3_tarski(k5_enumset1(k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),k3_xboole_0(X5,X6),X7))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u355,axiom,
% 0.21/0.48      (![X5, X7, X6] : ((~r1_xboole_0(X5,X6) | r1_xboole_0(k3_xboole_0(X5,X6),k3_tarski(k5_enumset1(X7,X7,X7,X7,X7,X7,k3_xboole_0(X5,X6)))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u354,axiom,
% 0.21/0.48      (![X1, X2] : ((~r1_xboole_0(X1,X2) | r1_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u353,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u352,axiom,
% 0.21/0.48      (![X5, X4] : ((~r1_xboole_0(X4,X4) | r1_xboole_0(X4,k3_tarski(k5_enumset1(X5,X5,X5,X5,X5,X5,X4))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u351,axiom,
% 0.21/0.48      (![X3, X2] : ((~r1_xboole_0(X2,X2) | r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u350,axiom,
% 0.21/0.48      (![X1] : ((~r1_xboole_0(X1,X1) | v1_xboole_0(X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u349,axiom,
% 0.21/0.48      (![X3, X2] : ((~r1_xboole_0(X2,X2) | ~r2_hidden(X3,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u348,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) | r1_xboole_0(X1,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X1))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u347,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) | r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X2))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u346,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) | r1_xboole_0(X1,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u345,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_xboole_0(X1,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) | v1_xboole_0(X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u344,axiom,
% 0.21/0.48      (![X5, X4, X6] : ((~r1_xboole_0(X4,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X5))) | ~r2_hidden(X6,X4))))).
% 0.21/0.48  
% 0.21/0.48  tff(u343,axiom,
% 0.21/0.48      (![X9, X7, X8] : ((~r1_xboole_0(X7,k3_tarski(k5_enumset1(X9,X9,X9,X9,X9,X9,X7))) | r1_xboole_0(X7,k3_tarski(k5_enumset1(X8,X8,X8,X8,X8,X8,X7))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u342,axiom,
% 0.21/0.48      (![X5, X4, X6] : ((~r1_xboole_0(X4,k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X4))) | r1_xboole_0(X4,k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,X5))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u341,axiom,
% 0.21/0.48      (![X5, X6] : ((~r1_xboole_0(X5,k3_tarski(k5_enumset1(X6,X6,X6,X6,X6,X6,X5))) | r1_xboole_0(X5,X5))))).
% 0.21/0.48  
% 0.21/0.48  tff(u340,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_xboole_0(X0,k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,X0))) | v1_xboole_0(X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u339,negated_conjecture,
% 0.21/0.48      ((~~r1_xboole_0(sK0,k3_tarski(k1_xboole_0))) | ~r1_xboole_0(sK0,k3_tarski(k1_xboole_0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u338,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | (![X0] : (~r1_xboole_0(sK0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,sK0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u337,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | (![X0] : (~r1_xboole_0(sK0,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,X0))))))).
% 0.21/0.48  
% 0.21/0.48  tff(u336,negated_conjecture,
% 0.21/0.48      ((~r2_hidden(sK3(sK0,k3_tarski(k1_xboole_0)),sK0)) | ~r1_xboole_0(sK0,sK0))).
% 0.21/0.48  
% 0.21/0.48  tff(u335,axiom,
% 0.21/0.48      (![X3, X2, X4] : ((~r1_xboole_0(k3_xboole_0(X2,X3),k3_tarski(k5_enumset1(X4,X4,X4,X4,X4,X4,k3_xboole_0(X2,X3)))) | r1_xboole_0(X2,X3))))).
% 0.21/0.48  
% 0.21/0.48  tff(u334,axiom,
% 0.21/0.48      (![X1, X0, X2] : ((~r1_xboole_0(k3_xboole_0(X1,X2),k3_tarski(k5_enumset1(k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),k3_xboole_0(X1,X2),X0))) | r1_xboole_0(X1,X2))))).
% 0.21/0.48  
% 0.21/0.48  tff(u333,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))))).
% 0.21/0.48  
% 0.21/0.48  tff(u332,axiom,
% 0.21/0.48      (![X0] : (r1_xboole_0(X0,k1_xboole_0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u331,axiom,
% 0.21/0.48      (![X8] : (r1_xboole_0(k1_xboole_0,X8)))).
% 0.21/0.48  
% 0.21/0.48  tff(u330,axiom,
% 0.21/0.48      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 0.21/0.48  
% 0.21/0.48  tff(u329,axiom,
% 0.21/0.48      (![X1, X0] : (r1_tarski(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u328,axiom,
% 0.21/0.48      (![X7, X6] : (r1_tarski(X6,k3_tarski(k5_enumset1(X7,X7,X7,X7,X7,X7,X6)))))).
% 0.21/0.48  
% 0.21/0.48  tff(u327,axiom,
% 0.21/0.48      (![X0] : (r1_tarski(X0,X0)))).
% 0.21/0.48  
% 0.21/0.48  tff(u326,axiom,
% 0.21/0.48      (![X3] : (r1_tarski(k1_xboole_0,X3)))).
% 0.21/0.48  
% 0.21/0.48  tff(u325,negated_conjecture,
% 0.21/0.48      r1_tarski(sK0,k3_tarski(k1_xboole_0))).
% 0.21/0.48  
% 0.21/0.48  % (5254)# SZS output end Saturation.
% 0.21/0.48  % (5254)------------------------------
% 0.21/0.48  % (5254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5254)Termination reason: Satisfiable
% 0.21/0.48  
% 0.21/0.48  % (5254)Memory used [KB]: 6268
% 0.21/0.48  % (5254)Time elapsed: 0.070 s
% 0.21/0.48  % (5254)------------------------------
% 0.21/0.48  % (5254)------------------------------
% 0.21/0.48  % (5250)Success in time 0.124 s
%------------------------------------------------------------------------------
