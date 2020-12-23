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
% DateTime   : Thu Dec  3 12:40:46 EST 2020

% Result     : CounterSatisfiable 0.20s
% Output     : Saturation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    0
%              Number of atoms          :   56 (  56 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u195,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) )).

tff(u194,axiom,(
    ! [X3,X2] :
      ( k1_xboole_0 != X2
      | r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))) ) )).

tff(u193,axiom,(
    ! [X1] :
      ( k1_xboole_0 != X1
      | r1_xboole_0(X1,X1) ) )).

tff(u192,axiom,(
    ! [X7,X6] :
      ( k5_enumset1(X7,X7,X7,X7,X7,X7,X7) != X6
      | r1_xboole_0(X6,k4_xboole_0(X6,k5_enumset1(X7,X7,X7,X7,X7,X7,X7)))
      | k5_enumset1(X7,X7,X7,X7,X7,X7,X7) = k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),X6) ) )).

tff(u191,axiom,(
    ! [X5,X4] :
      ( k5_enumset1(X5,X5,X5,X5,X5,X5,X5) != X4
      | r1_xboole_0(X4,k4_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))
      | k4_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)) = X4 ) )).

tff(u190,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )).

tff(u189,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) )).

tff(u188,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u187,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) )).

tff(u186,negated_conjecture,
    ( sK0 != k4_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,sK0)
    | k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) )).

tff(u185,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) )).

tff(u184,axiom,(
    ! [X3,X2] :
      ( k4_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) = k5_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) = k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),X2) ) )).

tff(u183,axiom,(
    ! [X1,X0] :
      ( k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0 ) )).

tff(u182,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u181,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u180,axiom,(
    ! [X1,X0] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) ) )).

tff(u179,axiom,(
    ! [X1,X0] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))
      | k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0 ) )).

tff(u178,axiom,(
    ! [X5,X4] :
      ( k5_enumset1(X5,X5,X5,X5,X5,X5,X5) = k5_xboole_0(X4,k4_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))
      | k5_enumset1(X5,X5,X5,X5,X5,X5,X5) = k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),X4) ) )).

tff(u177,axiom,(
    ! [X3,X2] :
      ( k5_enumset1(X3,X3,X3,X3,X3,X3,X3) = k5_xboole_0(X2,k4_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))
      | k4_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) = X2 ) )).

tff(u176,axiom,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0 )).

tff(u175,negated_conjecture,
    ( sK0 != k4_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | ~ r2_hidden(sK1,sK0)
    | sK1 = k3_tarski(k1_xboole_0) )).

tff(u174,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) )).

tff(u173,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

tff(u172,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) )).

tff(u171,axiom,(
    ! [X3,X2] :
      ( r1_xboole_0(X3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2))
      | r2_hidden(X2,X3) ) )).

tff(u170,axiom,(
    ! [X1] : r1_xboole_0(k1_xboole_0,X1) )).

tff(u169,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) )).

tff(u168,axiom,(
    ! [X1,X0] :
      ( ~ r2_hidden(X0,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) ) )).

tff(u167,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) ) )).

tff(u166,axiom,(
    ! [X1,X0] :
      ( r2_hidden(X0,X1)
      | k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X1 ) )).

tff(u165,negated_conjecture,
    ( ~ r2_hidden(sK1,sK0)
    | r2_hidden(sK1,sK0) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (14555)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (14554)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.45  % (14549)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (14552)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (14561)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (14559)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (14544)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (14551)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (14553)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % SZS status CounterSatisfiable for theBenchmark
% 0.20/0.47  % (14547)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (14557)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (14545)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (14554)# SZS output start Saturation.
% 0.20/0.47  tff(u195,axiom,
% 0.20/0.47      (![X1, X0] : (((k4_xboole_0(X0,X1) != X0) | r1_xboole_0(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u194,axiom,
% 0.20/0.47      (![X3, X2] : (((k1_xboole_0 != X2) | r1_xboole_0(X2,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u193,axiom,
% 0.20/0.47      (![X1] : (((k1_xboole_0 != X1) | r1_xboole_0(X1,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u192,axiom,
% 0.20/0.47      (![X7, X6] : (((k5_enumset1(X7,X7,X7,X7,X7,X7,X7) != X6) | r1_xboole_0(X6,k4_xboole_0(X6,k5_enumset1(X7,X7,X7,X7,X7,X7,X7))) | (k5_enumset1(X7,X7,X7,X7,X7,X7,X7) = k4_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),X6)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u191,axiom,
% 0.20/0.47      (![X5, X4] : (((k5_enumset1(X5,X5,X5,X5,X5,X5,X5) != X4) | r1_xboole_0(X4,k4_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5))) | (k4_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)) = X4))))).
% 0.20/0.47  
% 0.20/0.47  tff(u190,axiom,
% 0.20/0.47      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u189,axiom,
% 0.20/0.47      (![X0] : ((k1_xboole_0 = k4_xboole_0(X0,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u188,axiom,
% 0.20/0.47      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u187,axiom,
% 0.20/0.47      (![X0] : ((k1_xboole_0 = k5_xboole_0(X0,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u186,negated_conjecture,
% 0.20/0.47      ((~(sK0 = k4_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | (~r2_hidden(sK1,sK0)) | (k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))).
% 0.20/0.47  
% 0.20/0.47  tff(u185,axiom,
% 0.20/0.47      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u184,axiom,
% 0.20/0.47      (![X3, X2] : (((k4_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) = k5_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) | (k5_enumset1(X3,X3,X3,X3,X3,X3,X3) = k4_xboole_0(k5_enumset1(X3,X3,X3,X3,X3,X3,X3),X2)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u183,axiom,
% 0.20/0.47      (![X1, X0] : (((k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k5_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) | (k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u182,axiom,
% 0.20/0.47      (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u181,axiom,
% 0.20/0.47      (![X0] : ((k5_xboole_0(X0,k1_xboole_0) = X0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u180,axiom,
% 0.20/0.47      (![X1, X0] : (((k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) | (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u179,axiom,
% 0.20/0.47      (![X1, X0] : (((k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)))) | (k4_xboole_0(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u178,axiom,
% 0.20/0.47      (![X5, X4] : (((k5_enumset1(X5,X5,X5,X5,X5,X5,X5) = k5_xboole_0(X4,k4_xboole_0(X4,k5_enumset1(X5,X5,X5,X5,X5,X5,X5)))) | (k5_enumset1(X5,X5,X5,X5,X5,X5,X5) = k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X5),X4)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u177,axiom,
% 0.20/0.47      (![X3, X2] : (((k5_enumset1(X3,X3,X3,X3,X3,X3,X3) = k5_xboole_0(X2,k4_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))) | (k4_xboole_0(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) = X2))))).
% 0.20/0.47  
% 0.20/0.47  tff(u176,axiom,
% 0.20/0.47      (![X0] : ((k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u175,negated_conjecture,
% 0.20/0.47      ((~(sK0 = k4_xboole_0(sK0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | (~r2_hidden(sK1,sK0)) | (sK1 = k3_tarski(k1_xboole_0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u174,axiom,
% 0.20/0.47      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u173,axiom,
% 0.20/0.47      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 0.20/0.47  
% 0.20/0.47  tff(u172,axiom,
% 0.20/0.47      (![X0] : (r1_xboole_0(X0,k1_xboole_0)))).
% 0.20/0.47  
% 0.20/0.47  tff(u171,axiom,
% 0.20/0.47      (![X3, X2] : ((r1_xboole_0(X3,k5_enumset1(X2,X2,X2,X2,X2,X2,X2)) | r2_hidden(X2,X3))))).
% 0.20/0.47  
% 0.20/0.47  tff(u170,axiom,
% 0.20/0.47      (![X1] : (r1_xboole_0(k1_xboole_0,X1)))).
% 0.20/0.47  
% 0.20/0.47  tff(u169,axiom,
% 0.20/0.47      (![X1, X0] : ((r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u168,axiom,
% 0.20/0.47      (![X1, X0] : ((~r2_hidden(X0,X1) | (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(X1,k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))))))).
% 0.20/0.47  
% 0.20/0.47  tff(u167,axiom,
% 0.20/0.47      (![X1, X0] : ((r2_hidden(X0,X1) | (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)))))).
% 0.20/0.47  
% 0.20/0.47  tff(u166,axiom,
% 0.20/0.47      (![X1, X0] : ((r2_hidden(X0,X1) | (k4_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = X1))))).
% 0.20/0.47  
% 0.20/0.47  tff(u165,negated_conjecture,
% 0.20/0.47      ((~r2_hidden(sK1,sK0)) | r2_hidden(sK1,sK0))).
% 0.20/0.47  
% 0.20/0.47  % (14554)# SZS output end Saturation.
% 0.20/0.47  % (14554)------------------------------
% 0.20/0.47  % (14554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (14554)Termination reason: Satisfiable
% 0.20/0.47  
% 0.20/0.47  % (14554)Memory used [KB]: 10618
% 0.20/0.47  % (14554)Time elapsed: 0.058 s
% 0.20/0.47  % (14554)------------------------------
% 0.20/0.47  % (14554)------------------------------
% 0.20/0.48  % (14543)Success in time 0.123 s
%------------------------------------------------------------------------------
