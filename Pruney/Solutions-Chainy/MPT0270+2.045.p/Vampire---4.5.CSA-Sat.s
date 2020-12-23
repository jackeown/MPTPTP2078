%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:02 EST 2020

% Result     : CounterSatisfiable 2.51s
% Output     : Saturation 2.51s
% Verified   : 
% Statistics : Number of formulae       :   54 (  54 expanded)
%              Number of leaves         :   54 (  54 expanded)
%              Depth                    :    0
%              Number of atoms          :  128 ( 128 expanded)
%              Number of equality atoms :   40 (  40 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u5140,axiom,(
    ! [X5,X4] :
      ( k4_xboole_0(X5,X4) != X5
      | k4_xboole_0(X4,X5) = X4 ) )).

tff(u5139,axiom,(
    ! [X3,X2] :
      ( k4_xboole_0(X3,X2) != X3
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) )).

tff(u5138,axiom,(
    ! [X3,X2] :
      ( k4_xboole_0(X2,X3) != X2
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) )).

tff(u5137,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u5136,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X9] : k1_xboole_0 = k3_xboole_0(X9,k1_xboole_0) )).

tff(u5135,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X6] :
        ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)
        | k1_xboole_0 = k3_xboole_0(X6,k1_xboole_0) ) )).

tff(u5134,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X8] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8) )).

tff(u5133,negated_conjecture,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) )).

tff(u5132,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) )).

tff(u5131,negated_conjecture,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) )).

tff(u5130,negated_conjecture,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) )).

tff(u5129,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ ! [X49,X50] :
          ( ~ r1_xboole_0(k1_tarski(X50),k1_tarski(X49))
          | k1_tarski(X49) = k1_tarski(X50) )
    | ! [X0] : k1_xboole_0 = k2_tarski(X0,X0) )).

tff(u5128,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) )).

tff(u5127,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ ! [X49,X50] :
          ( ~ r1_xboole_0(k1_tarski(X50),k1_tarski(X49))
          | k1_tarski(X49) = k1_tarski(X50) )
    | ! [X0] : k1_xboole_0 = k1_tarski(X0) )).

tff(u5126,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u5125,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) )).

tff(u5124,negated_conjecture,
    ( ~ ! [X1] : ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u5123,negated_conjecture,
    ( ~ ! [X1] : ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 )).

tff(u5122,axiom,(
    ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) )).

tff(u5121,axiom,(
    ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) )).

tff(u5120,axiom,(
    ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) )).

tff(u5119,axiom,(
    ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) )).

tff(u5118,axiom,(
    ! [X1,X3,X5,X0,X2,X4] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) )).

tff(u5117,axiom,(
    ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) )).

tff(u5116,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | sK1 = k4_xboole_0(sK1,k1_xboole_0) )).

tff(u5115,axiom,(
    v1_xboole_0(k1_xboole_0) )).

tff(u5114,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) )).

tff(u5113,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u5112,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X1,X0) = k1_xboole_0 ) )).

tff(u5111,axiom,(
    ! [X5,X4] :
      ( ~ r1_xboole_0(X4,X5)
      | k4_xboole_0(X5,X4) = X5 ) )).

tff(u5110,negated_conjecture,
    ( ~ ! [X1] : ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X13] : r1_xboole_0(k1_xboole_0,X13) )).

tff(u5109,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) )).

tff(u5108,axiom,(
    ! [X1,X0] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) )).

tff(u5107,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X3,X4] :
        ( r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4))
        | ~ r1_xboole_0(X3,X4) ) )).

tff(u5106,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X1,X2] :
        ( r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2))
        | ~ r1_xboole_0(X2,X1) ) )).

tff(u5105,negated_conjecture,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

tff(u5104,negated_conjecture,
    ( ~ ! [X1] : ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X3] : r1_xboole_0(X3,k1_xboole_0) )).

tff(u5103,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | r1_xboole_0(k1_xboole_0,sK1) )).

tff(u5102,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u5101,axiom,(
    ! [X1,X0,X2] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) )).

tff(u5100,negated_conjecture,
    ( ~ ! [X1] : ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
    | ! [X0] : ~ r2_hidden(X0,k1_xboole_0) )).

tff(u5099,negated_conjecture,
    ( ~ ! [X1] : ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ r2_hidden(sK0,k1_xboole_0) )).

tff(u5098,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ ! [X49,X50] :
          ( ~ r1_xboole_0(k1_tarski(X50),k1_tarski(X49))
          | k1_tarski(X49) = k1_tarski(X50) )
    | ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_xboole_0,X1) ) )).

tff(u5097,negated_conjecture,
    ( ~ r2_hidden(sK0,sK1)
    | r2_hidden(sK0,sK1) )).

tff(u5096,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X0] :
        ( r2_hidden(sK0,X0)
        | r1_xboole_0(k1_xboole_0,X0) ) )).

tff(u5095,axiom,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) )).

tff(u5094,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) )).

tff(u5093,axiom,(
    ! [X1,X0] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X1,X0))
      | r1_xboole_0(X0,X1) ) )).

tff(u5092,negated_conjecture,
    ( ~ ! [X1] : ~ r1_tarski(k1_tarski(X1),k1_xboole_0)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) )).

tff(u5091,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X5,X4] :
        ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(X4,X5))
        | ~ r1_xboole_0(X5,X4) ) )).

tff(u5090,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X3,X2] :
        ( ~ r1_tarski(k1_xboole_0,k3_xboole_0(X2,X3))
        | ~ r1_xboole_0(X2,X3) ) )).

tff(u5089,axiom,(
    ! [X1,X0] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) )).

tff(u5088,negated_conjecture,
    ( ~ r1_xboole_0(k1_tarski(sK0),sK1)
    | ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ~ ! [X49,X50] :
          ( ~ r1_xboole_0(k1_tarski(X50),k1_tarski(X49))
          | k1_tarski(X49) = k1_tarski(X50) )
    | ! [X1,X0] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ r2_hidden(X0,X1) ) )).

tff(u5087,negated_conjecture,
    ( ~ ! [X0] : ~ r2_hidden(X0,k1_tarski(sK0))
    | ! [X1] :
        ( r1_tarski(k1_xboole_0,X1)
        | ~ r2_hidden(sK0,X1) ) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:15:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (6759)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (6762)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (6753)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (6748)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (6747)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (6746)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (6758)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (6752)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (6757)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (6758)Refutation not found, incomplete strategy% (6758)------------------------------
% 0.21/0.48  % (6758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6758)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (6758)Memory used [KB]: 10618
% 0.21/0.48  % (6758)Time elapsed: 0.076 s
% 0.21/0.48  % (6758)------------------------------
% 0.21/0.48  % (6758)------------------------------
% 0.21/0.48  % (6749)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (6750)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (6756)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (6754)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (6763)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (6764)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (6755)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (6761)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (6760)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 2.51/0.71  % SZS status CounterSatisfiable for theBenchmark
% 2.51/0.71  % (6763)# SZS output start Saturation.
% 2.51/0.71  tff(u5140,axiom,
% 2.51/0.71      (![X5, X4] : (((k4_xboole_0(X5,X4) != X5) | (k4_xboole_0(X4,X5) = X4))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5139,axiom,
% 2.51/0.71      (![X3, X2] : (((k4_xboole_0(X3,X2) != X3) | (k1_xboole_0 = k3_xboole_0(X2,X3)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5138,axiom,
% 2.51/0.71      (![X3, X2] : (((k4_xboole_0(X2,X3) != X2) | (k1_xboole_0 = k3_xboole_0(X2,X3)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5137,axiom,
% 2.51/0.71      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5136,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X9] : ((k1_xboole_0 = k3_xboole_0(X9,k1_xboole_0)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5135,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X6] : (((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X6)) | (k1_xboole_0 = k3_xboole_0(X6,k1_xboole_0))))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5134,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X8] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X8)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5133,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)))).
% 2.51/0.71  
% 2.51/0.71  tff(u5132,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | (![X2] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5131,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)))).
% 2.51/0.71  
% 2.51/0.71  tff(u5130,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)))).
% 2.51/0.71  
% 2.51/0.71  tff(u5129,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_tarski(sK0),sK1)) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (~(![X49, X50] : ((~r1_xboole_0(k1_tarski(X50),k1_tarski(X49)) | (k1_tarski(X49) = k1_tarski(X50)))))) | (![X0] : ((k1_xboole_0 = k2_tarski(X0,X0)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5128,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (k1_xboole_0 = k1_tarski(sK0)))).
% 2.51/0.71  
% 2.51/0.71  tff(u5127,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_tarski(sK0),sK1)) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (~(![X49, X50] : ((~r1_xboole_0(k1_tarski(X50),k1_tarski(X49)) | (k1_tarski(X49) = k1_tarski(X50)))))) | (![X0] : ((k1_xboole_0 = k1_tarski(X0)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5126,axiom,
% 2.51/0.71      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5125,axiom,
% 2.51/0.71      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5124,negated_conjecture,
% 2.51/0.71      ((~(![X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0)))) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X0] : ((k4_xboole_0(X0,k1_xboole_0) = X0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5123,negated_conjecture,
% 2.51/0.71      ((~(![X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0)))) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X2] : ((k5_xboole_0(X2,k1_xboole_0) = X2))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5122,axiom,
% 2.51/0.71      (![X1, X0] : ((k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5121,axiom,
% 2.51/0.71      (![X1, X0, X2] : ((k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5120,axiom,
% 2.51/0.71      (![X1, X3, X0, X2] : ((k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5119,axiom,
% 2.51/0.71      (![X1, X3, X0, X2, X4] : ((k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5118,axiom,
% 2.51/0.71      (![X1, X3, X5, X0, X2, X4] : ((k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5117,axiom,
% 2.51/0.71      (![X1, X3, X5, X0, X2, X4, X6] : ((k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5116,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_tarski(sK0),sK1)) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (sK1 = k4_xboole_0(sK1,k1_xboole_0)))).
% 2.51/0.71  
% 2.51/0.71  tff(u5115,axiom,
% 2.51/0.71      v1_xboole_0(k1_xboole_0)).
% 2.51/0.71  
% 2.51/0.71  tff(u5114,axiom,
% 2.51/0.71      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) = X0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5113,axiom,
% 2.51/0.71      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5112,axiom,
% 2.51/0.71      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X1,X0) = k1_xboole_0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5111,axiom,
% 2.51/0.71      (![X5, X4] : ((~r1_xboole_0(X4,X5) | (k4_xboole_0(X5,X4) = X5))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5110,negated_conjecture,
% 2.51/0.71      ((~(![X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0)))) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X13] : (r1_xboole_0(k1_xboole_0,X13))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5109,axiom,
% 2.51/0.71      (![X1, X0] : ((r1_xboole_0(X0,X1) | ~r1_xboole_0(X1,X0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5108,axiom,
% 2.51/0.71      (![X1, X0] : ((r1_xboole_0(X0,X1) | (k4_xboole_0(X0,X1) != X0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5107,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X3, X4] : ((r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4)) | ~r1_xboole_0(X3,X4)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5106,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X1, X2] : ((r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X2,X1)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5105,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | r1_xboole_0(k1_xboole_0,k1_xboole_0))).
% 2.51/0.71  
% 2.51/0.71  tff(u5104,negated_conjecture,
% 2.51/0.71      ((~(![X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0)))) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X3] : (r1_xboole_0(X3,k1_xboole_0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5103,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_tarski(sK0),sK1)) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | r1_xboole_0(k1_xboole_0,sK1))).
% 2.51/0.71  
% 2.51/0.71  tff(u5102,axiom,
% 2.51/0.71      (![X1, X0, X2] : ((~r2_hidden(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X0,X1))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5101,axiom,
% 2.51/0.71      (![X1, X0, X2] : ((~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5100,negated_conjecture,
% 2.51/0.71      ((~(![X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0)))) | (![X0] : (~r2_hidden(X0,k1_xboole_0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5099,negated_conjecture,
% 2.51/0.71      ((~(![X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0)))) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | ~r2_hidden(sK0,k1_xboole_0))).
% 2.51/0.71  
% 2.51/0.71  tff(u5098,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_tarski(sK0),sK1)) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (~(![X49, X50] : ((~r1_xboole_0(k1_tarski(X50),k1_tarski(X49)) | (k1_tarski(X49) = k1_tarski(X50)))))) | (![X1, X0] : ((r2_hidden(X0,X1) | ~r1_tarski(k1_xboole_0,X1)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5097,negated_conjecture,
% 2.51/0.71      ((~r2_hidden(sK0,sK1)) | r2_hidden(sK0,sK1))).
% 2.51/0.71  
% 2.51/0.71  tff(u5096,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X0] : ((r2_hidden(sK0,X0) | r1_xboole_0(k1_xboole_0,X0)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5095,axiom,
% 2.51/0.71      (![X0] : ((r2_hidden(sK2(X0),X0) | (k1_xboole_0 = X0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5094,axiom,
% 2.51/0.71      (![X1, X0] : ((r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5093,axiom,
% 2.51/0.71      (![X1, X0] : ((r2_hidden(sK3(X0,X1),k3_xboole_0(X1,X0)) | r1_xboole_0(X0,X1))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5092,negated_conjecture,
% 2.51/0.71      ((~(![X1] : (~r1_tarski(k1_tarski(X1),k1_xboole_0)))) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | ~r1_tarski(k1_xboole_0,k1_xboole_0))).
% 2.51/0.71  
% 2.51/0.71  tff(u5091,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X5, X4] : ((~r1_tarski(k1_xboole_0,k3_xboole_0(X4,X5)) | ~r1_xboole_0(X5,X4)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5090,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X3, X2] : ((~r1_tarski(k1_xboole_0,k3_xboole_0(X2,X3)) | ~r1_xboole_0(X2,X3)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5089,axiom,
% 2.51/0.71      (![X1, X0] : ((~r1_tarski(X0,X1) | (k3_xboole_0(X0,X1) = X0))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5088,negated_conjecture,
% 2.51/0.71      ((~r1_xboole_0(k1_tarski(sK0),sK1)) | (~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (~(![X49, X50] : ((~r1_xboole_0(k1_tarski(X50),k1_tarski(X49)) | (k1_tarski(X49) = k1_tarski(X50)))))) | (![X1, X0] : ((r1_tarski(k1_xboole_0,X1) | ~r2_hidden(X0,X1)))))).
% 2.51/0.71  
% 2.51/0.71  tff(u5087,negated_conjecture,
% 2.51/0.71      ((~(![X0] : (~r2_hidden(X0,k1_tarski(sK0))))) | (![X1] : ((r1_tarski(k1_xboole_0,X1) | ~r2_hidden(sK0,X1)))))).
% 2.51/0.71  
% 2.51/0.71  % (6763)# SZS output end Saturation.
% 2.51/0.71  % (6763)------------------------------
% 2.51/0.71  % (6763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.71  % (6763)Termination reason: Satisfiable
% 2.51/0.71  
% 2.51/0.71  % (6763)Memory used [KB]: 7803
% 2.51/0.71  % (6763)Time elapsed: 0.256 s
% 2.51/0.71  % (6763)------------------------------
% 2.51/0.71  % (6763)------------------------------
% 2.51/0.71  % (6743)Success in time 0.355 s
%------------------------------------------------------------------------------
