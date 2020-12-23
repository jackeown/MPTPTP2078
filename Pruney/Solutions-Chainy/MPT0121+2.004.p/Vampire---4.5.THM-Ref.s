%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:56 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 205 expanded)
%              Number of leaves         :    9 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  118 ( 458 expanded)
%              Number of equality atoms :   22 ( 148 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2710,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2707,f25])).

fof(f25,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f2707,plain,(
    ~ r1_xboole_0(sK0,sK3) ),
    inference(resolution,[],[f2676,f1207])).

fof(f1207,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(forward_demodulation,[],[f1206,f29])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f1206,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_xboole_0(X0,X0),X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(subsumption_resolution,[],[f1205,f711])).

fof(f711,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = X2
      | ~ r1_xboole_0(X3,X2) ) ),
    inference(subsumption_resolution,[],[f680,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f680,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X3) = X2
      | ~ r1_xboole_0(X3,X2)
      | ~ r1_tarski(k4_xboole_0(X2,X3),X2) ) ),
    inference(superposition,[],[f125,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f125,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f44,f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f1205,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(k2_xboole_0(X0,X0),X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(forward_demodulation,[],[f1198,f29])).

fof(f1198,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X0) != k4_xboole_0(X0,X1)
      | r1_xboole_0(k2_xboole_0(X0,X0),X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f1188])).

fof(f1188,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X0) != k4_xboole_0(X0,X1)
      | r1_xboole_0(k2_xboole_0(X0,X0),X1)
      | ~ r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f139,f125])).

fof(f139,plain,(
    ! [X21,X22,X20] :
      ( k2_xboole_0(X20,X21) != k2_xboole_0(k4_xboole_0(X20,X22),X21)
      | r1_xboole_0(k2_xboole_0(X20,X21),X22)
      | ~ r1_xboole_0(X22,X21) ) ),
    inference(superposition,[],[f38,f44])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f2676,plain,(
    ~ r1_xboole_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f2673,f26])).

fof(f26,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f2673,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f2645,f1207])).

fof(f2645,plain,
    ( ~ r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK3,sK0) ),
    inference(subsumption_resolution,[],[f2642,f27])).

fof(f27,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f2642,plain,
    ( ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK1)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f1724,f1207])).

fof(f1724,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK3,sK0)
    | ~ r1_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f1620,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1620,plain,
    ( ~ r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK3,sK2) ),
    inference(resolution,[],[f1608,f120])).

fof(f120,plain,(
    ! [X6,X8,X7,X5] :
      ( r1_xboole_0(X8,k2_xboole_0(X5,k2_xboole_0(X6,X7)))
      | ~ r1_xboole_0(X8,k2_xboole_0(X5,X6))
      | ~ r1_xboole_0(X8,X7) ) ),
    inference(superposition,[],[f41,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1608,plain,(
    ~ r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f1207,f45])).

fof(f45,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) ),
    inference(backward_demodulation,[],[f28,f40])).

fof(f28,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:55:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.47  % (6051)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (6042)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (6043)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (6044)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (6057)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (6050)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (6046)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (6052)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (6049)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (6045)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (6056)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (6048)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (6055)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.54  % (6053)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.41/0.55  % (6047)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.41/0.55  % (6054)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.41/0.56  % (6059)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.41/0.56  % (6058)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.38/0.69  % (6045)Refutation found. Thanks to Tanya!
% 2.38/0.69  % SZS status Theorem for theBenchmark
% 2.38/0.69  % SZS output start Proof for theBenchmark
% 2.38/0.69  fof(f2710,plain,(
% 2.38/0.69    $false),
% 2.38/0.69    inference(subsumption_resolution,[],[f2707,f25])).
% 2.38/0.69  fof(f25,plain,(
% 2.38/0.69    r1_xboole_0(sK0,sK3)),
% 2.38/0.69    inference(cnf_transformation,[],[f23])).
% 2.38/0.69  fof(f23,plain,(
% 2.38/0.69    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 2.38/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).
% 2.38/0.69  fof(f22,plain,(
% 2.38/0.69    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 2.38/0.69    introduced(choice_axiom,[])).
% 2.38/0.69  fof(f18,plain,(
% 2.38/0.69    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 2.38/0.69    inference(flattening,[],[f17])).
% 2.38/0.69  fof(f17,plain,(
% 2.38/0.69    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 2.38/0.69    inference(ennf_transformation,[],[f15])).
% 2.38/0.69  fof(f15,negated_conjecture,(
% 2.38/0.69    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 2.38/0.69    inference(negated_conjecture,[],[f14])).
% 2.38/0.69  fof(f14,conjecture,(
% 2.38/0.69    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).
% 2.38/0.69  fof(f2707,plain,(
% 2.38/0.69    ~r1_xboole_0(sK0,sK3)),
% 2.38/0.69    inference(resolution,[],[f2676,f1207])).
% 2.38/0.69  fof(f1207,plain,(
% 2.38/0.69    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X1,X0)) )),
% 2.38/0.69    inference(forward_demodulation,[],[f1206,f29])).
% 2.38/0.69  fof(f29,plain,(
% 2.38/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.38/0.69    inference(cnf_transformation,[],[f16])).
% 2.38/0.69  fof(f16,plain,(
% 2.38/0.69    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.38/0.69    inference(rectify,[],[f2])).
% 2.38/0.69  fof(f2,axiom,(
% 2.38/0.69    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.38/0.69  fof(f1206,plain,(
% 2.38/0.69    ( ! [X0,X1] : (r1_xboole_0(k2_xboole_0(X0,X0),X1) | ~r1_xboole_0(X1,X0)) )),
% 2.38/0.69    inference(subsumption_resolution,[],[f1205,f711])).
% 2.38/0.69  fof(f711,plain,(
% 2.38/0.69    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = X2 | ~r1_xboole_0(X3,X2)) )),
% 2.38/0.69    inference(subsumption_resolution,[],[f680,f30])).
% 2.38/0.69  fof(f30,plain,(
% 2.38/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f4])).
% 2.38/0.69  fof(f4,axiom,(
% 2.38/0.69    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.38/0.69  fof(f680,plain,(
% 2.38/0.69    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = X2 | ~r1_xboole_0(X3,X2) | ~r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 2.38/0.69    inference(superposition,[],[f125,f36])).
% 2.38/0.69  fof(f36,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f19])).
% 2.38/0.69  fof(f19,plain,(
% 2.38/0.69    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.38/0.69    inference(ennf_transformation,[],[f3])).
% 2.38/0.69  fof(f3,axiom,(
% 2.38/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.38/0.69  fof(f125,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),X0) | ~r1_xboole_0(X1,X0)) )),
% 2.38/0.69    inference(superposition,[],[f44,f29])).
% 2.38/0.69  fof(f44,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f21])).
% 2.38/0.69  fof(f21,plain,(
% 2.38/0.69    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 2.38/0.69    inference(ennf_transformation,[],[f11])).
% 2.38/0.69  fof(f11,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 2.38/0.69  fof(f1205,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(k2_xboole_0(X0,X0),X1) | ~r1_xboole_0(X1,X0)) )),
% 2.38/0.69    inference(forward_demodulation,[],[f1198,f29])).
% 2.38/0.69  fof(f1198,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X0) != k4_xboole_0(X0,X1) | r1_xboole_0(k2_xboole_0(X0,X0),X1) | ~r1_xboole_0(X1,X0)) )),
% 2.38/0.69    inference(duplicate_literal_removal,[],[f1188])).
% 2.38/0.69  fof(f1188,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X0) != k4_xboole_0(X0,X1) | r1_xboole_0(k2_xboole_0(X0,X0),X1) | ~r1_xboole_0(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 2.38/0.69    inference(superposition,[],[f139,f125])).
% 2.38/0.69  fof(f139,plain,(
% 2.38/0.69    ( ! [X21,X22,X20] : (k2_xboole_0(X20,X21) != k2_xboole_0(k4_xboole_0(X20,X22),X21) | r1_xboole_0(k2_xboole_0(X20,X21),X22) | ~r1_xboole_0(X22,X21)) )),
% 2.38/0.69    inference(superposition,[],[f38,f44])).
% 2.38/0.69  fof(f38,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f24])).
% 2.38/0.69  fof(f24,plain,(
% 2.38/0.69    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.38/0.69    inference(nnf_transformation,[],[f10])).
% 2.38/0.69  fof(f10,axiom,(
% 2.38/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.38/0.69  fof(f2676,plain,(
% 2.38/0.69    ~r1_xboole_0(sK3,sK0)),
% 2.38/0.69    inference(subsumption_resolution,[],[f2673,f26])).
% 2.38/0.69  fof(f26,plain,(
% 2.38/0.69    r1_xboole_0(sK1,sK3)),
% 2.38/0.69    inference(cnf_transformation,[],[f23])).
% 2.38/0.69  fof(f2673,plain,(
% 2.38/0.69    ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK1,sK3)),
% 2.38/0.69    inference(resolution,[],[f2645,f1207])).
% 2.38/0.69  fof(f2645,plain,(
% 2.38/0.69    ~r1_xboole_0(sK3,sK1) | ~r1_xboole_0(sK3,sK0)),
% 2.38/0.69    inference(subsumption_resolution,[],[f2642,f27])).
% 2.38/0.69  fof(f27,plain,(
% 2.38/0.69    r1_xboole_0(sK2,sK3)),
% 2.38/0.69    inference(cnf_transformation,[],[f23])).
% 2.38/0.69  fof(f2642,plain,(
% 2.38/0.69    ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK3,sK1) | ~r1_xboole_0(sK2,sK3)),
% 2.38/0.69    inference(resolution,[],[f1724,f1207])).
% 2.38/0.69  fof(f1724,plain,(
% 2.38/0.69    ~r1_xboole_0(sK3,sK2) | ~r1_xboole_0(sK3,sK0) | ~r1_xboole_0(sK3,sK1)),
% 2.38/0.69    inference(resolution,[],[f1620,f41])).
% 2.38/0.69  fof(f41,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f20])).
% 2.38/0.69  fof(f20,plain,(
% 2.38/0.69    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.38/0.69    inference(ennf_transformation,[],[f8])).
% 2.38/0.69  fof(f8,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.38/0.69  fof(f1620,plain,(
% 2.38/0.69    ~r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK3,sK2)),
% 2.38/0.69    inference(resolution,[],[f1608,f120])).
% 2.38/0.69  fof(f120,plain,(
% 2.38/0.69    ( ! [X6,X8,X7,X5] : (r1_xboole_0(X8,k2_xboole_0(X5,k2_xboole_0(X6,X7))) | ~r1_xboole_0(X8,k2_xboole_0(X5,X6)) | ~r1_xboole_0(X8,X7)) )),
% 2.38/0.69    inference(superposition,[],[f41,f40])).
% 2.38/0.69  fof(f40,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.38/0.69    inference(cnf_transformation,[],[f7])).
% 2.38/0.69  fof(f7,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.38/0.69  fof(f1608,plain,(
% 2.38/0.69    ~r1_xboole_0(sK3,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 2.38/0.69    inference(resolution,[],[f1207,f45])).
% 2.38/0.69  fof(f45,plain,(
% 2.38/0.69    ~r1_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3)),
% 2.38/0.69    inference(backward_demodulation,[],[f28,f40])).
% 2.38/0.69  fof(f28,plain,(
% 2.38/0.69    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 2.38/0.69    inference(cnf_transformation,[],[f23])).
% 2.38/0.69  % SZS output end Proof for theBenchmark
% 2.38/0.69  % (6045)------------------------------
% 2.38/0.69  % (6045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.69  % (6045)Termination reason: Refutation
% 2.38/0.69  
% 2.38/0.69  % (6045)Memory used [KB]: 3454
% 2.38/0.69  % (6045)Time elapsed: 0.240 s
% 2.38/0.69  % (6045)------------------------------
% 2.38/0.69  % (6045)------------------------------
% 2.38/0.69  % (6041)Success in time 0.323 s
%------------------------------------------------------------------------------
