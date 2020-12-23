%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:34 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 272 expanded)
%              Number of leaves         :   15 (  83 expanded)
%              Depth                    :   22
%              Number of atoms          :   96 ( 399 expanded)
%              Number of equality atoms :   50 ( 199 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4255,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4253,f3019])).

fof(f3019,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f3006])).

fof(f3006,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f34,f2941])).

fof(f2941,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f2415,f2228])).

fof(f2228,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f511,f437])).

fof(f437,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f37,f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f511,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f510,f88])).

fof(f88,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4) ),
    inference(resolution,[],[f32,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f65,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f65,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f39,f26])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f510,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f498,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f498,plain,(
    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f479,f134])).

fof(f134,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2)) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f479,plain,(
    ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(superposition,[],[f445,f29])).

fof(f445,plain,(
    ! [X20] : k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X20)) = k3_xboole_0(sK0,X20) ),
    inference(superposition,[],[f37,f89])).

fof(f89,plain,(
    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f22,f31])).

fof(f22,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f2415,plain,(
    ! [X0] : k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f37,f2399])).

fof(f2399,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2398,f89])).

fof(f2398,plain,(
    k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2364,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f2364,plain,(
    k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f645,f2228])).

fof(f645,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f40,f37])).

fof(f40,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f36,f31,f31])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4253,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f4244,f23])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f4244,plain,(
    r1_tarski(sK0,sK1) ),
    inference(forward_demodulation,[],[f4231,f205])).

fof(f205,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f201,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f201,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f183,f41])).

fof(f41,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f28,f25])).

fof(f183,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f35,f24])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f4231,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f66,f2440])).

fof(f2440,plain,(
    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f2433,f32])).

fof(f2433,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f2418,f28])).

fof(f2418,plain,(
    r1_tarski(k5_xboole_0(sK1,sK0),sK1) ),
    inference(superposition,[],[f66,f2399])).

fof(f66,plain,(
    ! [X2,X1] : r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f39,f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (3505)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (3507)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (3510)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (3503)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (3511)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (3513)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (3501)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (3509)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (3504)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (3502)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (3515)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (3516)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (3508)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (3517)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (3518)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (3512)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (3506)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.52  % (3514)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.54/0.56  % (3513)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f4255,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(subsumption_resolution,[],[f4253,f3019])).
% 1.54/0.56  fof(f3019,plain,(
% 1.54/0.56    r1_xboole_0(sK0,sK2)),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f3006])).
% 1.54/0.56  fof(f3006,plain,(
% 1.54/0.56    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2)),
% 1.54/0.56    inference(superposition,[],[f34,f2941])).
% 1.54/0.56  fof(f2941,plain,(
% 1.54/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.54/0.56    inference(superposition,[],[f2415,f2228])).
% 1.54/0.56  fof(f2228,plain,(
% 1.54/0.56    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.54/0.56    inference(backward_demodulation,[],[f511,f437])).
% 1.54/0.56  fof(f437,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(superposition,[],[f37,f26])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f16])).
% 1.54/0.56  fof(f16,plain,(
% 1.54/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.56    inference(rectify,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.54/0.56  fof(f511,plain,(
% 1.54/0.56    k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.54/0.56    inference(forward_demodulation,[],[f510,f88])).
% 1.54/0.56  fof(f88,plain,(
% 1.54/0.56    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X4)) )),
% 1.54/0.56    inference(resolution,[],[f32,f69])).
% 1.54/0.56  fof(f69,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f65,f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f13])).
% 1.54/0.56  fof(f13,axiom,(
% 1.54/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.54/0.56  fof(f65,plain,(
% 1.54/0.56    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,X0),X0)) )),
% 1.54/0.56    inference(superposition,[],[f39,f26])).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f27,f31])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f18])).
% 1.54/0.56  fof(f18,plain,(
% 1.54/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.56    inference(ennf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.54/0.56  fof(f510,plain,(
% 1.54/0.56    k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(k1_xboole_0,sK0)),
% 1.54/0.56    inference(forward_demodulation,[],[f498,f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.56  fof(f498,plain,(
% 1.54/0.56    k3_xboole_0(sK0,k1_xboole_0) = k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.54/0.56    inference(superposition,[],[f479,f134])).
% 1.54/0.56  fof(f134,plain,(
% 1.54/0.56    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,X2),k5_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(resolution,[],[f33,f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f21])).
% 1.54/0.56  fof(f21,plain,(
% 1.54/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.54/0.56    inference(nnf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.54/0.56  fof(f479,plain,(
% 1.54/0.56    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))) )),
% 1.54/0.56    inference(superposition,[],[f445,f29])).
% 1.54/0.56  fof(f445,plain,(
% 1.54/0.56    ( ! [X20] : (k3_xboole_0(sK0,k3_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)),X20)) = k3_xboole_0(sK0,X20)) )),
% 1.54/0.56    inference(superposition,[],[f37,f89])).
% 1.54/0.56  fof(f89,plain,(
% 1.54/0.56    sK0 = k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.54/0.56    inference(resolution,[],[f32,f38])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    r1_tarski(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.54/0.56    inference(definition_unfolding,[],[f22,f31])).
% 1.54/0.56  fof(f22,plain,(
% 1.54/0.56    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.54/0.56    inference(cnf_transformation,[],[f20])).
% 1.54/0.56  fof(f20,plain,(
% 1.54/0.56    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 1.54/0.56  fof(f19,plain,(
% 1.54/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f17,plain,(
% 1.54/0.56    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.54/0.56    inference(ennf_transformation,[],[f15])).
% 1.54/0.56  fof(f15,negated_conjecture,(
% 1.54/0.56    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.54/0.56    inference(negated_conjecture,[],[f14])).
% 1.54/0.56  fof(f14,conjecture,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.54/0.56  fof(f2415,plain,(
% 1.54/0.56    ( ! [X0] : (k3_xboole_0(sK0,X0) = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))) )),
% 1.54/0.56    inference(superposition,[],[f37,f2399])).
% 1.54/0.56  fof(f2399,plain,(
% 1.54/0.56    sK0 = k3_xboole_0(sK0,sK1)),
% 1.54/0.56    inference(forward_demodulation,[],[f2398,f89])).
% 1.54/0.56  fof(f2398,plain,(
% 1.54/0.56    k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k3_xboole_0(sK0,sK1)),
% 1.54/0.56    inference(forward_demodulation,[],[f2364,f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f11])).
% 1.54/0.56  fof(f11,axiom,(
% 1.54/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.54/0.56  fof(f2364,plain,(
% 1.54/0.56    k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.54/0.56    inference(superposition,[],[f645,f2228])).
% 1.54/0.56  fof(f645,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 1.54/0.56    inference(forward_demodulation,[],[f40,f37])).
% 1.54/0.56  fof(f40,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f36,f31,f31])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f10])).
% 1.54/0.56  fof(f10,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f21])).
% 1.54/0.56  fof(f4253,plain,(
% 1.54/0.56    ~r1_xboole_0(sK0,sK2)),
% 1.54/0.56    inference(resolution,[],[f4244,f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 1.54/0.56    inference(cnf_transformation,[],[f20])).
% 1.54/0.56  fof(f4244,plain,(
% 1.54/0.56    r1_tarski(sK0,sK1)),
% 1.54/0.56    inference(forward_demodulation,[],[f4231,f205])).
% 1.54/0.56  fof(f205,plain,(
% 1.54/0.56    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.54/0.56    inference(superposition,[],[f201,f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.54/0.56  fof(f201,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.54/0.56    inference(forward_demodulation,[],[f183,f41])).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.54/0.56    inference(superposition,[],[f28,f25])).
% 1.54/0.56  fof(f183,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.54/0.56    inference(superposition,[],[f35,f24])).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.54/0.56  fof(f4231,plain,(
% 1.54/0.56    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)),sK1)),
% 1.54/0.56    inference(superposition,[],[f66,f2440])).
% 1.54/0.56  fof(f2440,plain,(
% 1.54/0.56    k5_xboole_0(sK0,sK1) = k3_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 1.54/0.56    inference(resolution,[],[f2433,f32])).
% 1.54/0.56  fof(f2433,plain,(
% 1.54/0.56    r1_tarski(k5_xboole_0(sK0,sK1),sK1)),
% 1.54/0.56    inference(forward_demodulation,[],[f2418,f28])).
% 1.54/0.56  fof(f2418,plain,(
% 1.54/0.56    r1_tarski(k5_xboole_0(sK1,sK0),sK1)),
% 1.54/0.56    inference(superposition,[],[f66,f2399])).
% 1.54/0.56  fof(f66,plain,(
% 1.54/0.56    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X1,k3_xboole_0(X2,X1)),X1)) )),
% 1.54/0.56    inference(superposition,[],[f39,f29])).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (3513)------------------------------
% 1.54/0.56  % (3513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (3513)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (3513)Memory used [KB]: 3198
% 1.54/0.56  % (3513)Time elapsed: 0.152 s
% 1.54/0.56  % (3513)------------------------------
% 1.54/0.56  % (3513)------------------------------
% 1.54/0.56  % (3500)Success in time 0.195 s
%------------------------------------------------------------------------------
