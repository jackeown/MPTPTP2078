%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 135 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   16
%              Number of atoms          :  120 ( 234 expanded)
%              Number of equality atoms :   56 (  98 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f414,f710])).

fof(f710,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f709])).

fof(f709,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f424,f694])).

fof(f694,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f493,f76])).

fof(f76,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f493,plain,
    ( ! [X3] : k3_xboole_0(sK0,X3) = k4_xboole_0(sK0,k4_xboole_0(sK1,X3))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f486,f292])).

fof(f292,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f277,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f277,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f253,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f28,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f253,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f38,f128])).

fof(f128,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f119,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f27,f91])).

fof(f91,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f85,f25])).

fof(f85,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f31,f74])).

fof(f74,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f37,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f119,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f32,f94])).

fof(f94,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f30,f91])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f486,plain,
    ( ! [X3] : k5_xboole_0(sK0,k4_xboole_0(sK0,X3)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X3))
    | ~ spl3_1 ),
    inference(superposition,[],[f32,f425])).

fof(f425,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(sK1,X0))
    | ~ spl3_1 ),
    inference(superposition,[],[f39,f423])).

fof(f423,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f43,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f424,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f48,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f414,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f71,f412])).

fof(f412,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f411,f61])).

fof(f61,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f33,f50])).

fof(f411,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f403,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f403,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f319,f75])).

fof(f75,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(resolution,[],[f37,f26])).

fof(f319,plain,(
    ! [X23] : k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X23)) = k4_xboole_0(sK0,X23) ),
    inference(superposition,[],[f39,f59])).

fof(f59,plain,(
    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f33,f23])).

fof(f71,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(resolution,[],[f36,f44])).

fof(f44,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f46,f42])).

fof(f24,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (23317)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (23310)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (23322)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (23325)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (23311)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (23312)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (23315)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (23314)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (23326)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (23321)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (23320)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (23319)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (23318)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (23313)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (23324)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (23326)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f711,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f49,f414,f710])).
% 0.21/0.51  fof(f710,plain,(
% 0.21/0.51    ~spl3_1 | spl3_2),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f709])).
% 0.21/0.51  fof(f709,plain,(
% 0.21/0.51    $false | (~spl3_1 | spl3_2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f424,f694])).
% 0.21/0.51  fof(f694,plain,(
% 0.21/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_1),
% 0.21/0.51    inference(superposition,[],[f493,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.51    inference(resolution,[],[f37,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.51  fof(f493,plain,(
% 0.21/0.51    ( ! [X3] : (k3_xboole_0(sK0,X3) = k4_xboole_0(sK0,k4_xboole_0(sK1,X3))) ) | ~spl3_1),
% 0.21/0.51    inference(forward_demodulation,[],[f486,f292])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 0.21/0.51    inference(superposition,[],[f277,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.51    inference(forward_demodulation,[],[f253,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.51    inference(superposition,[],[f28,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(superposition,[],[f38,f128])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f119,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.21/0.51    inference(superposition,[],[f27,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.21/0.51    inference(forward_demodulation,[],[f85,f25])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f31,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.51    inference(resolution,[],[f37,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f26,f27])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f32,f94])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.51    inference(superposition,[],[f30,f91])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.51  fof(f486,plain,(
% 0.21/0.51    ( ! [X3] : (k5_xboole_0(sK0,k4_xboole_0(sK0,X3)) = k4_xboole_0(sK0,k4_xboole_0(sK1,X3))) ) | ~spl3_1),
% 0.21/0.51    inference(superposition,[],[f32,f425])).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(sK1,X0))) ) | ~spl3_1),
% 0.21/0.51    inference(superposition,[],[f39,f423])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.51    inference(resolution,[],[f43,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_2),
% 0.21/0.51    inference(resolution,[],[f48,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~r1_xboole_0(sK0,sK2) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f414,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f413])).
% 0.21/0.51  fof(f413,plain,(
% 0.21/0.51    $false | spl3_1),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f412])).
% 0.21/0.51  fof(f412,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.51    inference(forward_demodulation,[],[f411,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.51    inference(resolution,[],[f33,f50])).
% 0.21/0.51  fof(f411,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f403,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f319,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 0.21/0.51    inference(resolution,[],[f37,f26])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    ( ! [X23] : (k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X23)) = k4_xboole_0(sK0,X23)) )),
% 0.21/0.51    inference(superposition,[],[f39,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.51    inference(resolution,[],[f33,f23])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_1),
% 0.21/0.51    inference(resolution,[],[f36,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f42])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f46,f42])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (23326)------------------------------
% 0.21/0.51  % (23326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23326)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (23326)Memory used [KB]: 6652
% 0.21/0.51  % (23326)Time elapsed: 0.083 s
% 0.21/0.51  % (23326)------------------------------
% 0.21/0.51  % (23326)------------------------------
% 0.21/0.51  % (23316)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (23309)Success in time 0.154 s
%------------------------------------------------------------------------------
