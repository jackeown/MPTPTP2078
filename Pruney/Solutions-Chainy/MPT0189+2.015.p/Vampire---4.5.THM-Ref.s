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
% DateTime   : Thu Dec  3 12:34:20 EST 2020

% Result     : Theorem 5.21s
% Output     : Refutation 5.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  60 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :   47 (  61 expanded)
%              Number of equality atoms :   46 (  60 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8295,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8222,f63])).

fof(f63,plain,(
    ! [X17,X15,X18,X16] : k2_enumset1(X15,X17,X18,X16) = k2_enumset1(X15,X16,X18,X17) ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f8222,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(superposition,[],[f26,f5888])).

fof(f5888,plain,(
    ! [X19,X17,X18,X16] : k2_enumset1(X16,X17,X18,X19) = k2_enumset1(X19,X16,X18,X17) ),
    inference(superposition,[],[f1488,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1488,plain,(
    ! [X12,X10,X13,X11] : k3_enumset1(X10,X10,X11,X12,X13) = k2_enumset1(X13,X10,X12,X11) ),
    inference(forward_demodulation,[],[f1479,f35])).

fof(f1479,plain,(
    ! [X12,X10,X13,X11] : k3_enumset1(X10,X10,X11,X12,X13) = k3_enumset1(X13,X13,X10,X12,X11) ),
    inference(superposition,[],[f480,f442])).

fof(f442,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(forward_demodulation,[],[f438,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f438,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f200,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f200,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0) ),
    inference(backward_demodulation,[],[f148,f199])).

fof(f199,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f194,f38])).

fof(f194,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f41,f36])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f148,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    inference(superposition,[],[f40,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f480,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X3,X4,X0,X2,X1) ),
    inference(forward_demodulation,[],[f457,f106])).

fof(f106,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9) ),
    inference(superposition,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f457,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f153,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f153,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f147,f38])).

fof(f147,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f40,f35])).

fof(f26,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:08:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (10369)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.45  % (10381)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (10380)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (10383)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (10372)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (10374)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (10371)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (10368)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (10378)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (10373)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (10367)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (10375)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (10379)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (10370)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (10379)Refutation not found, incomplete strategy% (10379)------------------------------
% 0.21/0.51  % (10379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10379)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10379)Memory used [KB]: 10618
% 0.21/0.51  % (10379)Time elapsed: 0.089 s
% 0.21/0.51  % (10379)------------------------------
% 0.21/0.51  % (10379)------------------------------
% 0.21/0.52  % (10382)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.53  % (10376)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.53  % (10385)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.54  % (10384)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.21/1.01  % (10370)Refutation found. Thanks to Tanya!
% 5.21/1.01  % SZS status Theorem for theBenchmark
% 5.21/1.02  % SZS output start Proof for theBenchmark
% 5.21/1.02  fof(f8295,plain,(
% 5.21/1.02    $false),
% 5.21/1.02    inference(subsumption_resolution,[],[f8222,f63])).
% 5.21/1.02  fof(f63,plain,(
% 5.21/1.02    ( ! [X17,X15,X18,X16] : (k2_enumset1(X15,X17,X18,X16) = k2_enumset1(X15,X16,X18,X17)) )),
% 5.21/1.02    inference(superposition,[],[f34,f33])).
% 5.21/1.02  fof(f33,plain,(
% 5.21/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f5])).
% 5.21/1.02  fof(f5,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 5.21/1.02  fof(f34,plain,(
% 5.21/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f4])).
% 5.21/1.02  fof(f4,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 5.21/1.02  fof(f8222,plain,(
% 5.21/1.02    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 5.21/1.02    inference(superposition,[],[f26,f5888])).
% 5.21/1.02  fof(f5888,plain,(
% 5.21/1.02    ( ! [X19,X17,X18,X16] : (k2_enumset1(X16,X17,X18,X19) = k2_enumset1(X19,X16,X18,X17)) )),
% 5.21/1.02    inference(superposition,[],[f1488,f35])).
% 5.21/1.02  fof(f35,plain,(
% 5.21/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f17])).
% 5.21/1.02  fof(f17,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 5.21/1.02  fof(f1488,plain,(
% 5.21/1.02    ( ! [X12,X10,X13,X11] : (k3_enumset1(X10,X10,X11,X12,X13) = k2_enumset1(X13,X10,X12,X11)) )),
% 5.21/1.02    inference(forward_demodulation,[],[f1479,f35])).
% 5.21/1.02  fof(f1479,plain,(
% 5.21/1.02    ( ! [X12,X10,X13,X11] : (k3_enumset1(X10,X10,X11,X12,X13) = k3_enumset1(X13,X13,X10,X12,X11)) )),
% 5.21/1.02    inference(superposition,[],[f480,f442])).
% 5.21/1.02  fof(f442,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 5.21/1.02    inference(forward_demodulation,[],[f438,f36])).
% 5.21/1.02  fof(f36,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f18])).
% 5.21/1.02  fof(f18,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 5.21/1.02  fof(f438,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 5.21/1.02    inference(superposition,[],[f200,f38])).
% 5.21/1.02  fof(f38,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f19])).
% 5.21/1.02  fof(f19,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 5.21/1.02  fof(f200,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) )),
% 5.21/1.02    inference(backward_demodulation,[],[f148,f199])).
% 5.21/1.02  fof(f199,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 5.21/1.02    inference(forward_demodulation,[],[f194,f38])).
% 5.21/1.02  fof(f194,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 5.21/1.02    inference(superposition,[],[f41,f36])).
% 5.21/1.02  fof(f41,plain,(
% 5.21/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 5.21/1.02    inference(cnf_transformation,[],[f8])).
% 5.21/1.02  fof(f8,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 5.21/1.02  fof(f148,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) )),
% 5.21/1.02    inference(superposition,[],[f40,f27])).
% 5.21/1.02  fof(f27,plain,(
% 5.21/1.02    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f14])).
% 5.21/1.02  fof(f14,axiom,(
% 5.21/1.02    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 5.21/1.02  fof(f40,plain,(
% 5.21/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 5.21/1.02    inference(cnf_transformation,[],[f7])).
% 5.21/1.02  fof(f7,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 5.21/1.02  fof(f480,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X3,X4,X0,X2,X1)) )),
% 5.21/1.02    inference(forward_demodulation,[],[f457,f106])).
% 5.21/1.02  fof(f106,plain,(
% 5.21/1.02    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9)) )),
% 5.21/1.02    inference(superposition,[],[f37,f28])).
% 5.21/1.02  fof(f28,plain,(
% 5.21/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f1])).
% 5.21/1.02  fof(f1,axiom,(
% 5.21/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 5.21/1.02  fof(f37,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 5.21/1.02    inference(cnf_transformation,[],[f6])).
% 5.21/1.02  fof(f6,axiom,(
% 5.21/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 5.21/1.02  fof(f457,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) )),
% 5.21/1.02    inference(superposition,[],[f153,f61])).
% 5.21/1.02  fof(f61,plain,(
% 5.21/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 5.21/1.02    inference(superposition,[],[f34,f32])).
% 5.21/1.02  fof(f32,plain,(
% 5.21/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 5.21/1.02    inference(cnf_transformation,[],[f16])).
% 5.21/1.02  fof(f16,axiom,(
% 5.21/1.02    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 5.21/1.02  fof(f153,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 5.21/1.02    inference(forward_demodulation,[],[f147,f38])).
% 5.21/1.02  fof(f147,plain,(
% 5.21/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 5.21/1.02    inference(superposition,[],[f40,f35])).
% 5.21/1.02  fof(f26,plain,(
% 5.21/1.02    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 5.21/1.02    inference(cnf_transformation,[],[f25])).
% 5.21/1.02  fof(f25,plain,(
% 5.21/1.02    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 5.21/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).
% 5.21/1.02  fof(f24,plain,(
% 5.21/1.02    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 5.21/1.02    introduced(choice_axiom,[])).
% 5.21/1.02  fof(f23,plain,(
% 5.21/1.02    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 5.21/1.02    inference(ennf_transformation,[],[f22])).
% 5.21/1.02  fof(f22,negated_conjecture,(
% 5.21/1.02    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 5.21/1.02    inference(negated_conjecture,[],[f21])).
% 5.21/1.02  fof(f21,conjecture,(
% 5.21/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 5.21/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 5.21/1.02  % SZS output end Proof for theBenchmark
% 5.21/1.02  % (10370)------------------------------
% 5.21/1.02  % (10370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.21/1.02  % (10370)Termination reason: Refutation
% 5.21/1.02  
% 5.21/1.02  % (10370)Memory used [KB]: 10362
% 5.21/1.02  % (10370)Time elapsed: 0.591 s
% 5.21/1.02  % (10370)------------------------------
% 5.21/1.02  % (10370)------------------------------
% 5.21/1.03  % (10364)Success in time 0.667 s
%------------------------------------------------------------------------------
