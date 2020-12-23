%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:20 EST 2020

% Result     : Theorem 4.93s
% Output     : Refutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :   46 (  58 expanded)
%              Number of equality atoms :   45 (  57 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7989,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7918,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).

fof(f7918,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1) ),
    inference(superposition,[],[f26,f5032])).

fof(f5032,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X6,X5) ),
    inference(superposition,[],[f1483,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f1483,plain,(
    ! [X12,X10,X13,X11] : k3_enumset1(X10,X10,X11,X12,X13) = k2_enumset1(X13,X10,X12,X11) ),
    inference(forward_demodulation,[],[f1474,f35])).

fof(f1474,plain,(
    ! [X12,X10,X13,X11] : k3_enumset1(X10,X10,X11,X12,X13) = k3_enumset1(X13,X13,X10,X12,X11) ),
    inference(superposition,[],[f474,f436])).

fof(f436,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(forward_demodulation,[],[f432,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f432,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4) ),
    inference(superposition,[],[f194,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f194,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0) ),
    inference(backward_demodulation,[],[f140,f193])).

fof(f193,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f188,f38])).

fof(f188,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(superposition,[],[f41,f36])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f140,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)) ),
    inference(superposition,[],[f40,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f474,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X3,X4,X0,X2,X1) ),
    inference(forward_demodulation,[],[f451,f96])).

fof(f96,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9) ),
    inference(superposition,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f451,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f145,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f145,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f139,f38])).

fof(f139,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:44:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (24258)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (24255)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (24253)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (24267)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (24256)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (24268)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (24265)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (24269)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (24263)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.52  % (24270)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (24260)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.52  % (24262)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (24266)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (24261)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (24259)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (24254)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.53  % (24257)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.34/0.54  % (24264)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.49/0.56  % (24264)Refutation not found, incomplete strategy% (24264)------------------------------
% 1.49/0.56  % (24264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (24264)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (24264)Memory used [KB]: 10618
% 1.49/0.56  % (24264)Time elapsed: 0.134 s
% 1.49/0.56  % (24264)------------------------------
% 1.49/0.56  % (24264)------------------------------
% 4.93/0.98  % (24256)Refutation found. Thanks to Tanya!
% 4.93/0.98  % SZS status Theorem for theBenchmark
% 4.93/1.00  % SZS output start Proof for theBenchmark
% 4.93/1.00  fof(f7989,plain,(
% 4.93/1.00    $false),
% 4.93/1.00    inference(subsumption_resolution,[],[f7918,f33])).
% 4.93/1.00  fof(f33,plain,(
% 4.93/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f5])).
% 4.93/1.00  fof(f5,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X3,X2,X1)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_enumset1)).
% 4.93/1.00  fof(f7918,plain,(
% 4.93/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK3,sK2,sK1)),
% 4.93/1.00    inference(superposition,[],[f26,f5032])).
% 4.93/1.00  fof(f5032,plain,(
% 4.93/1.00    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X6,X5)) )),
% 4.93/1.00    inference(superposition,[],[f1483,f35])).
% 4.93/1.00  fof(f35,plain,(
% 4.93/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f17])).
% 4.93/1.00  fof(f17,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 4.93/1.00  fof(f1483,plain,(
% 4.93/1.00    ( ! [X12,X10,X13,X11] : (k3_enumset1(X10,X10,X11,X12,X13) = k2_enumset1(X13,X10,X12,X11)) )),
% 4.93/1.00    inference(forward_demodulation,[],[f1474,f35])).
% 4.93/1.00  fof(f1474,plain,(
% 4.93/1.00    ( ! [X12,X10,X13,X11] : (k3_enumset1(X10,X10,X11,X12,X13) = k3_enumset1(X13,X13,X10,X12,X11)) )),
% 4.93/1.00    inference(superposition,[],[f474,f436])).
% 4.93/1.00  fof(f436,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 4.93/1.00    inference(forward_demodulation,[],[f432,f36])).
% 4.93/1.00  fof(f36,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f18])).
% 4.93/1.00  fof(f18,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 4.93/1.00  fof(f432,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k4_enumset1(X0,X1,X2,X3,X4,X4)) )),
% 4.93/1.00    inference(superposition,[],[f194,f38])).
% 4.93/1.00  fof(f38,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f19])).
% 4.93/1.00  fof(f19,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 4.93/1.00  fof(f194,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k4_enumset1(X1,X2,X3,X4,X5,X0)) )),
% 4.93/1.00    inference(backward_demodulation,[],[f140,f193])).
% 4.93/1.00  fof(f193,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 4.93/1.00    inference(forward_demodulation,[],[f188,f38])).
% 4.93/1.00  fof(f188,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 4.93/1.00    inference(superposition,[],[f41,f36])).
% 4.93/1.00  fof(f41,plain,(
% 4.93/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 4.93/1.00    inference(cnf_transformation,[],[f8])).
% 4.93/1.00  fof(f8,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 4.93/1.00  fof(f140,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X1,X2,X3,X4,X5,X0,X0) = k2_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0))) )),
% 4.93/1.00    inference(superposition,[],[f40,f27])).
% 4.93/1.00  fof(f27,plain,(
% 4.93/1.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f14])).
% 4.93/1.00  fof(f14,axiom,(
% 4.93/1.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 4.93/1.00  fof(f40,plain,(
% 4.93/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 4.93/1.00    inference(cnf_transformation,[],[f7])).
% 4.93/1.00  fof(f7,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 4.93/1.00  fof(f474,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X3,X4,X0,X2,X1)) )),
% 4.93/1.00    inference(forward_demodulation,[],[f451,f96])).
% 4.93/1.00  fof(f96,plain,(
% 4.93/1.00    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9)) )),
% 4.93/1.00    inference(superposition,[],[f37,f28])).
% 4.93/1.00  fof(f28,plain,(
% 4.93/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f1])).
% 4.93/1.00  fof(f1,axiom,(
% 4.93/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.93/1.00  fof(f37,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 4.93/1.00    inference(cnf_transformation,[],[f6])).
% 4.93/1.00  fof(f6,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 4.93/1.00  fof(f451,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X2,X1),k2_tarski(X3,X4))) )),
% 4.93/1.00    inference(superposition,[],[f145,f55])).
% 4.93/1.00  fof(f55,plain,(
% 4.93/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 4.93/1.00    inference(superposition,[],[f34,f32])).
% 4.93/1.00  fof(f32,plain,(
% 4.93/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f16])).
% 4.93/1.00  fof(f16,axiom,(
% 4.93/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 4.93/1.00  fof(f34,plain,(
% 4.93/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 4.93/1.00    inference(cnf_transformation,[],[f4])).
% 4.93/1.00  fof(f4,axiom,(
% 4.93/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 4.93/1.00  fof(f145,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 4.93/1.00    inference(forward_demodulation,[],[f139,f38])).
% 4.93/1.00  fof(f139,plain,(
% 4.93/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 4.93/1.00    inference(superposition,[],[f40,f35])).
% 4.93/1.00  fof(f26,plain,(
% 4.93/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 4.93/1.00    inference(cnf_transformation,[],[f25])).
% 4.93/1.00  fof(f25,plain,(
% 4.93/1.00    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 4.93/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).
% 4.93/1.00  fof(f24,plain,(
% 4.93/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 4.93/1.00    introduced(choice_axiom,[])).
% 4.93/1.00  fof(f23,plain,(
% 4.93/1.00    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 4.93/1.00    inference(ennf_transformation,[],[f22])).
% 4.93/1.00  fof(f22,negated_conjecture,(
% 4.93/1.00    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 4.93/1.00    inference(negated_conjecture,[],[f21])).
% 4.93/1.00  fof(f21,conjecture,(
% 4.93/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 4.93/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_enumset1)).
% 4.93/1.00  % SZS output end Proof for theBenchmark
% 4.93/1.00  % (24256)------------------------------
% 4.93/1.00  % (24256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.00  % (24256)Termination reason: Refutation
% 4.93/1.00  
% 4.93/1.00  % (24256)Memory used [KB]: 10362
% 4.93/1.00  % (24256)Time elapsed: 0.541 s
% 4.93/1.00  % (24256)------------------------------
% 4.93/1.00  % (24256)------------------------------
% 4.93/1.00  % (24252)Success in time 0.638 s
%------------------------------------------------------------------------------
