%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:17 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 189 expanded)
%              Number of leaves         :   11 (  63 expanded)
%              Depth                    :   14
%              Number of atoms          :   51 ( 190 expanded)
%              Number of equality atoms :   50 ( 189 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6122,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19,f6101])).

fof(f6101,plain,(
    ! [X28,X26,X27,X25] : k2_enumset1(X25,X26,X27,X28) = k2_enumset1(X25,X28,X26,X27) ),
    inference(superposition,[],[f2768,f2767])).

fof(f2767,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3) ),
    inference(backward_demodulation,[],[f234,f2766])).

fof(f2766,plain,(
    ! [X6,X8,X7,X5] : k2_enumset1(X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8)) ),
    inference(forward_demodulation,[],[f2765,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f62,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f2765,plain,(
    ! [X6,X8,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X8)) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8)) ),
    inference(forward_demodulation,[],[f2740,f757])).

fof(f757,plain,(
    ! [X6,X8,X7,X5] : k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8)) = k4_enumset1(X5,X5,X5,X6,X7,X8) ),
    inference(superposition,[],[f29,f54])).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(superposition,[],[f52,f25])).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[],[f26,f20])).

fof(f20,plain,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f2740,plain,(
    ! [X6,X8,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X8)) = k4_enumset1(X5,X5,X5,X6,X7,X8) ),
    inference(superposition,[],[f30,f97])).

fof(f97,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k3_enumset1(X3,X3,X3,X4,X5) ),
    inference(backward_demodulation,[],[f78,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f90,f25])).

fof(f90,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f64,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f78,plain,(
    ! [X4,X5,X3] : k3_enumset1(X3,X3,X3,X4,X5) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5)) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(forward_demodulation,[],[f69,f21])).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(superposition,[],[f66,f25])).

fof(f66,plain,(
    ! [X4,X3] : k2_enumset1(X3,X3,X3,X4) = k2_xboole_0(k1_tarski(X3),k1_tarski(X4)) ),
    inference(superposition,[],[f63,f26])).

fof(f63,plain,(
    ! [X4,X5] : k3_enumset1(X4,X4,X4,X4,X5) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5)) ),
    inference(superposition,[],[f27,f52])).

fof(f73,plain,(
    ! [X4,X5,X3] : k3_enumset1(X3,X3,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5)) ),
    inference(superposition,[],[f27,f66])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f234,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f220,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(superposition,[],[f54,f21])).

fof(f220,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X3,X4,X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f28,f25])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(f2768,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X1,X2,X3) = k2_enumset1(X0,X3,X1,X2) ),
    inference(backward_demodulation,[],[f288,f2766])).

fof(f288,plain,(
    ! [X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X3,X1,X2)) ),
    inference(superposition,[],[f237,f56])).

fof(f237,plain,(
    ! [X10,X8,X7,X11,X9] : k4_enumset1(X10,X11,X7,X7,X8,X9) = k2_xboole_0(k2_tarski(X10,X11),k1_enumset1(X9,X7,X8)) ),
    inference(superposition,[],[f220,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X3,X1)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X3,X1) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (11857)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (11867)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (11863)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (11869)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (11853)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (11864)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (11858)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (11854)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (11859)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (11862)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (11855)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (11856)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (11870)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (11861)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (11866)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  % (11864)Refutation not found, incomplete strategy% (11864)------------------------------
% 0.21/0.53  % (11864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (11864)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (11864)Memory used [KB]: 10490
% 0.21/0.53  % (11864)Time elapsed: 0.112 s
% 0.21/0.53  % (11864)------------------------------
% 0.21/0.53  % (11864)------------------------------
% 0.21/0.54  % (11868)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.55  % (11860)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.53/0.56  % (11865)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 2.42/0.71  % (11869)Refutation found. Thanks to Tanya!
% 2.42/0.71  % SZS status Theorem for theBenchmark
% 2.42/0.71  % SZS output start Proof for theBenchmark
% 2.42/0.71  fof(f6122,plain,(
% 2.42/0.71    $false),
% 2.42/0.71    inference(subsumption_resolution,[],[f19,f6101])).
% 2.42/0.71  fof(f6101,plain,(
% 2.42/0.71    ( ! [X28,X26,X27,X25] : (k2_enumset1(X25,X26,X27,X28) = k2_enumset1(X25,X28,X26,X27)) )),
% 2.42/0.71    inference(superposition,[],[f2768,f2767])).
% 2.42/0.71  fof(f2767,plain,(
% 2.42/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X1,X1,X2,X3)) )),
% 2.42/0.71    inference(backward_demodulation,[],[f234,f2766])).
% 2.42/0.71  fof(f2766,plain,(
% 2.42/0.71    ( ! [X6,X8,X7,X5] : (k2_enumset1(X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8))) )),
% 2.42/0.71    inference(forward_demodulation,[],[f2765,f64])).
% 2.42/0.71  fof(f64,plain,(
% 2.42/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.42/0.71    inference(forward_demodulation,[],[f62,f26])).
% 2.42/0.71  fof(f26,plain,(
% 2.42/0.71    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.42/0.71    inference(cnf_transformation,[],[f12])).
% 2.42/0.71  fof(f12,axiom,(
% 2.42/0.71    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.42/0.71  fof(f62,plain,(
% 2.42/0.71    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 2.42/0.71    inference(superposition,[],[f27,f25])).
% 2.42/0.71  fof(f25,plain,(
% 2.42/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.42/0.71    inference(cnf_transformation,[],[f11])).
% 2.42/0.71  fof(f11,axiom,(
% 2.42/0.71    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.42/0.71  fof(f27,plain,(
% 2.42/0.71    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 2.42/0.71    inference(cnf_transformation,[],[f5])).
% 2.42/0.71  fof(f5,axiom,(
% 2.42/0.71    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 2.42/0.71  fof(f2765,plain,(
% 2.42/0.71    ( ! [X6,X8,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X8)) = k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8))) )),
% 2.42/0.71    inference(forward_demodulation,[],[f2740,f757])).
% 2.42/0.71  fof(f757,plain,(
% 2.42/0.71    ( ! [X6,X8,X7,X5] : (k2_xboole_0(k1_tarski(X5),k1_enumset1(X6,X7,X8)) = k4_enumset1(X5,X5,X5,X6,X7,X8)) )),
% 2.42/0.71    inference(superposition,[],[f29,f54])).
% 2.42/0.71  fof(f54,plain,(
% 2.42/0.71    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.42/0.71    inference(superposition,[],[f52,f25])).
% 2.42/0.71  fof(f52,plain,(
% 2.42/0.71    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.42/0.71    inference(superposition,[],[f26,f20])).
% 2.42/0.71  fof(f20,plain,(
% 2.42/0.71    ( ! [X0] : (k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 2.42/0.71    inference(cnf_transformation,[],[f13])).
% 2.42/0.71  fof(f13,axiom,(
% 2.42/0.71    ! [X0] : k3_enumset1(X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_enumset1)).
% 2.42/0.71  fof(f29,plain,(
% 2.42/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 2.42/0.71    inference(cnf_transformation,[],[f3])).
% 2.42/0.71  fof(f3,axiom,(
% 2.42/0.71    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 2.42/0.71  fof(f2740,plain,(
% 2.42/0.71    ( ! [X6,X8,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X8)) = k4_enumset1(X5,X5,X5,X6,X7,X8)) )),
% 2.42/0.71    inference(superposition,[],[f30,f97])).
% 2.42/0.71  fof(f97,plain,(
% 2.42/0.71    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k3_enumset1(X3,X3,X3,X4,X5)) )),
% 2.42/0.71    inference(backward_demodulation,[],[f78,f96])).
% 2.42/0.71  fof(f96,plain,(
% 2.42/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.42/0.71    inference(forward_demodulation,[],[f90,f25])).
% 2.42/0.71  fof(f90,plain,(
% 2.42/0.71    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 2.42/0.71    inference(superposition,[],[f64,f21])).
% 2.42/0.71  fof(f21,plain,(
% 2.42/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.42/0.71    inference(cnf_transformation,[],[f10])).
% 2.42/0.71  fof(f10,axiom,(
% 2.42/0.71    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.42/0.71  fof(f78,plain,(
% 2.42/0.71    ( ! [X4,X5,X3] : (k3_enumset1(X3,X3,X3,X4,X5) = k2_xboole_0(k2_tarski(X3,X4),k1_tarski(X5))) )),
% 2.42/0.71    inference(forward_demodulation,[],[f73,f74])).
% 2.42/0.71  fof(f74,plain,(
% 2.42/0.71    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.42/0.71    inference(forward_demodulation,[],[f69,f21])).
% 2.42/0.71  fof(f69,plain,(
% 2.42/0.71    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.42/0.71    inference(superposition,[],[f66,f25])).
% 2.42/0.71  fof(f66,plain,(
% 2.42/0.71    ( ! [X4,X3] : (k2_enumset1(X3,X3,X3,X4) = k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) )),
% 2.42/0.71    inference(superposition,[],[f63,f26])).
% 2.42/0.71  fof(f63,plain,(
% 2.42/0.71    ( ! [X4,X5] : (k3_enumset1(X4,X4,X4,X4,X5) = k2_xboole_0(k1_tarski(X4),k1_tarski(X5))) )),
% 2.42/0.71    inference(superposition,[],[f27,f52])).
% 2.42/0.71  fof(f73,plain,(
% 2.42/0.71    ( ! [X4,X5,X3] : (k3_enumset1(X3,X3,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5))) )),
% 2.42/0.71    inference(superposition,[],[f27,f66])).
% 2.42/0.71  fof(f30,plain,(
% 2.42/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 2.42/0.71    inference(cnf_transformation,[],[f7])).
% 2.42/0.71  fof(f7,axiom,(
% 2.42/0.71    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 2.42/0.71  fof(f234,plain,(
% 2.42/0.71    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 2.42/0.71    inference(superposition,[],[f220,f56])).
% 2.42/0.71  fof(f56,plain,(
% 2.42/0.71    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.42/0.71    inference(superposition,[],[f54,f21])).
% 2.42/0.71  fof(f220,plain,(
% 2.42/0.71    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X3,X4,X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X3,X4),k1_enumset1(X0,X1,X2))) )),
% 2.42/0.71    inference(superposition,[],[f28,f25])).
% 2.42/0.71  fof(f28,plain,(
% 2.42/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 2.42/0.71    inference(cnf_transformation,[],[f6])).
% 2.42/0.71  fof(f6,axiom,(
% 2.42/0.71    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).
% 2.42/0.71  fof(f2768,plain,(
% 2.42/0.71    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X1,X2,X3) = k2_enumset1(X0,X3,X1,X2)) )),
% 2.42/0.71    inference(backward_demodulation,[],[f288,f2766])).
% 2.42/0.71  fof(f288,plain,(
% 2.42/0.71    ( ! [X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X3,X1,X2))) )),
% 2.42/0.71    inference(superposition,[],[f237,f56])).
% 2.42/0.71  fof(f237,plain,(
% 2.42/0.71    ( ! [X10,X8,X7,X11,X9] : (k4_enumset1(X10,X11,X7,X7,X8,X9) = k2_xboole_0(k2_tarski(X10,X11),k1_enumset1(X9,X7,X8))) )),
% 2.42/0.71    inference(superposition,[],[f220,f24])).
% 2.42/0.71  fof(f24,plain,(
% 2.42/0.71    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 2.42/0.71    inference(cnf_transformation,[],[f4])).
% 2.42/0.71  fof(f4,axiom,(
% 2.42/0.71    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 2.42/0.71  fof(f19,plain,(
% 2.42/0.71    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)),
% 2.42/0.71    inference(cnf_transformation,[],[f18])).
% 2.42/0.71  fof(f18,plain,(
% 2.42/0.71    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)),
% 2.42/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 2.42/0.71  fof(f17,plain,(
% 2.42/0.71    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X3,X1) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK3,sK1)),
% 2.42/0.71    introduced(choice_axiom,[])).
% 2.42/0.71  fof(f16,plain,(
% 2.42/0.71    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X3,X1)),
% 2.42/0.71    inference(ennf_transformation,[],[f15])).
% 2.42/0.71  fof(f15,negated_conjecture,(
% 2.42/0.71    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 2.42/0.71    inference(negated_conjecture,[],[f14])).
% 2.42/0.71  fof(f14,conjecture,(
% 2.42/0.71    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 2.42/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 2.42/0.71  % SZS output end Proof for theBenchmark
% 2.42/0.71  % (11869)------------------------------
% 2.42/0.71  % (11869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.71  % (11869)Termination reason: Refutation
% 2.42/0.71  
% 2.42/0.71  % (11869)Memory used [KB]: 8315
% 2.42/0.71  % (11869)Time elapsed: 0.271 s
% 2.42/0.71  % (11869)------------------------------
% 2.42/0.71  % (11869)------------------------------
% 2.42/0.71  % (11852)Success in time 0.345 s
%------------------------------------------------------------------------------
