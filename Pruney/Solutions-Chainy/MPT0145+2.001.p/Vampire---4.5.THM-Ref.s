%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:19 EST 2020

% Result     : Theorem 29.32s
% Output     : Refutation 29.32s
% Verified   : 
% Statistics : Number of formulae       :   29 (  39 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  40 expanded)
%              Number of equality atoms :   29 (  39 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18865,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18862,f18386])).

fof(f18386,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X4,X5,X6,X0,X1,X2,X3) = k5_enumset1(X3,X4,X5,X6,X0,X1,X2) ),
    inference(superposition,[],[f1122,f1122])).

fof(f1122,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k5_enumset1(X11,X12,X13,X7,X8,X9,X10) ),
    inference(superposition,[],[f351,f30])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).

fof(f351,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9)) ),
    inference(superposition,[],[f29,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).

fof(f18862,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK6,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(superposition,[],[f31,f520])).

fof(f520,plain,(
    ! [X28,X26,X24,X23,X29,X27,X25] : k2_xboole_0(k1_tarski(X29),k4_enumset1(X23,X24,X25,X26,X27,X28)) = k5_enumset1(X29,X23,X24,X25,X26,X27,X28) ),
    inference(forward_demodulation,[],[f480,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(f480,plain,(
    ! [X28,X26,X24,X23,X29,X27,X25] : k2_xboole_0(k2_tarski(X29,X23),k3_enumset1(X24,X25,X26,X27,X28)) = k2_xboole_0(k1_tarski(X29),k4_enumset1(X23,X24,X25,X26,X27,X28)) ),
    inference(superposition,[],[f52,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f52,plain,(
    ! [X10,X11,X9] : k2_xboole_0(k1_tarski(X9),k2_xboole_0(k1_tarski(X10),X11)) = k2_xboole_0(k2_tarski(X9,X10),X11) ),
    inference(superposition,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f31,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(superposition,[],[f18,f19])).

fof(f18,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (2501)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (2500)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (2510)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (2513)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (2503)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (2509)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (2504)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (2496)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (2497)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (2511)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (2506)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (2495)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (2499)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (2507)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (2508)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (2508)Refutation not found, incomplete strategy% (2508)------------------------------
% 0.20/0.50  % (2508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (2508)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (2508)Memory used [KB]: 10618
% 0.20/0.50  % (2508)Time elapsed: 0.094 s
% 0.20/0.50  % (2508)------------------------------
% 0.20/0.50  % (2508)------------------------------
% 0.20/0.50  % (2505)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (2514)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (2512)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.27/1.05  % (2500)Time limit reached!
% 5.27/1.05  % (2500)------------------------------
% 5.27/1.05  % (2500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.27/1.05  % (2500)Termination reason: Time limit
% 5.27/1.05  % (2500)Termination phase: Saturation
% 5.27/1.05  
% 5.27/1.05  % (2500)Memory used [KB]: 14711
% 5.27/1.05  % (2500)Time elapsed: 0.600 s
% 5.27/1.05  % (2500)------------------------------
% 5.27/1.05  % (2500)------------------------------
% 12.44/1.93  % (2503)Time limit reached!
% 12.44/1.93  % (2503)------------------------------
% 12.44/1.93  % (2503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.44/1.93  % (2503)Termination reason: Time limit
% 12.44/1.93  % (2503)Termination phase: Saturation
% 12.44/1.93  
% 12.44/1.93  % (2503)Memory used [KB]: 25713
% 12.44/1.93  % (2503)Time elapsed: 1.500 s
% 12.44/1.93  % (2503)------------------------------
% 12.44/1.93  % (2503)------------------------------
% 13.09/2.05  % (2501)Time limit reached!
% 13.09/2.05  % (2501)------------------------------
% 13.09/2.05  % (2501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.09/2.05  % (2501)Termination reason: Time limit
% 13.09/2.05  
% 13.09/2.05  % (2501)Memory used [KB]: 62429
% 13.09/2.05  % (2501)Time elapsed: 1.611 s
% 13.09/2.05  % (2501)------------------------------
% 13.09/2.05  % (2501)------------------------------
% 15.59/2.31  % (2497)Time limit reached!
% 15.59/2.31  % (2497)------------------------------
% 15.59/2.31  % (2497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.59/2.31  % (2497)Termination reason: Time limit
% 15.59/2.31  
% 15.59/2.31  % (2497)Memory used [KB]: 23155
% 15.59/2.31  % (2497)Time elapsed: 1.901 s
% 15.59/2.31  % (2497)------------------------------
% 15.59/2.31  % (2497)------------------------------
% 17.91/2.60  % (2509)Time limit reached!
% 17.91/2.60  % (2509)------------------------------
% 17.91/2.60  % (2509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.91/2.60  % (2509)Termination reason: Time limit
% 17.91/2.60  % (2509)Termination phase: Saturation
% 17.91/2.60  
% 17.91/2.60  % (2509)Memory used [KB]: 30191
% 17.91/2.60  % (2509)Time elapsed: 2.200 s
% 17.91/2.60  % (2509)------------------------------
% 17.91/2.60  % (2509)------------------------------
% 29.32/4.05  % (2499)Refutation found. Thanks to Tanya!
% 29.32/4.05  % SZS status Theorem for theBenchmark
% 29.32/4.05  % SZS output start Proof for theBenchmark
% 29.32/4.05  fof(f18865,plain,(
% 29.32/4.05    $false),
% 29.32/4.05    inference(subsumption_resolution,[],[f18862,f18386])).
% 29.32/4.05  fof(f18386,plain,(
% 29.32/4.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X4,X5,X6,X0,X1,X2,X3) = k5_enumset1(X3,X4,X5,X6,X0,X1,X2)) )),
% 29.32/4.05    inference(superposition,[],[f1122,f1122])).
% 29.32/4.05  fof(f1122,plain,(
% 29.32/4.05    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k5_enumset1(X11,X12,X13,X7,X8,X9,X10)) )),
% 29.32/4.05    inference(superposition,[],[f351,f30])).
% 29.32/4.05  fof(f30,plain,(
% 29.32/4.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 29.32/4.05    inference(cnf_transformation,[],[f5])).
% 29.32/4.05  fof(f5,axiom,(
% 29.32/4.05    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_enumset1)).
% 29.32/4.05  fof(f351,plain,(
% 29.32/4.05    ( ! [X12,X10,X8,X7,X13,X11,X9] : (k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k2_enumset1(X10,X11,X12,X13),k1_enumset1(X7,X8,X9))) )),
% 29.32/4.05    inference(superposition,[],[f29,f19])).
% 29.32/4.05  fof(f19,plain,(
% 29.32/4.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 29.32/4.05    inference(cnf_transformation,[],[f1])).
% 29.32/4.05  fof(f1,axiom,(
% 29.32/4.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 29.32/4.05  fof(f29,plain,(
% 29.32/4.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 29.32/4.05    inference(cnf_transformation,[],[f12])).
% 29.32/4.05  fof(f12,axiom,(
% 29.32/4.05    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_enumset1)).
% 29.32/4.05  fof(f18862,plain,(
% 29.32/4.05    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK6,sK0,sK1,sK2,sK3,sK4,sK5)),
% 29.32/4.05    inference(superposition,[],[f31,f520])).
% 29.32/4.05  fof(f520,plain,(
% 29.32/4.05    ( ! [X28,X26,X24,X23,X29,X27,X25] : (k2_xboole_0(k1_tarski(X29),k4_enumset1(X23,X24,X25,X26,X27,X28)) = k5_enumset1(X29,X23,X24,X25,X26,X27,X28)) )),
% 29.32/4.05    inference(forward_demodulation,[],[f480,f28])).
% 29.32/4.05  fof(f28,plain,(
% 29.32/4.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 29.32/4.05    inference(cnf_transformation,[],[f11])).
% 29.32/4.05  fof(f11,axiom,(
% 29.32/4.05    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 29.32/4.05  fof(f480,plain,(
% 29.32/4.05    ( ! [X28,X26,X24,X23,X29,X27,X25] : (k2_xboole_0(k2_tarski(X29,X23),k3_enumset1(X24,X25,X26,X27,X28)) = k2_xboole_0(k1_tarski(X29),k4_enumset1(X23,X24,X25,X26,X27,X28))) )),
% 29.32/4.05    inference(superposition,[],[f52,f27])).
% 29.32/4.05  fof(f27,plain,(
% 29.32/4.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 29.32/4.05    inference(cnf_transformation,[],[f10])).
% 29.32/4.05  fof(f10,axiom,(
% 29.32/4.05    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 29.32/4.05  fof(f52,plain,(
% 29.32/4.05    ( ! [X10,X11,X9] : (k2_xboole_0(k1_tarski(X9),k2_xboole_0(k1_tarski(X10),X11)) = k2_xboole_0(k2_tarski(X9,X10),X11)) )),
% 29.32/4.05    inference(superposition,[],[f24,f21])).
% 29.32/4.05  fof(f21,plain,(
% 29.32/4.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 29.32/4.05    inference(cnf_transformation,[],[f6])).
% 29.32/4.05  fof(f6,axiom,(
% 29.32/4.05    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 29.32/4.05  fof(f24,plain,(
% 29.32/4.05    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 29.32/4.05    inference(cnf_transformation,[],[f3])).
% 29.32/4.05  fof(f3,axiom,(
% 29.32/4.05    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 29.32/4.05  fof(f31,plain,(
% 29.32/4.05    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK6),k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 29.32/4.05    inference(superposition,[],[f18,f19])).
% 29.32/4.05  fof(f18,plain,(
% 29.32/4.05    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 29.32/4.05    inference(cnf_transformation,[],[f17])).
% 29.32/4.05  fof(f17,plain,(
% 29.32/4.05    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 29.32/4.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f15,f16])).
% 29.32/4.05  fof(f16,plain,(
% 29.32/4.05    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5),k1_tarski(sK6))),
% 29.32/4.05    introduced(choice_axiom,[])).
% 29.32/4.05  fof(f15,plain,(
% 29.32/4.05    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 29.32/4.05    inference(ennf_transformation,[],[f14])).
% 29.32/4.05  fof(f14,negated_conjecture,(
% 29.32/4.05    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 29.32/4.05    inference(negated_conjecture,[],[f13])).
% 29.32/4.05  fof(f13,conjecture,(
% 29.32/4.05    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 29.32/4.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 29.32/4.05  % SZS output end Proof for theBenchmark
% 29.32/4.05  % (2499)------------------------------
% 29.32/4.05  % (2499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 29.32/4.05  % (2499)Termination reason: Refutation
% 29.32/4.05  
% 29.32/4.05  % (2499)Memory used [KB]: 112450
% 29.32/4.05  % (2499)Time elapsed: 3.651 s
% 29.32/4.05  % (2499)------------------------------
% 29.32/4.05  % (2499)------------------------------
% 29.32/4.06  % (2494)Success in time 3.705 s
%------------------------------------------------------------------------------
