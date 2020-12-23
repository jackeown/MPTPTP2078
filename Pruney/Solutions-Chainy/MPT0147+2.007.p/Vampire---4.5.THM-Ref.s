%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  37 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 (  38 expanded)
%              Number of equality atoms :   30 (  37 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1131,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1119])).

fof(f1119,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(superposition,[],[f17,f340])).

fof(f340,plain,(
    ! [X14,X19,X17,X15,X13,X20,X18,X16] : k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18)) = k6_enumset1(X19,X20,X13,X14,X15,X16,X17,X18) ),
    inference(forward_demodulation,[],[f327,f28])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).

fof(f327,plain,(
    ! [X14,X19,X17,X15,X13,X20,X18,X16] : k2_xboole_0(k2_enumset1(X19,X20,X13,X14),k2_enumset1(X15,X16,X17,X18)) = k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18)) ),
    inference(superposition,[],[f118,f91])).

fof(f91,plain,(
    ! [X6,X4,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8) ),
    inference(forward_demodulation,[],[f82,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f82,plain,(
    ! [X6,X4,X8,X7,X5,X9] : k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k1_tarski(X9),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(superposition,[],[f35,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(superposition,[],[f22,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f118,plain,(
    ! [X14,X12,X15,X13,X11] : k2_xboole_0(k2_tarski(X11,X12),k2_xboole_0(k2_tarski(X13,X14),X15)) = k2_xboole_0(k2_enumset1(X11,X12,X13,X14),X15) ),
    inference(superposition,[],[f22,f92])).

fof(f92,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k2_tarski(X13,X10),k2_tarski(X11,X12)) = k2_enumset1(X13,X10,X11,X12) ),
    inference(forward_demodulation,[],[f83,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f83,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k2_tarski(X13,X10),k2_tarski(X11,X12)) = k2_xboole_0(k1_tarski(X13),k1_enumset1(X10,X11,X12)) ),
    inference(superposition,[],[f35,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f17,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (14997)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (15001)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (15003)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (14998)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (14995)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (15006)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (15005)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (14996)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (15009)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (15002)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (15010)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (15004)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (15006)Refutation not found, incomplete strategy% (15006)------------------------------
% 0.22/0.49  % (15006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15006)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15006)Memory used [KB]: 10618
% 0.22/0.49  % (15006)Time elapsed: 0.071 s
% 0.22/0.49  % (15006)------------------------------
% 0.22/0.49  % (15006)------------------------------
% 0.22/0.50  % (15000)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (15007)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (14999)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (14998)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f1131,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(trivial_inequality_removal,[],[f1119])).
% 0.22/0.52  fof(f1119,plain,(
% 0.22/0.52    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 0.22/0.52    inference(superposition,[],[f17,f340])).
% 0.22/0.52  fof(f340,plain,(
% 0.22/0.52    ( ! [X14,X19,X17,X15,X13,X20,X18,X16] : (k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18)) = k6_enumset1(X19,X20,X13,X14,X15,X16,X17,X18)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f327,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l75_enumset1)).
% 0.22/0.52  fof(f327,plain,(
% 0.22/0.52    ( ! [X14,X19,X17,X15,X13,X20,X18,X16] : (k2_xboole_0(k2_enumset1(X19,X20,X13,X14),k2_enumset1(X15,X16,X17,X18)) = k2_xboole_0(k2_tarski(X19,X20),k4_enumset1(X13,X14,X15,X16,X17,X18))) )),
% 0.22/0.52    inference(superposition,[],[f118,f91])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X6,X4,X8,X7,X5,X9] : (k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k4_enumset1(X9,X4,X5,X6,X7,X8)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f82,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X6,X4,X8,X7,X5,X9] : (k2_xboole_0(k2_tarski(X9,X4),k2_enumset1(X5,X6,X7,X8)) = k2_xboole_0(k1_tarski(X9),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 0.22/0.52    inference(superposition,[],[f35,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),X2)) = k2_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.22/0.52    inference(superposition,[],[f22,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ( ! [X14,X12,X15,X13,X11] : (k2_xboole_0(k2_tarski(X11,X12),k2_xboole_0(k2_tarski(X13,X14),X15)) = k2_xboole_0(k2_enumset1(X11,X12,X13,X14),X15)) )),
% 0.22/0.52    inference(superposition,[],[f22,f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k2_tarski(X13,X10),k2_tarski(X11,X12)) = k2_enumset1(X13,X10,X11,X12)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f83,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X12,X10,X13,X11] : (k2_xboole_0(k2_tarski(X13,X10),k2_tarski(X11,X12)) = k2_xboole_0(k1_tarski(X13),k1_enumset1(X10,X11,X12))) )),
% 0.22/0.52    inference(superposition,[],[f35,f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f14,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.52    inference(negated_conjecture,[],[f12])).
% 0.22/0.52  fof(f12,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (14998)------------------------------
% 0.22/0.52  % (14998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14998)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (14998)Memory used [KB]: 2814
% 0.22/0.52  % (14998)Time elapsed: 0.092 s
% 0.22/0.52  % (14998)------------------------------
% 0.22/0.52  % (14998)------------------------------
% 0.22/0.52  % (14994)Success in time 0.157 s
%------------------------------------------------------------------------------
