%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:12 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   35 (  49 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  50 expanded)
%              Number of equality atoms :   35 (  49 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3287,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3259])).

fof(f3259,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f27,f1479])).

fof(f1479,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f1454,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1454,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(backward_demodulation,[],[f130,f1449])).

fof(f1449,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4)) ),
    inference(backward_demodulation,[],[f1297,f1389])).

fof(f1389,plain,(
    ! [X12,X13,X11] : k3_xboole_0(X11,k4_xboole_0(X12,X13)) = k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f82,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f82,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f69,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f24,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1297,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5))) ),
    inference(backward_demodulation,[],[f89,f1260])).

fof(f1260,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f78,f17])).

fof(f78,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k2_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8))) ),
    inference(superposition,[],[f19,f24])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f89,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f74,f24])).

fof(f74,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5))) ),
    inference(superposition,[],[f24,f18])).

fof(f130,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(superposition,[],[f26,f18])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f27,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f16,f17])).

fof(f16,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.42  % (20506)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.42  % (20506)Refutation not found, incomplete strategy% (20506)------------------------------
% 0.21/0.42  % (20506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (20506)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.42  
% 0.21/0.42  % (20506)Memory used [KB]: 10618
% 0.21/0.42  % (20506)Time elapsed: 0.004 s
% 0.21/0.42  % (20506)------------------------------
% 0.21/0.42  % (20506)------------------------------
% 0.21/0.45  % (20508)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (20505)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (20499)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (20495)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (20498)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (20507)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (20501)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (20504)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (20503)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (20509)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (20496)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (20511)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (20510)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (20500)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (20497)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (20502)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (20512)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.50/0.59  % (20498)Refutation found. Thanks to Tanya!
% 1.50/0.59  % SZS status Theorem for theBenchmark
% 1.50/0.59  % SZS output start Proof for theBenchmark
% 1.50/0.59  fof(f3287,plain,(
% 1.50/0.59    $false),
% 1.50/0.59    inference(trivial_inequality_removal,[],[f3259])).
% 1.50/0.59  fof(f3259,plain,(
% 1.50/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.50/0.59    inference(superposition,[],[f27,f1479])).
% 1.50/0.59  fof(f1479,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 1.50/0.59    inference(forward_demodulation,[],[f1454,f20])).
% 1.50/0.59  fof(f20,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f7])).
% 1.50/0.59  fof(f7,axiom,(
% 1.50/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.50/0.59  fof(f1454,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X2,X1)))) )),
% 1.50/0.59    inference(backward_demodulation,[],[f130,f1449])).
% 1.50/0.59  fof(f1449,plain,(
% 1.50/0.59    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(X3,k4_xboole_0(X5,X4))) )),
% 1.50/0.59    inference(backward_demodulation,[],[f1297,f1389])).
% 1.50/0.59  fof(f1389,plain,(
% 1.50/0.59    ( ! [X12,X13,X11] : (k3_xboole_0(X11,k4_xboole_0(X12,X13)) = k4_xboole_0(X11,k2_xboole_0(X13,k4_xboole_0(X11,X12)))) )),
% 1.50/0.59    inference(superposition,[],[f82,f17])).
% 1.50/0.59  fof(f17,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f1])).
% 1.50/0.59  fof(f1,axiom,(
% 1.50/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.50/0.59  fof(f82,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.50/0.59    inference(forward_demodulation,[],[f69,f23])).
% 1.50/0.59  fof(f23,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f9])).
% 1.50/0.59  fof(f9,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.50/0.59  fof(f69,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.50/0.59    inference(superposition,[],[f24,f18])).
% 1.50/0.59  fof(f18,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f8])).
% 1.50/0.59  fof(f8,axiom,(
% 1.50/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.50/0.59  fof(f24,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f6])).
% 1.50/0.59  fof(f6,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.50/0.59  fof(f1297,plain,(
% 1.50/0.59    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X5)))) )),
% 1.50/0.59    inference(backward_demodulation,[],[f89,f1260])).
% 1.50/0.59  fof(f1260,plain,(
% 1.50/0.59    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 1.50/0.59    inference(superposition,[],[f78,f17])).
% 1.50/0.59  fof(f78,plain,(
% 1.50/0.59    ( ! [X6,X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k2_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8)))) )),
% 1.50/0.59    inference(superposition,[],[f19,f24])).
% 1.50/0.59  fof(f19,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f4])).
% 1.50/0.59  fof(f4,axiom,(
% 1.50/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.50/0.59  fof(f89,plain,(
% 1.50/0.59    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))) )),
% 1.50/0.59    inference(forward_demodulation,[],[f74,f24])).
% 1.50/0.59  fof(f74,plain,(
% 1.50/0.59    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5)))) )),
% 1.50/0.59    inference(superposition,[],[f24,f18])).
% 1.50/0.59  fof(f130,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.50/0.59    inference(superposition,[],[f26,f18])).
% 1.50/0.59  fof(f26,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f2])).
% 1.50/0.59  fof(f2,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 1.50/0.59  fof(f27,plain,(
% 1.50/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k3_xboole_0(sK0,sK2),k4_xboole_0(sK0,sK1))),
% 1.50/0.59    inference(superposition,[],[f16,f17])).
% 1.50/0.59  fof(f16,plain,(
% 1.50/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.50/0.59    inference(cnf_transformation,[],[f15])).
% 1.50/0.59  fof(f15,plain,(
% 1.50/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 1.50/0.59  fof(f14,plain,(
% 1.50/0.59    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f13,plain,(
% 1.50/0.59    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.50/0.59    inference(ennf_transformation,[],[f12])).
% 1.50/0.59  fof(f12,negated_conjecture,(
% 1.50/0.59    ~! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.50/0.59    inference(negated_conjecture,[],[f11])).
% 1.50/0.59  fof(f11,conjecture,(
% 1.50/0.59    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.50/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.50/0.59  % SZS output end Proof for theBenchmark
% 1.50/0.59  % (20498)------------------------------
% 1.50/0.59  % (20498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.59  % (20498)Termination reason: Refutation
% 1.50/0.59  
% 1.50/0.59  % (20498)Memory used [KB]: 3965
% 1.50/0.59  % (20498)Time elapsed: 0.178 s
% 1.50/0.59  % (20498)------------------------------
% 1.50/0.59  % (20498)------------------------------
% 1.50/0.59  % (20494)Success in time 0.231 s
%------------------------------------------------------------------------------
