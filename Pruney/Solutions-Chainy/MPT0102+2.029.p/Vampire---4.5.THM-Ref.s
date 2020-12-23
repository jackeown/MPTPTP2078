%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 130 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :   51 ( 131 expanded)
%              Number of equality atoms :   50 ( 130 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f376])).

fof(f376,plain,(
    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f164,f167])).

fof(f167,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f162,f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f162,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f94,f154])).

fof(f154,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8)) ),
    inference(backward_demodulation,[],[f125,f146])).

fof(f146,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f49,f142])).

fof(f142,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(backward_demodulation,[],[f42,f138])).

fof(f138,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f68,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f19,f17])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(backward_demodulation,[],[f53,f61])).

fof(f61,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f52,f19])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f42,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,X7) ),
    inference(superposition,[],[f21,f27])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f22,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f125,plain,(
    ! [X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0) = k4_xboole_0(X8,k2_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f112,f20])).

fof(f112,plain,(
    ! [X8,X9] : k3_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f26,f49])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f94,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f80,f26])).

fof(f80,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1)) ),
    inference(superposition,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f164,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f101,f163])).

fof(f163,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X5,k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f159,f27])).

fof(f159,plain,(
    ! [X4,X5] : k5_xboole_0(X5,k2_xboole_0(X4,X5)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5)) ),
    inference(backward_demodulation,[],[f86,f154])).

fof(f86,plain,(
    ! [X4,X5] : k5_xboole_0(X5,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(X4,X5)),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f24,f21])).

fof(f101,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f16,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f16,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:06:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (4396)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.46  % (4395)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (4394)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (4399)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (4408)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (4393)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (4404)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (4402)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (4396)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (4397)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (4405)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (4406)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (4401)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f377,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f376])).
% 0.22/0.48  fof(f376,plain,(
% 0.22/0.48    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(superposition,[],[f164,f167])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f162,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.48  fof(f162,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k1_xboole_0)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f94,f154])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,X8))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f125,f146])).
% 0.22/0.48  fof(f146,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f49,f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f42,f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7)) )),
% 0.22/0.48    inference(superposition,[],[f68,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.48    inference(superposition,[],[f19,f17])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.48    inference(backward_demodulation,[],[f53,f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2) )),
% 0.22/0.48    inference(superposition,[],[f23,f19])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f52,f19])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(superposition,[],[f20,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X7] : (k4_xboole_0(k1_xboole_0,X7) = k4_xboole_0(X7,X7)) )),
% 0.22/0.48    inference(superposition,[],[f21,f27])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(superposition,[],[f22,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ( ! [X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0) = k4_xboole_0(X8,k2_xboole_0(X9,X8))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f112,f20])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    ( ! [X8,X9] : (k3_xboole_0(k4_xboole_0(X8,X9),k1_xboole_0) = k4_xboole_0(X8,k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 0.22/0.48    inference(superposition,[],[f26,f49])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,k2_xboole_0(X2,X1)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f80,f26])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(k4_xboole_0(X1,X2),X1))) )),
% 0.22/0.48    inference(superposition,[],[f24,f22])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    k3_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.48    inference(backward_demodulation,[],[f101,f163])).
% 0.22/0.48  fof(f163,plain,(
% 0.22/0.48    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X5,k2_xboole_0(X4,X5))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f159,f27])).
% 0.22/0.48  fof(f159,plain,(
% 0.22/0.48    ( ! [X4,X5] : (k5_xboole_0(X5,k2_xboole_0(X4,X5)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,X5))) )),
% 0.22/0.48    inference(backward_demodulation,[],[f86,f154])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X4,X5] : (k5_xboole_0(X5,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(X4,X5)),k4_xboole_0(X4,X5))) )),
% 0.22/0.48    inference(superposition,[],[f24,f21])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    k3_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 0.22/0.48    inference(superposition,[],[f16,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.48    inference(negated_conjecture,[],[f11])).
% 0.22/0.48  fof(f11,conjecture,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (4396)------------------------------
% 0.22/0.48  % (4396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4396)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (4396)Memory used [KB]: 1791
% 0.22/0.48  % (4396)Time elapsed: 0.059 s
% 0.22/0.48  % (4396)------------------------------
% 0.22/0.48  % (4396)------------------------------
% 0.22/0.49  % (4392)Success in time 0.125 s
%------------------------------------------------------------------------------
