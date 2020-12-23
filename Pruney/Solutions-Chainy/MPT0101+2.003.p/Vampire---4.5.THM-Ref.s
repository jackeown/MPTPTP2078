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
% DateTime   : Thu Dec  3 12:31:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 232 expanded)
%              Number of leaves         :   13 (  79 expanded)
%              Depth                    :   15
%              Number of atoms          :   59 ( 233 expanded)
%              Number of equality atoms :   58 ( 232 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2641,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2640,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f2640,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f2612,f2637])).

fof(f2637,plain,(
    ! [X72,X73] : k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(X72,k4_xboole_0(X72,X73))) ),
    inference(forward_demodulation,[],[f2636,f1625])).

fof(f1625,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f903,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f903,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X5,X4),X6)) = k4_xboole_0(X4,X6) ),
    inference(superposition,[],[f29,f836])).

fof(f836,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k4_xboole_0(X23,X22)) = X22 ),
    inference(forward_demodulation,[],[f835,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f835,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k1_xboole_0) = k4_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f834,f132])).

fof(f132,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f130,f75])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

% (21041)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f130,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f26,f97])).

fof(f97,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f92,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f92,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f25,f35])).

fof(f35,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f834,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(X22,k4_xboole_0(X23,X22)) ),
    inference(forward_demodulation,[],[f794,f37])).

fof(f37,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f26,f25])).

fof(f794,plain,(
    ! [X23,X22] : k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X23,X22)) ),
    inference(superposition,[],[f32,f35])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2636,plain,(
    ! [X72,X73] : k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(X72,k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)))) ),
    inference(forward_demodulation,[],[f2635,f97])).

fof(f2635,plain,(
    ! [X72,X73] : k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(X72,k2_xboole_0(k4_xboole_0(X72,X73),k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72))))) ),
    inference(forward_demodulation,[],[f2359,f29])).

fof(f2359,plain,(
    ! [X72,X73] : k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X73)),k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)))) ),
    inference(superposition,[],[f838,f33])).

fof(f838,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5 ),
    inference(backward_demodulation,[],[f37,f836])).

fof(f2612,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1666,f2331])).

fof(f2331,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f26,f33])).

fof(f1666,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f98,f1625])).

fof(f98,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f34,f97])).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f30,f29])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f18,f27,f27,f24])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (21038)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.43  % (21036)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (21033)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (21035)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (21029)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (21032)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (21038)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f2641,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f2640,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f28,f27,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.20/0.47  fof(f2640,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(backward_demodulation,[],[f2612,f2637])).
% 0.20/0.47  fof(f2637,plain,(
% 0.20/0.47    ( ! [X72,X73] : (k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(X72,k4_xboole_0(X72,X73)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f2636,f1625])).
% 0.20/0.47  fof(f1625,plain,(
% 0.20/0.47    ( ! [X10,X8,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X8,X9)))) )),
% 0.20/0.47    inference(superposition,[],[f903,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.47  fof(f903,plain,(
% 0.20/0.47    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X5,X4),X6)) = k4_xboole_0(X4,X6)) )),
% 0.20/0.47    inference(superposition,[],[f29,f836])).
% 0.20/0.47  fof(f836,plain,(
% 0.20/0.47    ( ! [X23,X22] : (k4_xboole_0(X22,k4_xboole_0(X23,X22)) = X22) )),
% 0.20/0.47    inference(forward_demodulation,[],[f835,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.47  fof(f835,plain,(
% 0.20/0.47    ( ! [X23,X22] : (k4_xboole_0(X22,k1_xboole_0) = k4_xboole_0(X22,k4_xboole_0(X23,X22))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f834,f132])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f130,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.20/0.47    inference(superposition,[],[f31,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.47    inference(rectify,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f19,f27])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.47  % (21041)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 0.20/0.47    inference(superposition,[],[f26,f97])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f92,f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.20/0.47    inference(superposition,[],[f25,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 0.20/0.47    inference(superposition,[],[f26,f23])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.47  fof(f834,plain,(
% 0.20/0.47    ( ! [X23,X22] : (k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(X22,k4_xboole_0(X23,X22))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f794,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) )),
% 0.20/0.47    inference(superposition,[],[f26,f25])).
% 0.20/0.47  fof(f794,plain,(
% 0.20/0.47    ( ! [X23,X22] : (k4_xboole_0(X22,k4_xboole_0(X22,k2_xboole_0(X22,X23))) = k4_xboole_0(k2_xboole_0(X22,X23),k4_xboole_0(X23,X22))) )),
% 0.20/0.47    inference(superposition,[],[f32,f35])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f22,f24,f24])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.47  fof(f2636,plain,(
% 0.20/0.47    ( ! [X72,X73] : (k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(X72,k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72))))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f2635,f97])).
% 0.20/0.47  fof(f2635,plain,(
% 0.20/0.47    ( ! [X72,X73] : (k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(X72,k2_xboole_0(k4_xboole_0(X72,X73),k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)))))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f2359,f29])).
% 0.20/0.47  fof(f2359,plain,(
% 0.20/0.47    ( ! [X72,X73] : (k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72)) = k4_xboole_0(k2_xboole_0(X72,X73),k4_xboole_0(k4_xboole_0(X72,k4_xboole_0(X72,X73)),k2_xboole_0(k4_xboole_0(X72,X73),k4_xboole_0(X73,X72))))) )),
% 0.20/0.47    inference(superposition,[],[f838,f33])).
% 0.20/0.47  fof(f838,plain,(
% 0.20/0.47    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) = X5) )),
% 0.20/0.47    inference(backward_demodulation,[],[f37,f836])).
% 0.20/0.47  fof(f2612,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(backward_demodulation,[],[f1666,f2331])).
% 0.20/0.47  fof(f2331,plain,(
% 0.20/0.47    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X11,X10)),k4_xboole_0(X10,k4_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 0.20/0.47    inference(superposition,[],[f26,f33])).
% 0.20/0.47  fof(f1666,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.47    inference(backward_demodulation,[],[f98,f1625])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.20/0.47    inference(backward_demodulation,[],[f34,f97])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.20/0.47    inference(backward_demodulation,[],[f30,f29])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.20/0.47    inference(definition_unfolding,[],[f18,f27,f27,f24])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f12])).
% 0.20/0.48  fof(f12,conjecture,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (21038)------------------------------
% 0.20/0.48  % (21038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (21038)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (21038)Memory used [KB]: 12153
% 0.20/0.48  % (21038)Time elapsed: 0.080 s
% 0.20/0.48  % (21038)------------------------------
% 0.20/0.48  % (21038)------------------------------
% 0.20/0.48  % (21031)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (21028)Success in time 0.124 s
%------------------------------------------------------------------------------
