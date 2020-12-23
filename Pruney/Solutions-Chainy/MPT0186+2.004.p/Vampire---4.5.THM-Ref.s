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
% DateTime   : Thu Dec  3 12:34:15 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 202 expanded)
%              Number of leaves         :   13 (  67 expanded)
%              Depth                    :   18
%              Number of atoms          :   65 ( 203 expanded)
%              Number of equality atoms :   64 ( 202 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f967,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f942])).

fof(f942,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f19,f403])).

fof(f403,plain,(
    ! [X14,X12,X13,X11] : k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X11,X13,X12,X14) ),
    inference(superposition,[],[f397,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(forward_demodulation,[],[f68,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3) ),
    inference(superposition,[],[f67,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X1,X2,X3,X4,X0,X0) = k3_enumset1(X1,X2,X3,X4,X0) ),
    inference(forward_demodulation,[],[f65,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)) ),
    inference(superposition,[],[f43,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(forward_demodulation,[],[f41,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f30,f26])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).

fof(f397,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X17,X14,X15,X16,X16) = k2_enumset1(X17,X15,X14,X16) ),
    inference(forward_demodulation,[],[f392,f396])).

fof(f396,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f389,f208])).

fof(f208,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17) ),
    inference(forward_demodulation,[],[f204,f207])).

fof(f207,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f201,f26])).

fof(f201,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f66,f21])).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f62,f27])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(superposition,[],[f43,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f204,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X14,X15,X15,X16,X17) = k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17)) ),
    inference(superposition,[],[f66,f101])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(forward_demodulation,[],[f91,f21])).

fof(f91,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1) ),
    inference(superposition,[],[f87,f25])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(forward_demodulation,[],[f83,f25])).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2) ),
    inference(superposition,[],[f71,f26])).

fof(f389,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f265,f25])).

fof(f265,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f257,f27])).

fof(f257,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(superposition,[],[f115,f20])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(forward_demodulation,[],[f108,f29])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(superposition,[],[f55,f21])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(backward_demodulation,[],[f44,f54])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(forward_demodulation,[],[f52,f30])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(superposition,[],[f32,f27])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(superposition,[],[f31,f25])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f392,plain,(
    ! [X14,X17,X15,X16] : k3_enumset1(X17,X14,X15,X16,X16) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X15,X14,X16)) ),
    inference(superposition,[],[f265,f92])).

fof(f92,plain,(
    ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_enumset1(X3,X2,X4,X4) ),
    inference(superposition,[],[f87,f49])).

fof(f49,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X4,X6,X7) ),
    inference(superposition,[],[f36,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f33,f26])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f28,f25])).

fof(f36,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X4,X3,X5),k1_tarski(X6)) ),
    inference(superposition,[],[f34,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:00:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (14628)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.42  % (14617)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (14624)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (14616)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (14625)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (14618)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (14629)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (14632)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (14633)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (14631)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (14620)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (14619)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (14630)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (14626)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (14627)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (14627)Refutation not found, incomplete strategy% (14627)------------------------------
% 0.21/0.50  % (14627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14627)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14627)Memory used [KB]: 10490
% 0.21/0.50  % (14627)Time elapsed: 0.089 s
% 0.21/0.50  % (14627)------------------------------
% 0.21/0.50  % (14627)------------------------------
% 0.21/0.50  % (14622)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (14623)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (14621)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 1.56/0.56  % (14619)Refutation found. Thanks to Tanya!
% 1.56/0.56  % SZS status Theorem for theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f967,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f942])).
% 1.56/0.56  fof(f942,plain,(
% 1.56/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)),
% 1.56/0.56    inference(superposition,[],[f19,f403])).
% 1.56/0.56  fof(f403,plain,(
% 1.56/0.56    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X12,X13,X14) = k2_enumset1(X11,X13,X12,X14)) )),
% 1.56/0.56    inference(superposition,[],[f397,f71])).
% 1.56/0.56  fof(f71,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f68,f26])).
% 1.56/0.56  fof(f26,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.56/0.56  fof(f68,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k3_enumset1(X0,X1,X2,X3,X3)) )),
% 1.56/0.56    inference(superposition,[],[f67,f27])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f11])).
% 1.56/0.56  fof(f11,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.56/0.56  fof(f67,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X2,X3,X4,X0,X0) = k3_enumset1(X1,X2,X3,X4,X0)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f65,f28])).
% 1.56/0.56  fof(f28,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 1.56/0.56  fof(f65,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X1,X2,X3,X4,X0,X0) = k2_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) )),
% 1.56/0.56    inference(superposition,[],[f43,f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f7])).
% 1.56/0.56  fof(f7,axiom,(
% 1.56/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.56  fof(f43,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f41,f29])).
% 1.56/0.56  fof(f29,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f12])).
% 1.56/0.56  fof(f12,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.56/0.56  fof(f41,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) )),
% 1.56/0.56    inference(superposition,[],[f30,f26])).
% 1.56/0.56  fof(f30,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f5])).
% 1.56/0.56  fof(f5,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_enumset1)).
% 1.56/0.56  fof(f397,plain,(
% 1.56/0.56    ( ! [X14,X17,X15,X16] : (k3_enumset1(X17,X14,X15,X16,X16) = k2_enumset1(X17,X15,X14,X16)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f392,f396])).
% 1.56/0.56  fof(f396,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2)) = k2_enumset1(X3,X0,X1,X2)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f389,f208])).
% 1.56/0.56  fof(f208,plain,(
% 1.56/0.56    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X15,X16,X17) = k2_enumset1(X14,X15,X16,X17)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f204,f207])).
% 1.56/0.56  fof(f207,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f201,f26])).
% 1.56/0.56  fof(f201,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.56/0.56    inference(superposition,[],[f66,f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f8])).
% 1.56/0.56  fof(f8,axiom,(
% 1.56/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.56  fof(f66,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f62,f27])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 1.56/0.56    inference(superposition,[],[f43,f25])).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f9])).
% 1.56/0.56  fof(f9,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.56/0.56  fof(f204,plain,(
% 1.56/0.56    ( ! [X14,X17,X15,X16] : (k3_enumset1(X14,X15,X15,X16,X17) = k2_xboole_0(k2_tarski(X14,X15),k2_tarski(X16,X17))) )),
% 1.56/0.56    inference(superposition,[],[f66,f101])).
% 1.56/0.56  fof(f101,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f91,f21])).
% 1.56/0.56  fof(f91,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X0,X1,X1)) )),
% 1.56/0.56    inference(superposition,[],[f87,f25])).
% 1.56/0.56  fof(f87,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f83,f25])).
% 1.56/0.56  fof(f83,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X0,X1,X2,X2)) )),
% 1.56/0.56    inference(superposition,[],[f71,f26])).
% 1.56/0.56  fof(f389,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X3,X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X3),k1_enumset1(X0,X1,X2))) )),
% 1.56/0.56    inference(superposition,[],[f265,f25])).
% 1.56/0.56  fof(f265,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f257,f27])).
% 1.56/0.56  fof(f257,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.56/0.56    inference(superposition,[],[f115,f20])).
% 1.56/0.56  fof(f115,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f108,f29])).
% 1.56/0.56  fof(f108,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 1.56/0.56    inference(superposition,[],[f55,f21])).
% 1.56/0.56  fof(f55,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 1.56/0.56    inference(backward_demodulation,[],[f44,f54])).
% 1.56/0.56  fof(f54,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.56/0.56    inference(forward_demodulation,[],[f52,f30])).
% 1.56/0.56  fof(f52,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.56/0.56    inference(superposition,[],[f32,f27])).
% 1.56/0.56  fof(f32,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 1.56/0.56    inference(superposition,[],[f31,f25])).
% 1.56/0.56  fof(f31,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f3])).
% 1.56/0.56  fof(f3,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 1.56/0.56  fof(f392,plain,(
% 1.56/0.56    ( ! [X14,X17,X15,X16] : (k3_enumset1(X17,X14,X15,X16,X16) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X15,X14,X16))) )),
% 1.56/0.56    inference(superposition,[],[f265,f92])).
% 1.56/0.56  fof(f92,plain,(
% 1.56/0.56    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_enumset1(X3,X2,X4,X4)) )),
% 1.56/0.56    inference(superposition,[],[f87,f49])).
% 1.56/0.56  fof(f49,plain,(
% 1.56/0.56    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X4,X6,X7)) )),
% 1.56/0.56    inference(superposition,[],[f36,f34])).
% 1.56/0.56  fof(f34,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.56/0.56    inference(forward_demodulation,[],[f33,f26])).
% 1.56/0.56  fof(f33,plain,(
% 1.56/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.56/0.56    inference(superposition,[],[f28,f25])).
% 1.56/0.56  fof(f36,plain,(
% 1.56/0.56    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X4,X3,X5),k1_tarski(X6))) )),
% 1.56/0.56    inference(superposition,[],[f34,f24])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f13])).
% 1.56/0.56  fof(f13,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_enumset1)).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 1.56/0.56    inference(cnf_transformation,[],[f18])).
% 1.56/0.56  fof(f18,plain,(
% 1.56/0.56    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 1.56/0.56  fof(f17,plain,(
% 1.56/0.56    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f16,plain,(
% 1.56/0.56    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 1.56/0.56    inference(ennf_transformation,[],[f15])).
% 1.56/0.56  fof(f15,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 1.56/0.56    inference(negated_conjecture,[],[f14])).
% 1.56/0.56  fof(f14,conjecture,(
% 1.56/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 1.56/0.56  % SZS output end Proof for theBenchmark
% 1.56/0.56  % (14619)------------------------------
% 1.56/0.56  % (14619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (14619)Termination reason: Refutation
% 1.56/0.56  
% 1.56/0.56  % (14619)Memory used [KB]: 2430
% 1.56/0.56  % (14619)Time elapsed: 0.139 s
% 1.56/0.56  % (14619)------------------------------
% 1.56/0.56  % (14619)------------------------------
% 1.56/0.56  % (14615)Success in time 0.201 s
%------------------------------------------------------------------------------
