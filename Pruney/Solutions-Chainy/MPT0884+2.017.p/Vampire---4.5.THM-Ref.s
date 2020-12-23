%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:57 EST 2020

% Result     : Theorem 20.21s
% Output     : Refutation 20.57s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 165 expanded)
%              Number of leaves         :   14 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :   62 ( 167 expanded)
%              Number of equality atoms :   61 ( 166 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30690,plain,(
    $false ),
    inference(subsumption_resolution,[],[f30689,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f30689,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f30511,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f30511,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f12739,f1242])).

fof(f1242,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1220,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1220,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f110,f26])).

fof(f110,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f100,f26])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f32,f26])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f12739,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f12644,f8752])).

fof(f8752,plain,(
    ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X10,X11,X13,X12) ),
    inference(superposition,[],[f252,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k3_enumset1(X2,X3,X0,X0,X1) ),
    inference(forward_demodulation,[],[f91,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k3_enumset1(X2,X3,X0,X0,X1) ),
    inference(superposition,[],[f33,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f252,plain,(
    ! [X6,X8,X7,X5] : k3_enumset1(X7,X8,X5,X5,X6) = k2_enumset1(X7,X8,X6,X5) ),
    inference(forward_demodulation,[],[f249,f30])).

fof(f249,plain,(
    ! [X6,X8,X7,X5] : k3_enumset1(X7,X8,X5,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k2_tarski(X6,X5)) ),
    inference(superposition,[],[f33,f230])).

fof(f230,plain,(
    ! [X6,X7] : k2_tarski(X7,X6) = k1_enumset1(X6,X6,X7) ),
    inference(forward_demodulation,[],[f223,f23])).

fof(f223,plain,(
    ! [X6,X7] : k1_enumset1(X6,X6,X7) = k1_enumset1(X7,X7,X6) ),
    inference(superposition,[],[f155,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X1,X2,X0) ),
    inference(backward_demodulation,[],[f38,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f46,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(superposition,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f30,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f155,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(forward_demodulation,[],[f151,f25])).

fof(f151,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0) ),
    inference(superposition,[],[f98,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(forward_demodulation,[],[f88,f47])).

fof(f47,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f33,f20])).

fof(f12644,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(superposition,[],[f19,f10067])).

fof(f10067,plain,(
    ! [X144,X142,X143,X141] : k2_enumset1(X144,X141,X142,X143) = k2_enumset1(X144,X143,X141,X142) ),
    inference(superposition,[],[f8829,f149])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4) ),
    inference(superposition,[],[f97,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f8829,plain,(
    ! [X140,X138,X139,X137] : k2_enumset1(X139,X140,X137,X138) = k2_enumset1(X137,X138,X140,X139) ),
    inference(superposition,[],[f8752,f212])).

fof(f212,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5) ),
    inference(superposition,[],[f39,f30])).

fof(f39,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_enumset1(X4,X5,X6,X7) ),
    inference(superposition,[],[f30,f21])).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:13:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (29847)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.44  % (29855)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.45  % (29842)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (29857)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (29849)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (29854)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (29850)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (29843)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (29859)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (29846)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (29851)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (29845)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (29858)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (29853)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (29856)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (29853)Refutation not found, incomplete strategy% (29853)------------------------------
% 0.22/0.50  % (29853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (29853)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (29853)Memory used [KB]: 10618
% 0.22/0.50  % (29853)Time elapsed: 0.069 s
% 0.22/0.50  % (29853)------------------------------
% 0.22/0.50  % (29853)------------------------------
% 0.22/0.50  % (29844)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (29848)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (29852)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.85/1.02  % (29846)Time limit reached!
% 4.85/1.02  % (29846)------------------------------
% 4.85/1.02  % (29846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.02  % (29846)Termination reason: Time limit
% 4.85/1.02  
% 4.85/1.02  % (29846)Memory used [KB]: 11769
% 4.85/1.02  % (29846)Time elapsed: 0.600 s
% 4.85/1.02  % (29846)------------------------------
% 4.85/1.02  % (29846)------------------------------
% 11.92/1.89  % (29847)Time limit reached!
% 11.92/1.89  % (29847)------------------------------
% 11.92/1.89  % (29847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.92/1.89  % (29847)Termination reason: Time limit
% 11.92/1.89  % (29847)Termination phase: Saturation
% 11.92/1.89  
% 11.92/1.89  % (29847)Memory used [KB]: 33901
% 11.92/1.89  % (29847)Time elapsed: 1.500 s
% 11.92/1.89  % (29847)------------------------------
% 11.92/1.89  % (29847)------------------------------
% 12.57/1.97  % (29848)Time limit reached!
% 12.57/1.97  % (29848)------------------------------
% 12.57/1.97  % (29848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.57/1.97  % (29848)Termination reason: Time limit
% 12.57/1.97  % (29848)Termination phase: Saturation
% 12.57/1.97  
% 12.57/1.97  % (29848)Memory used [KB]: 17654
% 12.57/1.97  % (29848)Time elapsed: 1.500 s
% 12.57/1.97  % (29848)------------------------------
% 12.57/1.97  % (29848)------------------------------
% 15.06/2.26  % (29844)Time limit reached!
% 15.06/2.26  % (29844)------------------------------
% 15.06/2.26  % (29844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.06/2.26  % (29844)Termination reason: Time limit
% 15.06/2.26  
% 15.06/2.26  % (29844)Memory used [KB]: 18549
% 15.06/2.26  % (29844)Time elapsed: 1.822 s
% 15.06/2.26  % (29844)------------------------------
% 15.06/2.26  % (29844)------------------------------
% 17.83/2.62  % (29854)Time limit reached!
% 17.83/2.62  % (29854)------------------------------
% 17.83/2.62  % (29854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.83/2.62  % (29854)Termination reason: Time limit
% 17.83/2.62  
% 17.83/2.62  % (29854)Memory used [KB]: 14200
% 17.83/2.62  % (29854)Time elapsed: 2.202 s
% 17.83/2.62  % (29854)------------------------------
% 17.83/2.62  % (29854)------------------------------
% 20.21/2.94  % (29845)Refutation found. Thanks to Tanya!
% 20.21/2.94  % SZS status Theorem for theBenchmark
% 20.21/2.94  % SZS output start Proof for theBenchmark
% 20.21/2.94  fof(f30690,plain,(
% 20.21/2.94    $false),
% 20.21/2.94    inference(subsumption_resolution,[],[f30689,f24])).
% 20.21/2.94  fof(f24,plain,(
% 20.21/2.94    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 20.21/2.94    inference(cnf_transformation,[],[f13])).
% 20.21/2.94  fof(f13,axiom,(
% 20.21/2.94    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 20.21/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 20.21/2.94  fof(f30689,plain,(
% 20.21/2.94    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 20.21/2.94    inference(forward_demodulation,[],[f30511,f28])).
% 20.21/2.94  fof(f28,plain,(
% 20.21/2.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 20.21/2.94    inference(cnf_transformation,[],[f11])).
% 20.21/2.94  fof(f11,axiom,(
% 20.21/2.94    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 20.21/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 20.21/2.94  fof(f30511,plain,(
% 20.21/2.94    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 20.21/2.94    inference(superposition,[],[f12739,f1242])).
% 20.21/2.94  fof(f1242,plain,(
% 20.21/2.94    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 20.21/2.94    inference(forward_demodulation,[],[f1220,f26])).
% 20.21/2.94  fof(f26,plain,(
% 20.21/2.94    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 20.21/2.94    inference(cnf_transformation,[],[f12])).
% 20.21/2.94  fof(f12,axiom,(
% 20.21/2.94    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 20.21/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 20.21/2.94  fof(f1220,plain,(
% 20.21/2.94    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 20.21/2.94    inference(superposition,[],[f110,f26])).
% 20.21/2.94  fof(f110,plain,(
% 20.21/2.94    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 20.21/2.94    inference(forward_demodulation,[],[f100,f26])).
% 20.21/2.94  fof(f100,plain,(
% 20.21/2.94    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 20.21/2.94    inference(superposition,[],[f32,f26])).
% 20.21/2.94  fof(f32,plain,(
% 20.21/2.94    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 20.21/2.94    inference(cnf_transformation,[],[f10])).
% 20.57/2.94  fof(f10,axiom,(
% 20.57/2.94    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 20.57/2.94  fof(f12739,plain,(
% 20.57/2.94    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 20.57/2.94    inference(superposition,[],[f12644,f8752])).
% 20.57/2.94  fof(f8752,plain,(
% 20.57/2.94    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X10,X11,X13,X12)) )),
% 20.57/2.94    inference(superposition,[],[f252,f98])).
% 20.57/2.94  fof(f98,plain,(
% 20.57/2.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X2,X3,X0,X1) = k3_enumset1(X2,X3,X0,X0,X1)) )),
% 20.57/2.94    inference(forward_demodulation,[],[f91,f30])).
% 20.57/2.94  fof(f30,plain,(
% 20.57/2.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 20.57/2.94    inference(cnf_transformation,[],[f2])).
% 20.57/2.94  fof(f2,axiom,(
% 20.57/2.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 20.57/2.94  fof(f91,plain,(
% 20.57/2.94    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k3_enumset1(X2,X3,X0,X0,X1)) )),
% 20.57/2.94    inference(superposition,[],[f33,f23])).
% 20.57/2.94  fof(f23,plain,(
% 20.57/2.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 20.57/2.94    inference(cnf_transformation,[],[f6])).
% 20.57/2.94  fof(f6,axiom,(
% 20.57/2.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 20.57/2.94  fof(f33,plain,(
% 20.57/2.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 20.57/2.94    inference(cnf_transformation,[],[f4])).
% 20.57/2.94  fof(f4,axiom,(
% 20.57/2.94    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 20.57/2.94  fof(f252,plain,(
% 20.57/2.94    ( ! [X6,X8,X7,X5] : (k3_enumset1(X7,X8,X5,X5,X6) = k2_enumset1(X7,X8,X6,X5)) )),
% 20.57/2.94    inference(forward_demodulation,[],[f249,f30])).
% 20.57/2.94  fof(f249,plain,(
% 20.57/2.94    ( ! [X6,X8,X7,X5] : (k3_enumset1(X7,X8,X5,X5,X6) = k2_xboole_0(k2_tarski(X7,X8),k2_tarski(X6,X5))) )),
% 20.57/2.94    inference(superposition,[],[f33,f230])).
% 20.57/2.94  fof(f230,plain,(
% 20.57/2.94    ( ! [X6,X7] : (k2_tarski(X7,X6) = k1_enumset1(X6,X6,X7)) )),
% 20.57/2.94    inference(forward_demodulation,[],[f223,f23])).
% 20.57/2.94  fof(f223,plain,(
% 20.57/2.94    ( ! [X6,X7] : (k1_enumset1(X6,X6,X7) = k1_enumset1(X7,X7,X6)) )),
% 20.57/2.94    inference(superposition,[],[f155,f52])).
% 20.57/2.94  fof(f52,plain,(
% 20.57/2.94    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X1,X2,X0)) )),
% 20.57/2.94    inference(backward_demodulation,[],[f38,f51])).
% 20.57/2.94  fof(f51,plain,(
% 20.57/2.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 20.57/2.94    inference(forward_demodulation,[],[f46,f25])).
% 20.57/2.94  fof(f25,plain,(
% 20.57/2.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 20.57/2.94    inference(cnf_transformation,[],[f7])).
% 20.57/2.94  fof(f7,axiom,(
% 20.57/2.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 20.57/2.94  fof(f46,plain,(
% 20.57/2.94    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 20.57/2.94    inference(superposition,[],[f31,f23])).
% 20.57/2.94  fof(f31,plain,(
% 20.57/2.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 20.57/2.94    inference(cnf_transformation,[],[f3])).
% 20.57/2.94  fof(f3,axiom,(
% 20.57/2.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 20.57/2.94  fof(f38,plain,(
% 20.57/2.94    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 20.57/2.94    inference(superposition,[],[f30,f20])).
% 20.57/2.94  fof(f20,plain,(
% 20.57/2.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 20.57/2.94    inference(cnf_transformation,[],[f5])).
% 20.57/2.94  fof(f5,axiom,(
% 20.57/2.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 20.57/2.94  fof(f155,plain,(
% 20.57/2.94    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 20.57/2.94    inference(forward_demodulation,[],[f151,f25])).
% 20.57/2.94  fof(f151,plain,(
% 20.57/2.94    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_enumset1(X1,X1,X2,X0)) )),
% 20.57/2.94    inference(superposition,[],[f98,f97])).
% 20.57/2.94  fof(f97,plain,(
% 20.57/2.94    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 20.57/2.94    inference(forward_demodulation,[],[f88,f47])).
% 20.57/2.94  fof(f47,plain,(
% 20.57/2.94    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6))) )),
% 20.57/2.94    inference(superposition,[],[f31,f21])).
% 20.57/2.94  fof(f21,plain,(
% 20.57/2.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 20.57/2.94    inference(cnf_transformation,[],[f1])).
% 20.57/2.94  fof(f1,axiom,(
% 20.57/2.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 20.57/2.94  fof(f88,plain,(
% 20.57/2.94    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 20.57/2.94    inference(superposition,[],[f33,f20])).
% 20.57/2.94  fof(f12644,plain,(
% 20.57/2.94    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3))),
% 20.57/2.94    inference(superposition,[],[f19,f10067])).
% 20.57/2.94  fof(f10067,plain,(
% 20.57/2.94    ( ! [X144,X142,X143,X141] : (k2_enumset1(X144,X141,X142,X143) = k2_enumset1(X144,X143,X141,X142)) )),
% 20.57/2.94    inference(superposition,[],[f8829,f149])).
% 20.57/2.94  fof(f149,plain,(
% 20.57/2.94    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4)) )),
% 20.57/2.94    inference(superposition,[],[f97,f29])).
% 20.57/2.94  fof(f29,plain,(
% 20.57/2.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 20.57/2.94    inference(cnf_transformation,[],[f8])).
% 20.57/2.94  fof(f8,axiom,(
% 20.57/2.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 20.57/2.94  fof(f8829,plain,(
% 20.57/2.94    ( ! [X140,X138,X139,X137] : (k2_enumset1(X139,X140,X137,X138) = k2_enumset1(X137,X138,X140,X139)) )),
% 20.57/2.94    inference(superposition,[],[f8752,f212])).
% 20.57/2.94  fof(f212,plain,(
% 20.57/2.94    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)) )),
% 20.57/2.94    inference(superposition,[],[f39,f30])).
% 20.57/2.94  fof(f39,plain,(
% 20.57/2.94    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_enumset1(X4,X5,X6,X7)) )),
% 20.57/2.94    inference(superposition,[],[f30,f21])).
% 20.57/2.94  fof(f19,plain,(
% 20.57/2.94    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 20.57/2.94    inference(cnf_transformation,[],[f18])).
% 20.57/2.94  fof(f18,plain,(
% 20.57/2.94    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 20.57/2.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 20.57/2.94  fof(f17,plain,(
% 20.57/2.94    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 20.57/2.94    introduced(choice_axiom,[])).
% 20.57/2.94  fof(f16,plain,(
% 20.57/2.94    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 20.57/2.94    inference(ennf_transformation,[],[f15])).
% 20.57/2.94  fof(f15,negated_conjecture,(
% 20.57/2.94    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 20.57/2.94    inference(negated_conjecture,[],[f14])).
% 20.57/2.94  fof(f14,conjecture,(
% 20.57/2.94    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 20.57/2.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 20.57/2.94  % SZS output end Proof for theBenchmark
% 20.57/2.94  % (29845)------------------------------
% 20.57/2.94  % (29845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.57/2.94  % (29845)Termination reason: Refutation
% 20.57/2.94  
% 20.57/2.94  % (29845)Memory used [KB]: 38506
% 20.57/2.94  % (29845)Time elapsed: 2.515 s
% 20.57/2.94  % (29845)------------------------------
% 20.57/2.94  % (29845)------------------------------
% 20.65/2.94  % (29841)Success in time 2.58 s
%------------------------------------------------------------------------------
