%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:03 EST 2020

% Result     : Theorem 20.65s
% Output     : Refutation 20.65s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 135 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   14
%              Number of atoms          :   61 ( 137 expanded)
%              Number of equality atoms :   60 ( 136 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40166,plain,(
    $false ),
    inference(subsumption_resolution,[],[f40165,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f40165,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f39985,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f39985,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f13268,f1281])).

fof(f1281,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1263,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1263,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f114,f25])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f105,f25])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f31,f25])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f13268,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f12335,f10669])).

fof(f10669,plain,(
    ! [X152,X151,X149,X150] : k2_enumset1(X150,X151,X149,X152) = k2_enumset1(X150,X151,X152,X149) ),
    inference(superposition,[],[f1870,f1798])).

fof(f1798,plain,(
    ! [X10,X8,X7,X9] : k2_enumset1(X9,X7,X8,X10) = k2_enumset1(X7,X8,X9,X10) ),
    inference(superposition,[],[f102,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k3_enumset1(X2,X3,X0,X0,X1) ),
    inference(forward_demodulation,[],[f86,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k3_enumset1(X2,X3,X0,X0,X1) ),
    inference(superposition,[],[f32,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f102,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X6,X4,X5,X7) ),
    inference(forward_demodulation,[],[f96,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f95,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f33,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f96,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X5,X6,X6,X7) = k2_xboole_0(k1_enumset1(X6,X4,X5),k1_tarski(X7)) ),
    inference(superposition,[],[f33,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0) ),
    inference(backward_demodulation,[],[f38,f78])).

fof(f78,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f45,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f37,f26])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f30,f20])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f30,f20])).

fof(f1870,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4) ),
    inference(superposition,[],[f342,f29])).

fof(f342,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(forward_demodulation,[],[f333,f101])).

fof(f333,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)) ),
    inference(superposition,[],[f87,f20])).

fof(f87,plain,(
    ! [X6,X8,X7,X5,X9] : k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9) ),
    inference(superposition,[],[f32,f21])).

fof(f12335,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(superposition,[],[f19,f8243])).

fof(f8243,plain,(
    ! [X127,X125,X128,X126] : k2_enumset1(X127,X128,X125,X126) = k2_enumset1(X127,X125,X126,X128) ),
    inference(superposition,[],[f1798,f165])).

fof(f165,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5) ),
    inference(superposition,[],[f39,f30])).

fof(f39,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_enumset1(X4,X5,X6,X7) ),
    inference(superposition,[],[f30,f21])).

fof(f19,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:34:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (31803)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (31804)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (31797)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (31796)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (31795)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (31806)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (31793)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (31789)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (31794)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (31792)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (31799)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (31802)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (31791)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (31801)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (31801)Refutation not found, incomplete strategy% (31801)------------------------------
% 0.22/0.51  % (31801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31801)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31801)Memory used [KB]: 10618
% 0.22/0.51  % (31801)Time elapsed: 0.092 s
% 0.22/0.51  % (31801)------------------------------
% 0.22/0.51  % (31801)------------------------------
% 0.22/0.51  % (31790)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (31807)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.52  % (31805)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.53  % (31798)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 5.29/1.04  % (31793)Time limit reached!
% 5.29/1.04  % (31793)------------------------------
% 5.29/1.04  % (31793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.29/1.04  % (31793)Termination reason: Time limit
% 5.29/1.04  % (31793)Termination phase: Saturation
% 5.29/1.04  
% 5.29/1.04  % (31793)Memory used [KB]: 14839
% 5.29/1.04  % (31793)Time elapsed: 0.600 s
% 5.29/1.04  % (31793)------------------------------
% 5.29/1.04  % (31793)------------------------------
% 12.37/1.95  % (31794)Time limit reached!
% 12.37/1.95  % (31794)------------------------------
% 12.37/1.95  % (31794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.37/1.97  % (31794)Termination reason: Time limit
% 12.37/1.97  
% 12.37/1.97  % (31794)Memory used [KB]: 35180
% 12.37/1.97  % (31794)Time elapsed: 1.528 s
% 12.37/1.97  % (31794)------------------------------
% 12.37/1.97  % (31794)------------------------------
% 12.81/1.98  % (31795)Time limit reached!
% 12.81/1.98  % (31795)------------------------------
% 12.81/1.98  % (31795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.81/1.98  % (31795)Termination reason: Time limit
% 12.81/1.98  % (31795)Termination phase: Saturation
% 12.81/1.98  
% 12.81/1.98  % (31795)Memory used [KB]: 24050
% 12.81/1.98  % (31795)Time elapsed: 1.500 s
% 12.81/1.98  % (31795)------------------------------
% 12.81/1.98  % (31795)------------------------------
% 14.84/2.28  % (31791)Time limit reached!
% 14.84/2.28  % (31791)------------------------------
% 14.84/2.28  % (31791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.84/2.28  % (31791)Termination reason: Time limit
% 14.84/2.28  % (31791)Termination phase: Saturation
% 14.84/2.28  
% 14.84/2.28  % (31791)Memory used [KB]: 18549
% 14.84/2.28  % (31791)Time elapsed: 1.800 s
% 14.84/2.28  % (31791)------------------------------
% 14.84/2.28  % (31791)------------------------------
% 17.73/2.65  % (31802)Time limit reached!
% 17.73/2.65  % (31802)------------------------------
% 17.73/2.65  % (31802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.73/2.65  % (31802)Termination reason: Time limit
% 17.73/2.65  
% 17.73/2.65  % (31802)Memory used [KB]: 20724
% 17.73/2.65  % (31802)Time elapsed: 2.228 s
% 17.73/2.65  % (31802)------------------------------
% 17.73/2.65  % (31802)------------------------------
% 20.65/2.95  % (31792)Refutation found. Thanks to Tanya!
% 20.65/2.95  % SZS status Theorem for theBenchmark
% 20.65/2.95  % SZS output start Proof for theBenchmark
% 20.65/2.95  fof(f40166,plain,(
% 20.65/2.95    $false),
% 20.65/2.95    inference(subsumption_resolution,[],[f40165,f24])).
% 20.65/2.95  fof(f24,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 20.65/2.95    inference(cnf_transformation,[],[f13])).
% 20.65/2.95  fof(f13,axiom,(
% 20.65/2.95    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 20.65/2.95  fof(f40165,plain,(
% 20.65/2.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 20.65/2.95    inference(forward_demodulation,[],[f39985,f27])).
% 20.65/2.95  fof(f27,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 20.65/2.95    inference(cnf_transformation,[],[f11])).
% 20.65/2.95  fof(f11,axiom,(
% 20.65/2.95    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 20.65/2.95  fof(f39985,plain,(
% 20.65/2.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 20.65/2.95    inference(superposition,[],[f13268,f1281])).
% 20.65/2.95  fof(f1281,plain,(
% 20.65/2.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 20.65/2.95    inference(forward_demodulation,[],[f1263,f25])).
% 20.65/2.95  fof(f25,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 20.65/2.95    inference(cnf_transformation,[],[f12])).
% 20.65/2.95  fof(f12,axiom,(
% 20.65/2.95    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 20.65/2.95  fof(f1263,plain,(
% 20.65/2.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 20.65/2.95    inference(superposition,[],[f114,f25])).
% 20.65/2.95  fof(f114,plain,(
% 20.65/2.95    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 20.65/2.95    inference(forward_demodulation,[],[f105,f25])).
% 20.65/2.95  fof(f105,plain,(
% 20.65/2.95    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 20.65/2.95    inference(superposition,[],[f31,f25])).
% 20.65/2.95  fof(f31,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 20.65/2.95    inference(cnf_transformation,[],[f10])).
% 20.65/2.95  fof(f10,axiom,(
% 20.65/2.95    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 20.65/2.95  fof(f13268,plain,(
% 20.65/2.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 20.65/2.95    inference(superposition,[],[f12335,f10669])).
% 20.65/2.95  fof(f10669,plain,(
% 20.65/2.95    ( ! [X152,X151,X149,X150] : (k2_enumset1(X150,X151,X149,X152) = k2_enumset1(X150,X151,X152,X149)) )),
% 20.65/2.95    inference(superposition,[],[f1870,f1798])).
% 20.65/2.95  fof(f1798,plain,(
% 20.65/2.95    ( ! [X10,X8,X7,X9] : (k2_enumset1(X9,X7,X8,X10) = k2_enumset1(X7,X8,X9,X10)) )),
% 20.65/2.95    inference(superposition,[],[f102,f92])).
% 20.65/2.95  fof(f92,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X2,X3,X0,X1) = k3_enumset1(X2,X3,X0,X0,X1)) )),
% 20.65/2.95    inference(forward_demodulation,[],[f86,f30])).
% 20.65/2.95  fof(f30,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 20.65/2.95    inference(cnf_transformation,[],[f2])).
% 20.65/2.95  fof(f2,axiom,(
% 20.65/2.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 20.65/2.95  fof(f86,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k3_enumset1(X2,X3,X0,X0,X1)) )),
% 20.65/2.95    inference(superposition,[],[f32,f23])).
% 20.65/2.95  fof(f23,plain,(
% 20.65/2.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 20.65/2.95    inference(cnf_transformation,[],[f6])).
% 20.65/2.95  fof(f6,axiom,(
% 20.65/2.95    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 20.65/2.95  fof(f32,plain,(
% 20.65/2.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 20.65/2.95    inference(cnf_transformation,[],[f3])).
% 20.65/2.95  fof(f3,axiom,(
% 20.65/2.95    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 20.65/2.95  fof(f102,plain,(
% 20.65/2.95    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k2_enumset1(X6,X4,X5,X7)) )),
% 20.65/2.95    inference(forward_demodulation,[],[f96,f101])).
% 20.65/2.95  fof(f101,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 20.65/2.95    inference(forward_demodulation,[],[f95,f29])).
% 20.65/2.95  fof(f29,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 20.65/2.95    inference(cnf_transformation,[],[f8])).
% 20.65/2.95  fof(f8,axiom,(
% 20.65/2.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 20.65/2.95  fof(f95,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 20.65/2.95    inference(superposition,[],[f33,f26])).
% 20.65/2.95  fof(f26,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 20.65/2.95    inference(cnf_transformation,[],[f7])).
% 20.65/2.95  fof(f7,axiom,(
% 20.65/2.95    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 20.65/2.95  fof(f33,plain,(
% 20.65/2.95    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 20.65/2.95    inference(cnf_transformation,[],[f4])).
% 20.65/2.95  fof(f4,axiom,(
% 20.65/2.95    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 20.65/2.95  fof(f96,plain,(
% 20.65/2.95    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X5,X6,X6,X7) = k2_xboole_0(k1_enumset1(X6,X4,X5),k1_tarski(X7))) )),
% 20.65/2.95    inference(superposition,[],[f33,f82])).
% 20.65/2.95  fof(f82,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)) )),
% 20.65/2.95    inference(backward_demodulation,[],[f38,f78])).
% 20.65/2.95  fof(f78,plain,(
% 20.65/2.95    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) )),
% 20.65/2.95    inference(superposition,[],[f45,f21])).
% 20.65/2.95  fof(f21,plain,(
% 20.65/2.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 20.65/2.95    inference(cnf_transformation,[],[f1])).
% 20.65/2.95  fof(f1,axiom,(
% 20.65/2.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 20.65/2.95  fof(f45,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 20.65/2.95    inference(forward_demodulation,[],[f37,f26])).
% 20.65/2.95  fof(f37,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 20.65/2.95    inference(superposition,[],[f30,f20])).
% 20.65/2.95  fof(f20,plain,(
% 20.65/2.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 20.65/2.95    inference(cnf_transformation,[],[f5])).
% 20.65/2.95  fof(f5,axiom,(
% 20.65/2.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 20.65/2.95  fof(f38,plain,(
% 20.65/2.95    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 20.65/2.95    inference(superposition,[],[f30,f20])).
% 20.65/2.95  fof(f1870,plain,(
% 20.65/2.95    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X5,X6,X7,X4)) )),
% 20.65/2.95    inference(superposition,[],[f342,f29])).
% 20.65/2.95  fof(f342,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 20.65/2.95    inference(forward_demodulation,[],[f333,f101])).
% 20.65/2.95  fof(f333,plain,(
% 20.65/2.95    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) )),
% 20.65/2.95    inference(superposition,[],[f87,f20])).
% 20.65/2.95  fof(f87,plain,(
% 20.65/2.95    ( ! [X6,X8,X7,X5,X9] : (k2_xboole_0(k1_enumset1(X7,X8,X9),k2_tarski(X5,X6)) = k3_enumset1(X5,X6,X7,X8,X9)) )),
% 20.65/2.95    inference(superposition,[],[f32,f21])).
% 20.65/2.95  fof(f12335,plain,(
% 20.65/2.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3))),
% 20.65/2.95    inference(superposition,[],[f19,f8243])).
% 20.65/2.95  fof(f8243,plain,(
% 20.65/2.95    ( ! [X127,X125,X128,X126] : (k2_enumset1(X127,X128,X125,X126) = k2_enumset1(X127,X125,X126,X128)) )),
% 20.65/2.95    inference(superposition,[],[f1798,f165])).
% 20.65/2.95  fof(f165,plain,(
% 20.65/2.95    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)) )),
% 20.65/2.95    inference(superposition,[],[f39,f30])).
% 20.65/2.95  fof(f39,plain,(
% 20.65/2.95    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) = k2_enumset1(X4,X5,X6,X7)) )),
% 20.65/2.95    inference(superposition,[],[f30,f21])).
% 20.65/2.95  fof(f19,plain,(
% 20.65/2.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 20.65/2.95    inference(cnf_transformation,[],[f18])).
% 20.65/2.95  fof(f18,plain,(
% 20.65/2.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 20.65/2.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 20.65/2.95  fof(f17,plain,(
% 20.65/2.95    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 20.65/2.95    introduced(choice_axiom,[])).
% 20.65/2.95  fof(f16,plain,(
% 20.65/2.95    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 20.65/2.95    inference(ennf_transformation,[],[f15])).
% 20.65/2.95  fof(f15,negated_conjecture,(
% 20.65/2.95    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 20.65/2.95    inference(negated_conjecture,[],[f14])).
% 20.65/2.95  fof(f14,conjecture,(
% 20.65/2.95    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 20.65/2.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 20.65/2.95  % SZS output end Proof for theBenchmark
% 20.65/2.95  % (31792)------------------------------
% 20.65/2.95  % (31792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.65/2.95  % (31792)Termination reason: Refutation
% 20.65/2.95  
% 20.65/2.95  % (31792)Memory used [KB]: 45159
% 20.65/2.95  % (31792)Time elapsed: 2.522 s
% 20.65/2.95  % (31792)------------------------------
% 20.65/2.95  % (31792)------------------------------
% 20.65/2.96  % (31786)Success in time 2.579 s
%------------------------------------------------------------------------------
