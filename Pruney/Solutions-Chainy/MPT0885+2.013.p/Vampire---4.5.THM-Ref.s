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
% DateTime   : Thu Dec  3 12:59:02 EST 2020

% Result     : Theorem 13.70s
% Output     : Refutation 14.02s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 396 expanded)
%              Number of leaves         :   14 ( 132 expanded)
%              Depth                    :   18
%              Number of atoms          :   62 ( 398 expanded)
%              Number of equality atoms :   61 ( 397 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22991,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22990,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f22990,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f22841,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f22841,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f14048,f797])).

fof(f797,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f782,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f782,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f114,f24])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f107,f24])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f14048,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f13800,f1425])).

fof(f1425,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X11,X10,X8,X9) = k2_enumset1(X11,X10,X9,X8) ),
    inference(superposition,[],[f341,f342])).

fof(f342,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k2_enumset1(X1,X0,X2,X3) ),
    inference(backward_demodulation,[],[f88,f338])).

fof(f338,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X9,X10,X10,X11) = k2_enumset1(X11,X10,X8,X9) ),
    inference(forward_demodulation,[],[f330,f95])).

fof(f95,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    inference(superposition,[],[f93,f40])).

fof(f40,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(forward_demodulation,[],[f83,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f30,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f330,plain,(
    ! [X10,X8,X11,X9] : k3_enumset1(X8,X9,X10,X10,X11) = k2_xboole_0(k1_enumset1(X10,X8,X9),k1_tarski(X11)) ),
    inference(superposition,[],[f31,f160])).

fof(f160,plain,(
    ! [X6,X7,X5] : k2_enumset1(X7,X5,X6,X6) = k1_enumset1(X6,X7,X5) ),
    inference(superposition,[],[f120,f105])).

fof(f105,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    inference(superposition,[],[f104,f28])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X3,X0,X1,X2) ),
    inference(forward_demodulation,[],[f99,f95])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f31,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f120,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X0,X1) ),
    inference(superposition,[],[f105,f25])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f30,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f341,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6)) = k2_enumset1(X6,X5,X3,X4) ),
    inference(backward_demodulation,[],[f212,f338])).

fof(f212,plain,(
    ! [X6,X4,X5,X3] : k3_enumset1(X3,X4,X5,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f88,f20])).

fof(f13800,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(superposition,[],[f18,f7696])).

fof(f7696,plain,(
    ! [X118,X120,X119,X117] : k2_enumset1(X118,X119,X120,X117) = k2_enumset1(X118,X117,X119,X120) ),
    inference(superposition,[],[f1354,f105])).

fof(f1354,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X6,X7,X4,X5) = k2_enumset1(X7,X6,X4,X5) ),
    inference(superposition,[],[f340,f342])).

fof(f340,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3)) = k2_enumset1(X4,X3,X5,X6) ),
    inference(backward_demodulation,[],[f219,f338])).

fof(f219,plain,(
    ! [X6,X4,X5,X3] : k3_enumset1(X5,X6,X3,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3)) ),
    inference(superposition,[],[f88,f20])).

fof(f18,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.43  % (10811)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (10804)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (10810)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (10797)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (10796)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (10799)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (10806)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (10802)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (10795)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (10805)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (10805)Refutation not found, incomplete strategy% (10805)------------------------------
% 0.20/0.49  % (10805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (10805)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (10805)Memory used [KB]: 10618
% 0.20/0.49  % (10805)Time elapsed: 0.086 s
% 0.20/0.49  % (10805)------------------------------
% 0.20/0.49  % (10805)------------------------------
% 0.20/0.49  % (10803)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (10798)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (10801)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (10808)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (10800)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (10809)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (10794)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (10807)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 4.77/1.02  % (10798)Time limit reached!
% 4.77/1.02  % (10798)------------------------------
% 4.77/1.02  % (10798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.02  % (10798)Termination reason: Time limit
% 4.77/1.02  % (10798)Termination phase: Saturation
% 4.77/1.02  
% 4.77/1.02  % (10798)Memory used [KB]: 10874
% 4.77/1.02  % (10798)Time elapsed: 0.600 s
% 4.77/1.02  % (10798)------------------------------
% 4.77/1.02  % (10798)------------------------------
% 12.45/1.93  % (10799)Time limit reached!
% 12.45/1.93  % (10799)------------------------------
% 12.45/1.93  % (10799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.45/1.93  % (10799)Termination reason: Time limit
% 12.45/1.93  
% 12.45/1.93  % (10799)Memory used [KB]: 31982
% 12.45/1.93  % (10799)Time elapsed: 1.529 s
% 12.45/1.93  % (10799)------------------------------
% 12.45/1.93  % (10799)------------------------------
% 12.45/1.97  % (10800)Time limit reached!
% 12.45/1.97  % (10800)------------------------------
% 12.45/1.97  % (10800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.45/1.97  % (10800)Termination reason: Time limit
% 12.45/1.97  % (10800)Termination phase: Saturation
% 12.45/1.97  
% 12.45/1.97  % (10800)Memory used [KB]: 17398
% 12.45/1.97  % (10800)Time elapsed: 1.500 s
% 12.45/1.97  % (10800)------------------------------
% 12.45/1.97  % (10800)------------------------------
% 13.70/2.11  % (10797)Refutation found. Thanks to Tanya!
% 13.70/2.11  % SZS status Theorem for theBenchmark
% 13.70/2.11  % SZS output start Proof for theBenchmark
% 13.70/2.11  fof(f22991,plain,(
% 13.70/2.11    $false),
% 13.70/2.11    inference(subsumption_resolution,[],[f22990,f23])).
% 13.70/2.11  fof(f23,plain,(
% 13.70/2.11    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f12])).
% 13.70/2.11  fof(f12,axiom,(
% 13.70/2.11    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 13.70/2.11  fof(f22990,plain,(
% 13.70/2.11    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 13.70/2.11    inference(forward_demodulation,[],[f22841,f26])).
% 13.70/2.11  fof(f26,plain,(
% 13.70/2.11    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 13.70/2.11    inference(cnf_transformation,[],[f10])).
% 13.70/2.11  fof(f10,axiom,(
% 13.70/2.11    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 13.70/2.11  fof(f22841,plain,(
% 13.70/2.11    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 13.70/2.11    inference(superposition,[],[f14048,f797])).
% 13.70/2.11  fof(f797,plain,(
% 13.70/2.11    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 13.70/2.11    inference(forward_demodulation,[],[f782,f24])).
% 13.70/2.11  fof(f24,plain,(
% 13.70/2.11    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f11])).
% 13.70/2.11  fof(f11,axiom,(
% 13.70/2.11    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 13.70/2.11  fof(f782,plain,(
% 13.70/2.11    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 13.70/2.11    inference(superposition,[],[f114,f24])).
% 13.70/2.11  fof(f114,plain,(
% 13.70/2.11    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 13.70/2.11    inference(forward_demodulation,[],[f107,f24])).
% 13.70/2.11  fof(f107,plain,(
% 13.70/2.11    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 13.70/2.11    inference(superposition,[],[f29,f24])).
% 13.70/2.11  fof(f29,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 13.70/2.11    inference(cnf_transformation,[],[f9])).
% 13.70/2.11  fof(f9,axiom,(
% 13.70/2.11    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 13.70/2.11  fof(f14048,plain,(
% 13.70/2.11    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 13.70/2.11    inference(superposition,[],[f13800,f1425])).
% 13.70/2.11  fof(f1425,plain,(
% 13.70/2.11    ( ! [X10,X8,X11,X9] : (k2_enumset1(X11,X10,X8,X9) = k2_enumset1(X11,X10,X9,X8)) )),
% 13.70/2.11    inference(superposition,[],[f341,f342])).
% 13.70/2.11  fof(f342,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)) = k2_enumset1(X1,X0,X2,X3)) )),
% 13.70/2.11    inference(backward_demodulation,[],[f88,f338])).
% 13.70/2.11  fof(f338,plain,(
% 13.70/2.11    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X9,X10,X10,X11) = k2_enumset1(X11,X10,X8,X9)) )),
% 13.70/2.11    inference(forward_demodulation,[],[f330,f95])).
% 13.70/2.11  fof(f95,plain,(
% 13.70/2.11    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) )),
% 13.70/2.11    inference(superposition,[],[f93,f40])).
% 13.70/2.11  fof(f40,plain,(
% 13.70/2.11    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 13.70/2.11    inference(superposition,[],[f33,f22])).
% 13.70/2.11  fof(f22,plain,(
% 13.70/2.11    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f8])).
% 13.70/2.11  fof(f8,axiom,(
% 13.70/2.11    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 13.70/2.11  fof(f33,plain,(
% 13.70/2.11    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 13.70/2.11    inference(superposition,[],[f22,f20])).
% 13.70/2.11  fof(f20,plain,(
% 13.70/2.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f1])).
% 13.70/2.11  fof(f1,axiom,(
% 13.70/2.11    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 13.70/2.11  fof(f93,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 13.70/2.11    inference(forward_demodulation,[],[f83,f28])).
% 13.70/2.11  fof(f28,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f7])).
% 13.70/2.11  fof(f7,axiom,(
% 13.70/2.11    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 13.70/2.11  fof(f83,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 13.70/2.11    inference(superposition,[],[f30,f19])).
% 13.70/2.11  fof(f19,plain,(
% 13.70/2.11    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f4])).
% 13.70/2.11  fof(f4,axiom,(
% 13.70/2.11    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 13.70/2.11  fof(f30,plain,(
% 13.70/2.11    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 13.70/2.11    inference(cnf_transformation,[],[f2])).
% 13.70/2.11  fof(f2,axiom,(
% 13.70/2.11    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 13.70/2.11  fof(f330,plain,(
% 13.70/2.11    ( ! [X10,X8,X11,X9] : (k3_enumset1(X8,X9,X10,X10,X11) = k2_xboole_0(k1_enumset1(X10,X8,X9),k1_tarski(X11))) )),
% 13.70/2.11    inference(superposition,[],[f31,f160])).
% 13.70/2.11  fof(f160,plain,(
% 13.70/2.11    ( ! [X6,X7,X5] : (k2_enumset1(X7,X5,X6,X6) = k1_enumset1(X6,X7,X5)) )),
% 13.70/2.11    inference(superposition,[],[f120,f105])).
% 13.70/2.11  fof(f105,plain,(
% 13.70/2.11    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) )),
% 13.70/2.11    inference(superposition,[],[f104,f28])).
% 13.70/2.11  fof(f104,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X3,X0,X1,X2)) )),
% 13.70/2.11    inference(forward_demodulation,[],[f99,f95])).
% 13.70/2.11  fof(f99,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 13.70/2.11    inference(superposition,[],[f31,f25])).
% 13.70/2.11  fof(f25,plain,(
% 13.70/2.11    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f6])).
% 13.70/2.11  fof(f6,axiom,(
% 13.70/2.11    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 13.70/2.11  fof(f120,plain,(
% 13.70/2.11    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X2,X0,X0,X1)) )),
% 13.70/2.11    inference(superposition,[],[f105,f25])).
% 13.70/2.11  fof(f31,plain,(
% 13.70/2.11    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 13.70/2.11    inference(cnf_transformation,[],[f3])).
% 13.70/2.11  fof(f3,axiom,(
% 13.70/2.11    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 13.70/2.11  fof(f88,plain,(
% 13.70/2.11    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X3,X0,X0,X1) = k2_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) )),
% 13.70/2.11    inference(superposition,[],[f30,f21])).
% 13.70/2.11  fof(f21,plain,(
% 13.70/2.11    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 13.70/2.11    inference(cnf_transformation,[],[f5])).
% 13.70/2.11  fof(f5,axiom,(
% 13.70/2.11    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 13.70/2.11    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 13.70/2.11  fof(f341,plain,(
% 13.70/2.11    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6)) = k2_enumset1(X6,X5,X3,X4)) )),
% 13.70/2.11    inference(backward_demodulation,[],[f212,f338])).
% 13.70/2.11  fof(f212,plain,(
% 13.70/2.11    ( ! [X6,X4,X5,X3] : (k3_enumset1(X3,X4,X5,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6))) )),
% 13.70/2.11    inference(superposition,[],[f88,f20])).
% 13.70/2.11  fof(f13800,plain,(
% 13.70/2.11    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3))),
% 13.70/2.11    inference(superposition,[],[f18,f7696])).
% 13.70/2.11  fof(f7696,plain,(
% 13.70/2.11    ( ! [X118,X120,X119,X117] : (k2_enumset1(X118,X119,X120,X117) = k2_enumset1(X118,X117,X119,X120)) )),
% 13.70/2.11    inference(superposition,[],[f1354,f105])).
% 13.70/2.11  fof(f1354,plain,(
% 13.70/2.11    ( ! [X6,X4,X7,X5] : (k2_enumset1(X6,X7,X4,X5) = k2_enumset1(X7,X6,X4,X5)) )),
% 13.70/2.11    inference(superposition,[],[f340,f342])).
% 13.70/2.11  fof(f340,plain,(
% 13.70/2.11    ( ! [X6,X4,X5,X3] : (k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3)) = k2_enumset1(X4,X3,X5,X6)) )),
% 13.70/2.11    inference(backward_demodulation,[],[f219,f338])).
% 13.70/2.11  fof(f219,plain,(
% 13.70/2.11    ( ! [X6,X4,X5,X3] : (k3_enumset1(X5,X6,X3,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3))) )),
% 13.70/2.11    inference(superposition,[],[f88,f20])).
% 13.70/2.11  fof(f18,plain,(
% 13.70/2.11    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 13.70/2.11    inference(cnf_transformation,[],[f17])).
% 13.70/2.11  fof(f17,plain,(
% 13.70/2.11    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 13.70/2.11    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 13.70/2.11  fof(f16,plain,(
% 13.70/2.11    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 13.70/2.11    introduced(choice_axiom,[])).
% 14.02/2.13  fof(f15,plain,(
% 14.02/2.13    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 14.02/2.13    inference(ennf_transformation,[],[f14])).
% 14.02/2.13  fof(f14,negated_conjecture,(
% 14.02/2.13    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 14.02/2.13    inference(negated_conjecture,[],[f13])).
% 14.02/2.13  fof(f13,conjecture,(
% 14.02/2.13    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 14.02/2.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_mcart_1)).
% 14.02/2.13  % SZS output end Proof for theBenchmark
% 14.02/2.13  % (10797)------------------------------
% 14.02/2.13  % (10797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.02/2.13  % (10797)Termination reason: Refutation
% 14.02/2.13  
% 14.02/2.13  % (10797)Memory used [KB]: 23411
% 14.02/2.13  % (10797)Time elapsed: 1.683 s
% 14.02/2.13  % (10797)------------------------------
% 14.02/2.13  % (10797)------------------------------
% 14.02/2.13  % (10793)Success in time 1.773 s
%------------------------------------------------------------------------------
