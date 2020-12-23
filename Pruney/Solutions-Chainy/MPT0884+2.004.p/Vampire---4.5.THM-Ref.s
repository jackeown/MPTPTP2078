%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:55 EST 2020

% Result     : Theorem 28.57s
% Output     : Refutation 28.57s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 102 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   55 ( 104 expanded)
%              Number of equality atoms :   54 ( 103 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51533,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51532,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f51532,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f51327,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f51327,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f4046,f1092])).

fof(f1092,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1071,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1071,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f123,f24])).

fof(f123,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f114,f24])).

fof(f114,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f30,f24])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f4046,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f18,f3900])).

fof(f3900,plain,(
    ! [X14,X15,X13,X16] : k2_enumset1(X15,X13,X14,X16) = k2_enumset1(X15,X14,X13,X16) ),
    inference(superposition,[],[f222,f113])).

fof(f113,plain,(
    ! [X4,X2,X5,X3] : k3_enumset1(X2,X3,X4,X4,X5) = k2_enumset1(X4,X2,X3,X5) ),
    inference(forward_demodulation,[],[f112,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f104,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f104,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f31,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f112,plain,(
    ! [X4,X2,X5,X3] : k3_enumset1(X2,X3,X4,X4,X5) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5)) ),
    inference(superposition,[],[f31,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0) ),
    inference(backward_demodulation,[],[f45,f99])).

fof(f99,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f54,f40])).

fof(f40,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f42,f25])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f29,f19])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f29,f19])).

fof(f222,plain,(
    ! [X4,X2,X5,X3] : k3_enumset1(X2,X3,X4,X4,X5) = k2_enumset1(X4,X3,X2,X5) ),
    inference(forward_demodulation,[],[f217,f109])).

fof(f217,plain,(
    ! [X4,X2,X5,X3] : k3_enumset1(X2,X3,X4,X4,X5) = k2_xboole_0(k1_enumset1(X4,X3,X2),k1_tarski(X5)) ),
    inference(superposition,[],[f31,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X0,X2,X1) ),
    inference(forward_demodulation,[],[f162,f99])).

fof(f162,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X2,X1),k1_tarski(X0)) ),
    inference(superposition,[],[f43,f19])).

fof(f43,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f29,f20])).

fof(f18,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:44:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (15456)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (15453)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (15468)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (15465)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (15460)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (15451)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (15458)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (15454)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (15461)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (15455)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (15463)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (15452)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (15464)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (15462)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (15462)Refutation not found, incomplete strategy% (15462)------------------------------
% 0.22/0.51  % (15462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15462)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15462)Memory used [KB]: 10618
% 0.22/0.51  % (15462)Time elapsed: 0.091 s
% 0.22/0.51  % (15462)------------------------------
% 0.22/0.51  % (15462)------------------------------
% 0.22/0.51  % (15457)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (15459)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (15467)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (15466)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 5.35/1.03  % (15455)Time limit reached!
% 5.35/1.03  % (15455)------------------------------
% 5.35/1.03  % (15455)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.35/1.03  % (15455)Termination reason: Time limit
% 5.35/1.03  
% 5.35/1.03  % (15455)Memory used [KB]: 11257
% 5.35/1.03  % (15455)Time elapsed: 0.621 s
% 5.35/1.03  % (15455)------------------------------
% 5.35/1.03  % (15455)------------------------------
% 12.35/1.92  % (15456)Time limit reached!
% 12.35/1.92  % (15456)------------------------------
% 12.35/1.92  % (15456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.35/1.92  % (15456)Termination reason: Time limit
% 12.35/1.92  
% 12.35/1.92  % (15456)Memory used [KB]: 32622
% 12.35/1.92  % (15456)Time elapsed: 1.505 s
% 12.35/1.92  % (15456)------------------------------
% 12.35/1.92  % (15456)------------------------------
% 12.35/1.96  % (15457)Time limit reached!
% 12.35/1.96  % (15457)------------------------------
% 12.35/1.96  % (15457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.35/1.96  % (15457)Termination reason: Time limit
% 12.35/1.96  % (15457)Termination phase: Saturation
% 12.35/1.96  
% 12.35/1.96  % (15457)Memory used [KB]: 18038
% 12.35/1.96  % (15457)Time elapsed: 1.500 s
% 12.35/1.96  % (15457)------------------------------
% 12.35/1.96  % (15457)------------------------------
% 14.82/2.23  % (15453)Time limit reached!
% 14.82/2.23  % (15453)------------------------------
% 14.82/2.23  % (15453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.82/2.24  % (15453)Termination reason: Time limit
% 14.82/2.24  % (15453)Termination phase: Saturation
% 14.82/2.24  
% 14.82/2.24  % (15453)Memory used [KB]: 19573
% 14.82/2.24  % (15453)Time elapsed: 1.800 s
% 14.82/2.24  % (15453)------------------------------
% 14.82/2.24  % (15453)------------------------------
% 17.78/2.61  % (15463)Time limit reached!
% 17.78/2.61  % (15463)------------------------------
% 17.78/2.61  % (15463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.78/2.61  % (15463)Termination reason: Time limit
% 17.78/2.61  % (15463)Termination phase: Saturation
% 17.78/2.61  
% 17.78/2.62  % (15463)Memory used [KB]: 19573
% 17.78/2.62  % (15463)Time elapsed: 2.200 s
% 17.78/2.62  % (15463)------------------------------
% 17.78/2.62  % (15463)------------------------------
% 28.57/3.98  % (15454)Refutation found. Thanks to Tanya!
% 28.57/3.98  % SZS status Theorem for theBenchmark
% 28.57/3.98  % SZS output start Proof for theBenchmark
% 28.57/3.98  fof(f51533,plain,(
% 28.57/3.98    $false),
% 28.57/3.98    inference(subsumption_resolution,[],[f51532,f23])).
% 28.57/3.98  fof(f23,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 28.57/3.98    inference(cnf_transformation,[],[f12])).
% 28.57/3.98  fof(f12,axiom,(
% 28.57/3.98    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 28.57/3.98  fof(f51532,plain,(
% 28.57/3.98    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 28.57/3.98    inference(forward_demodulation,[],[f51327,f27])).
% 28.57/3.98  fof(f27,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 28.57/3.98    inference(cnf_transformation,[],[f10])).
% 28.57/3.98  fof(f10,axiom,(
% 28.57/3.98    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 28.57/3.98  fof(f51327,plain,(
% 28.57/3.98    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 28.57/3.98    inference(superposition,[],[f4046,f1092])).
% 28.57/3.98  fof(f1092,plain,(
% 28.57/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 28.57/3.98    inference(forward_demodulation,[],[f1071,f24])).
% 28.57/3.98  fof(f24,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 28.57/3.98    inference(cnf_transformation,[],[f11])).
% 28.57/3.98  fof(f11,axiom,(
% 28.57/3.98    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 28.57/3.98  fof(f1071,plain,(
% 28.57/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 28.57/3.98    inference(superposition,[],[f123,f24])).
% 28.57/3.98  fof(f123,plain,(
% 28.57/3.98    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 28.57/3.98    inference(forward_demodulation,[],[f114,f24])).
% 28.57/3.98  fof(f114,plain,(
% 28.57/3.98    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 28.57/3.98    inference(superposition,[],[f30,f24])).
% 28.57/3.98  fof(f30,plain,(
% 28.57/3.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 28.57/3.98    inference(cnf_transformation,[],[f9])).
% 28.57/3.98  fof(f9,axiom,(
% 28.57/3.98    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 28.57/3.98  fof(f4046,plain,(
% 28.57/3.98    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 28.57/3.98    inference(superposition,[],[f18,f3900])).
% 28.57/3.98  fof(f3900,plain,(
% 28.57/3.98    ( ! [X14,X15,X13,X16] : (k2_enumset1(X15,X13,X14,X16) = k2_enumset1(X15,X14,X13,X16)) )),
% 28.57/3.98    inference(superposition,[],[f222,f113])).
% 28.57/3.98  fof(f113,plain,(
% 28.57/3.98    ( ! [X4,X2,X5,X3] : (k3_enumset1(X2,X3,X4,X4,X5) = k2_enumset1(X4,X2,X3,X5)) )),
% 28.57/3.98    inference(forward_demodulation,[],[f112,f109])).
% 28.57/3.98  fof(f109,plain,(
% 28.57/3.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 28.57/3.98    inference(forward_demodulation,[],[f104,f28])).
% 28.57/3.98  fof(f28,plain,(
% 28.57/3.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 28.57/3.98    inference(cnf_transformation,[],[f7])).
% 28.57/3.98  fof(f7,axiom,(
% 28.57/3.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 28.57/3.98  fof(f104,plain,(
% 28.57/3.98    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 28.57/3.98    inference(superposition,[],[f31,f25])).
% 28.57/3.98  fof(f25,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 28.57/3.98    inference(cnf_transformation,[],[f6])).
% 28.57/3.98  fof(f6,axiom,(
% 28.57/3.98    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 28.57/3.98  fof(f31,plain,(
% 28.57/3.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 28.57/3.98    inference(cnf_transformation,[],[f3])).
% 28.57/3.98  fof(f3,axiom,(
% 28.57/3.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 28.57/3.98  fof(f112,plain,(
% 28.57/3.98    ( ! [X4,X2,X5,X3] : (k3_enumset1(X2,X3,X4,X4,X5) = k2_xboole_0(k1_enumset1(X4,X2,X3),k1_tarski(X5))) )),
% 28.57/3.98    inference(superposition,[],[f31,f103])).
% 28.57/3.98  fof(f103,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X1,X2,X0,X0)) )),
% 28.57/3.98    inference(backward_demodulation,[],[f45,f99])).
% 28.57/3.98  fof(f99,plain,(
% 28.57/3.98    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) )),
% 28.57/3.98    inference(superposition,[],[f54,f40])).
% 28.57/3.98  fof(f40,plain,(
% 28.57/3.98    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 28.57/3.98    inference(superposition,[],[f33,f22])).
% 28.57/3.98  fof(f22,plain,(
% 28.57/3.98    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 28.57/3.98    inference(cnf_transformation,[],[f8])).
% 28.57/3.98  fof(f8,axiom,(
% 28.57/3.98    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 28.57/3.98  fof(f33,plain,(
% 28.57/3.98    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 28.57/3.98    inference(superposition,[],[f22,f20])).
% 28.57/3.98  fof(f20,plain,(
% 28.57/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 28.57/3.98    inference(cnf_transformation,[],[f1])).
% 28.57/3.98  fof(f1,axiom,(
% 28.57/3.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 28.57/3.98  fof(f54,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 28.57/3.98    inference(forward_demodulation,[],[f42,f25])).
% 28.57/3.98  fof(f42,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 28.57/3.98    inference(superposition,[],[f29,f19])).
% 28.57/3.98  fof(f19,plain,(
% 28.57/3.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 28.57/3.98    inference(cnf_transformation,[],[f4])).
% 28.57/3.98  fof(f4,axiom,(
% 28.57/3.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 28.57/3.98  fof(f29,plain,(
% 28.57/3.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 28.57/3.98    inference(cnf_transformation,[],[f2])).
% 28.57/3.98  fof(f2,axiom,(
% 28.57/3.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 28.57/3.98  fof(f45,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 28.57/3.98    inference(superposition,[],[f29,f19])).
% 28.57/3.98  fof(f222,plain,(
% 28.57/3.98    ( ! [X4,X2,X5,X3] : (k3_enumset1(X2,X3,X4,X4,X5) = k2_enumset1(X4,X3,X2,X5)) )),
% 28.57/3.98    inference(forward_demodulation,[],[f217,f109])).
% 28.57/3.98  fof(f217,plain,(
% 28.57/3.98    ( ! [X4,X2,X5,X3] : (k3_enumset1(X2,X3,X4,X4,X5) = k2_xboole_0(k1_enumset1(X4,X3,X2),k1_tarski(X5))) )),
% 28.57/3.98    inference(superposition,[],[f31,f176])).
% 28.57/3.98  fof(f176,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k1_enumset1(X0,X2,X1)) )),
% 28.57/3.98    inference(forward_demodulation,[],[f162,f99])).
% 28.57/3.98  fof(f162,plain,(
% 28.57/3.98    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X2,X1),k1_tarski(X0))) )),
% 28.57/3.98    inference(superposition,[],[f43,f19])).
% 28.57/3.98  fof(f43,plain,(
% 28.57/3.98    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6))) )),
% 28.57/3.98    inference(superposition,[],[f29,f20])).
% 28.57/3.98  fof(f18,plain,(
% 28.57/3.98    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 28.57/3.98    inference(cnf_transformation,[],[f17])).
% 28.57/3.98  fof(f17,plain,(
% 28.57/3.98    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 28.57/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 28.57/3.98  fof(f16,plain,(
% 28.57/3.98    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 28.57/3.98    introduced(choice_axiom,[])).
% 28.57/3.98  fof(f15,plain,(
% 28.57/3.98    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 28.57/3.98    inference(ennf_transformation,[],[f14])).
% 28.57/3.98  fof(f14,negated_conjecture,(
% 28.57/3.98    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 28.57/3.98    inference(negated_conjecture,[],[f13])).
% 28.57/3.98  fof(f13,conjecture,(
% 28.57/3.98    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 28.57/3.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
% 28.57/3.98  % SZS output end Proof for theBenchmark
% 28.57/3.98  % (15454)------------------------------
% 28.57/3.98  % (15454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.57/3.98  % (15454)Termination reason: Refutation
% 28.57/3.98  
% 28.57/3.98  % (15454)Memory used [KB]: 66651
% 28.57/3.98  % (15454)Time elapsed: 3.569 s
% 28.57/3.98  % (15454)------------------------------
% 28.57/3.98  % (15454)------------------------------
% 28.57/3.98  % (15450)Success in time 3.612 s
%------------------------------------------------------------------------------
