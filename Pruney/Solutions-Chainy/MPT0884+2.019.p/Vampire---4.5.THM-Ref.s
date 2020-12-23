%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:57 EST 2020

% Result     : Theorem 4.54s
% Output     : Refutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  73 expanded)
%              Number of equality atoms :   50 (  72 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10160,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f10160,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f10159,f196])).

fof(f196,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X2),k1_tarski(X1)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)) ),
    inference(forward_demodulation,[],[f195,f23])).

fof(f23,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f195,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X1)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1)) ),
    inference(forward_demodulation,[],[f184,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0) ),
    inference(forward_demodulation,[],[f62,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0) ),
    inference(superposition,[],[f31,f23])).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f184,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X1)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X2,X1),k4_tarski(X2,X1)) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f10159,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f10114,f702])).

fof(f702,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f686,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f686,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f188,f29])).

fof(f188,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f177,f29])).

fof(f177,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f36,f29])).

fof(f10114,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(superposition,[],[f9914,f7404])).

fof(f7404,plain,(
    ! [X14,X12,X15,X13] : k2_enumset1(X12,X13,X14,X15) = k2_enumset1(X12,X13,X15,X14) ),
    inference(superposition,[],[f95,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f95,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X5,X6,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3)) ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f40,f27])).

fof(f40,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f9914,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3)) ),
    inference(superposition,[],[f22,f7780])).

fof(f7780,plain,(
    ! [X10,X8,X11,X9] : k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X8,X10,X11,X9) ),
    inference(superposition,[],[f149,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f149,plain,(
    ! [X14,X15,X13,X16] : k2_enumset1(X16,X13,X14,X15) = k2_xboole_0(k1_tarski(X16),k1_enumset1(X15,X13,X14)) ),
    inference(superposition,[],[f33,f120])).

fof(f120,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4) ),
    inference(superposition,[],[f65,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f65,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5) ),
    inference(superposition,[],[f31,f24])).

fof(f22,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (31740)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (31738)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (31751)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (31748)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (31739)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (31743)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (31755)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (31741)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (31747)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (31750)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (31753)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (31754)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (31756)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (31749)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.51  % (31749)Refutation not found, incomplete strategy% (31749)------------------------------
% 0.21/0.51  % (31749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31749)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31749)Memory used [KB]: 10618
% 0.21/0.51  % (31749)Time elapsed: 0.054 s
% 0.21/0.51  % (31749)------------------------------
% 0.21/0.51  % (31749)------------------------------
% 0.21/0.51  % (31744)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (31742)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (31746)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (31745)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 4.54/0.95  % (31741)Refutation found. Thanks to Tanya!
% 4.54/0.95  % SZS status Theorem for theBenchmark
% 4.54/0.95  % SZS output start Proof for theBenchmark
% 4.54/0.95  fof(f10161,plain,(
% 4.54/0.95    $false),
% 4.54/0.95    inference(subsumption_resolution,[],[f10160,f28])).
% 4.54/0.95  fof(f28,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 4.54/0.95    inference(cnf_transformation,[],[f16])).
% 4.54/0.95  fof(f16,axiom,(
% 4.54/0.95    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 4.54/0.95  fof(f10160,plain,(
% 4.54/0.95    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_tarski(sK3,sK4))),
% 4.54/0.95    inference(forward_demodulation,[],[f10159,f196])).
% 4.54/0.95  fof(f196,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X2),k1_tarski(X1)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1))) )),
% 4.54/0.95    inference(forward_demodulation,[],[f195,f23])).
% 4.54/0.95  fof(f23,plain,(
% 4.54/0.95    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 4.54/0.95    inference(cnf_transformation,[],[f10])).
% 4.54/0.95  fof(f10,axiom,(
% 4.54/0.95    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 4.54/0.95  fof(f195,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X1)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X1))) )),
% 4.54/0.95    inference(forward_demodulation,[],[f184,f69])).
% 4.54/0.95  fof(f69,plain,(
% 4.54/0.95    ( ! [X0,X1] : (k2_tarski(X1,X0) = k1_enumset1(X1,X0,X0)) )),
% 4.54/0.95    inference(forward_demodulation,[],[f62,f27])).
% 4.54/0.95  fof(f27,plain,(
% 4.54/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 4.54/0.95    inference(cnf_transformation,[],[f3])).
% 4.54/0.95  fof(f3,axiom,(
% 4.54/0.95    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 4.54/0.95  fof(f62,plain,(
% 4.54/0.95    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) = k1_enumset1(X1,X0,X0)) )),
% 4.54/0.95    inference(superposition,[],[f31,f23])).
% 4.54/0.95  fof(f31,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 4.54/0.95    inference(cnf_transformation,[],[f4])).
% 4.54/0.95  fof(f4,axiom,(
% 4.54/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 4.54/0.95  fof(f184,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X1)) = k1_enumset1(k4_tarski(X0,X1),k4_tarski(X2,X1),k4_tarski(X2,X1))) )),
% 4.54/0.95    inference(superposition,[],[f30,f36])).
% 4.54/0.95  fof(f36,plain,(
% 4.54/0.95    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 4.54/0.95    inference(cnf_transformation,[],[f14])).
% 4.54/0.95  fof(f14,axiom,(
% 4.54/0.95    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 4.54/0.95  fof(f30,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.54/0.95    inference(cnf_transformation,[],[f12])).
% 4.54/0.95  fof(f12,axiom,(
% 4.54/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.54/0.95  fof(f10159,plain,(
% 4.54/0.95    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 4.54/0.95    inference(superposition,[],[f10114,f702])).
% 4.54/0.95  fof(f702,plain,(
% 4.54/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 4.54/0.95    inference(forward_demodulation,[],[f686,f29])).
% 4.54/0.95  fof(f29,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 4.54/0.95    inference(cnf_transformation,[],[f15])).
% 4.54/0.95  fof(f15,axiom,(
% 4.54/0.95    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 4.54/0.95  fof(f686,plain,(
% 4.54/0.95    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 4.54/0.95    inference(superposition,[],[f188,f29])).
% 4.54/0.95  fof(f188,plain,(
% 4.54/0.95    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 4.54/0.95    inference(forward_demodulation,[],[f177,f29])).
% 4.54/0.95  fof(f177,plain,(
% 4.54/0.95    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 4.54/0.95    inference(superposition,[],[f36,f29])).
% 4.54/0.95  fof(f10114,plain,(
% 4.54/0.95    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))),
% 4.54/0.95    inference(superposition,[],[f9914,f7404])).
% 4.54/0.95  fof(f7404,plain,(
% 4.54/0.95    ( ! [X14,X12,X15,X13] : (k2_enumset1(X12,X13,X14,X15) = k2_enumset1(X12,X13,X15,X14)) )),
% 4.54/0.95    inference(superposition,[],[f95,f34])).
% 4.54/0.95  fof(f34,plain,(
% 4.54/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 4.54/0.95    inference(cnf_transformation,[],[f2])).
% 4.54/0.95  fof(f2,axiom,(
% 4.54/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 4.54/0.95  fof(f95,plain,(
% 4.54/0.95    ( ! [X6,X4,X5,X3] : (k2_enumset1(X5,X6,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3))) )),
% 4.54/0.95    inference(superposition,[],[f34,f50])).
% 4.54/0.95  fof(f50,plain,(
% 4.54/0.95    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 4.54/0.95    inference(superposition,[],[f40,f27])).
% 4.54/0.95  fof(f40,plain,(
% 4.54/0.95    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X3),k1_tarski(X2))) )),
% 4.54/0.95    inference(superposition,[],[f27,f24])).
% 4.54/0.95  fof(f24,plain,(
% 4.54/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.54/0.95    inference(cnf_transformation,[],[f1])).
% 4.54/0.95  fof(f1,axiom,(
% 4.54/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.54/0.95  fof(f9914,plain,(
% 4.54/0.95    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3))),
% 4.54/0.95    inference(superposition,[],[f22,f7780])).
% 4.54/0.95  fof(f7780,plain,(
% 4.54/0.95    ( ! [X10,X8,X11,X9] : (k2_enumset1(X8,X9,X10,X11) = k2_enumset1(X8,X10,X11,X9)) )),
% 4.54/0.95    inference(superposition,[],[f149,f33])).
% 4.54/0.95  fof(f33,plain,(
% 4.54/0.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 4.54/0.95    inference(cnf_transformation,[],[f6])).
% 4.54/0.95  fof(f6,axiom,(
% 4.54/0.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 4.54/0.95  fof(f149,plain,(
% 4.54/0.95    ( ! [X14,X15,X13,X16] : (k2_enumset1(X16,X13,X14,X15) = k2_xboole_0(k1_tarski(X16),k1_enumset1(X15,X13,X14))) )),
% 4.54/0.95    inference(superposition,[],[f33,f120])).
% 4.54/0.95  fof(f120,plain,(
% 4.54/0.95    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X5,X3,X4)) )),
% 4.54/0.95    inference(superposition,[],[f65,f32])).
% 4.54/0.95  fof(f32,plain,(
% 4.54/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 4.54/0.95    inference(cnf_transformation,[],[f5])).
% 4.54/0.95  fof(f5,axiom,(
% 4.54/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 4.54/0.95  fof(f65,plain,(
% 4.54/0.95    ( ! [X4,X5,X3] : (k2_xboole_0(k2_tarski(X4,X5),k1_tarski(X3)) = k1_enumset1(X3,X4,X5)) )),
% 4.54/0.95    inference(superposition,[],[f31,f24])).
% 4.54/0.95  fof(f22,plain,(
% 4.54/0.95    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 4.54/0.95    inference(cnf_transformation,[],[f21])).
% 4.54/0.95  fof(f21,plain,(
% 4.54/0.95    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 4.54/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).
% 4.54/0.95  fof(f20,plain,(
% 4.54/0.95    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 4.54/0.95    introduced(choice_axiom,[])).
% 4.54/0.95  fof(f19,plain,(
% 4.54/0.95    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 4.54/0.95    inference(ennf_transformation,[],[f18])).
% 4.54/0.95  fof(f18,negated_conjecture,(
% 4.54/0.95    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 4.54/0.95    inference(negated_conjecture,[],[f17])).
% 4.54/0.95  fof(f17,conjecture,(
% 4.54/0.95    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 4.54/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 4.54/0.95  % SZS output end Proof for theBenchmark
% 4.54/0.95  % (31741)------------------------------
% 4.54/0.95  % (31741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.54/0.95  % (31741)Termination reason: Refutation
% 4.54/0.95  
% 4.54/0.95  % (31741)Memory used [KB]: 8059
% 4.54/0.95  % (31741)Time elapsed: 0.530 s
% 4.54/0.95  % (31741)------------------------------
% 4.54/0.95  % (31741)------------------------------
% 4.54/0.95  % (31735)Success in time 0.592 s
%------------------------------------------------------------------------------
