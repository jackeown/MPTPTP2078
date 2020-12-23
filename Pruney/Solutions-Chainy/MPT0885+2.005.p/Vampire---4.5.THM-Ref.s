%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:01 EST 2020

% Result     : Theorem 10.02s
% Output     : Refutation 10.02s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 108 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :   55 ( 110 expanded)
%              Number of equality atoms :   54 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18155,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18154,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18154,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f18025,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f18025,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f9339,f814])).

fof(f814,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f803,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f803,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f142,f27])).

fof(f142,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f133,f27])).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f31,f27])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f9339,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f9234,f866])).

fof(f866,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X5,X7,X6) ),
    inference(superposition,[],[f379,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f379,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(forward_demodulation,[],[f363,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f87,f30])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f33,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f363,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X3,X2)) ),
    inference(superposition,[],[f89,f23])).

fof(f89,plain,(
    ! [X6,X4,X8,X7,X5] : k3_enumset1(X6,X7,X8,X4,X5) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X5,X4)) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f9234,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(superposition,[],[f20,f7014])).

fof(f7014,plain,(
    ! [X39,X37,X38,X36] : k2_enumset1(X36,X37,X39,X38) = k2_enumset1(X36,X38,X37,X39) ),
    inference(superposition,[],[f1658,f379])).

fof(f1658,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X12,X12,X13,X14,X15) = k2_enumset1(X12,X14,X13,X15) ),
    inference(forward_demodulation,[],[f1641,f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f115,f30])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(superposition,[],[f34,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f1641,plain,(
    ! [X14,X12,X15,X13] : k3_enumset1(X12,X12,X13,X14,X15) = k2_xboole_0(k1_enumset1(X12,X14,X13),k1_tarski(X15)) ),
    inference(superposition,[],[f34,f981])).

fof(f981,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(forward_demodulation,[],[f951,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(forward_demodulation,[],[f98,f26])).

fof(f98,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(superposition,[],[f97,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f951,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X2,X1)) ),
    inference(superposition,[],[f104,f21])).

fof(f104,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X5,X6,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3)) ),
    inference(superposition,[],[f97,f22])).

fof(f20,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (19453)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (19454)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (19462)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (19450)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (19456)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (19451)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (19463)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (19462)Refutation not found, incomplete strategy% (19462)------------------------------
% 0.20/0.48  % (19462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (19462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (19462)Memory used [KB]: 10618
% 0.20/0.48  % (19462)Time elapsed: 0.076 s
% 0.20/0.48  % (19462)------------------------------
% 0.20/0.48  % (19462)------------------------------
% 0.20/0.48  % (19466)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (19461)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (19464)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (19458)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (19468)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (19455)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (19457)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (19452)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (19465)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.51  % (19467)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (19459)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 5.24/1.07  % (19454)Time limit reached!
% 5.24/1.07  % (19454)------------------------------
% 5.24/1.07  % (19454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.07  % (19454)Termination reason: Time limit
% 5.24/1.07  
% 5.24/1.07  % (19454)Memory used [KB]: 11513
% 5.24/1.07  % (19454)Time elapsed: 0.630 s
% 5.24/1.07  % (19454)------------------------------
% 5.24/1.07  % (19454)------------------------------
% 10.02/1.66  % (19453)Refutation found. Thanks to Tanya!
% 10.02/1.66  % SZS status Theorem for theBenchmark
% 10.02/1.67  % SZS output start Proof for theBenchmark
% 10.02/1.67  fof(f18155,plain,(
% 10.02/1.67    $false),
% 10.02/1.67    inference(subsumption_resolution,[],[f18154,f25])).
% 10.02/1.67  fof(f25,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 10.02/1.67    inference(cnf_transformation,[],[f14])).
% 10.02/1.67  fof(f14,axiom,(
% 10.02/1.67    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 10.02/1.67  fof(f18154,plain,(
% 10.02/1.67    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 10.02/1.67    inference(forward_demodulation,[],[f18025,f28])).
% 10.02/1.67  fof(f28,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 10.02/1.67    inference(cnf_transformation,[],[f12])).
% 10.02/1.67  fof(f12,axiom,(
% 10.02/1.67    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 10.02/1.67  fof(f18025,plain,(
% 10.02/1.67    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 10.02/1.67    inference(superposition,[],[f9339,f814])).
% 10.02/1.67  fof(f814,plain,(
% 10.02/1.67    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 10.02/1.67    inference(forward_demodulation,[],[f803,f27])).
% 10.02/1.67  fof(f27,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 10.02/1.67    inference(cnf_transformation,[],[f13])).
% 10.02/1.67  fof(f13,axiom,(
% 10.02/1.67    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 10.02/1.67  fof(f803,plain,(
% 10.02/1.67    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 10.02/1.67    inference(superposition,[],[f142,f27])).
% 10.02/1.67  fof(f142,plain,(
% 10.02/1.67    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 10.02/1.67    inference(forward_demodulation,[],[f133,f27])).
% 10.02/1.67  fof(f133,plain,(
% 10.02/1.67    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 10.02/1.67    inference(superposition,[],[f31,f27])).
% 10.02/1.67  fof(f31,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 10.02/1.67    inference(cnf_transformation,[],[f11])).
% 10.02/1.67  fof(f11,axiom,(
% 10.02/1.67    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 10.02/1.67  fof(f9339,plain,(
% 10.02/1.67    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 10.02/1.67    inference(superposition,[],[f9234,f866])).
% 10.02/1.67  fof(f866,plain,(
% 10.02/1.67    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X4,X5,X7,X6)) )),
% 10.02/1.67    inference(superposition,[],[f379,f30])).
% 10.02/1.67  fof(f30,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 10.02/1.67    inference(cnf_transformation,[],[f7])).
% 10.02/1.67  fof(f7,axiom,(
% 10.02/1.67    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 10.02/1.67  fof(f379,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 10.02/1.67    inference(forward_demodulation,[],[f363,f97])).
% 10.02/1.67  fof(f97,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 10.02/1.67    inference(forward_demodulation,[],[f87,f30])).
% 10.02/1.67  fof(f87,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 10.02/1.67    inference(superposition,[],[f33,f23])).
% 10.02/1.67  fof(f23,plain,(
% 10.02/1.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 10.02/1.67    inference(cnf_transformation,[],[f5])).
% 10.02/1.67  fof(f5,axiom,(
% 10.02/1.67    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 10.02/1.67  fof(f33,plain,(
% 10.02/1.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 10.02/1.67    inference(cnf_transformation,[],[f2])).
% 10.02/1.67  fof(f2,axiom,(
% 10.02/1.67    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 10.02/1.67  fof(f363,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X3,X2))) )),
% 10.02/1.67    inference(superposition,[],[f89,f23])).
% 10.02/1.67  fof(f89,plain,(
% 10.02/1.67    ( ! [X6,X4,X8,X7,X5] : (k3_enumset1(X6,X7,X8,X4,X5) = k2_xboole_0(k1_enumset1(X6,X7,X8),k2_tarski(X5,X4))) )),
% 10.02/1.67    inference(superposition,[],[f33,f22])).
% 10.02/1.67  fof(f22,plain,(
% 10.02/1.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 10.02/1.67    inference(cnf_transformation,[],[f1])).
% 10.02/1.67  fof(f1,axiom,(
% 10.02/1.67    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 10.02/1.67  fof(f9234,plain,(
% 10.02/1.67    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3))),
% 10.02/1.67    inference(superposition,[],[f20,f7014])).
% 10.02/1.67  fof(f7014,plain,(
% 10.02/1.67    ( ! [X39,X37,X38,X36] : (k2_enumset1(X36,X37,X39,X38) = k2_enumset1(X36,X38,X37,X39)) )),
% 10.02/1.67    inference(superposition,[],[f1658,f379])).
% 10.02/1.67  fof(f1658,plain,(
% 10.02/1.67    ( ! [X14,X12,X15,X13] : (k3_enumset1(X12,X12,X13,X14,X15) = k2_enumset1(X12,X14,X13,X15)) )),
% 10.02/1.67    inference(forward_demodulation,[],[f1641,f120])).
% 10.02/1.67  fof(f120,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 10.02/1.67    inference(forward_demodulation,[],[f115,f30])).
% 10.02/1.67  fof(f115,plain,(
% 10.02/1.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 10.02/1.67    inference(superposition,[],[f34,f26])).
% 10.02/1.67  fof(f26,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 10.02/1.67    inference(cnf_transformation,[],[f6])).
% 10.02/1.67  fof(f6,axiom,(
% 10.02/1.67    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 10.02/1.67  fof(f34,plain,(
% 10.02/1.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 10.02/1.67    inference(cnf_transformation,[],[f3])).
% 10.02/1.67  fof(f3,axiom,(
% 10.02/1.67    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 10.02/1.67  fof(f1641,plain,(
% 10.02/1.67    ( ! [X14,X12,X15,X13] : (k3_enumset1(X12,X12,X13,X14,X15) = k2_xboole_0(k1_enumset1(X12,X14,X13),k1_tarski(X15))) )),
% 10.02/1.67    inference(superposition,[],[f34,f981])).
% 10.02/1.67  fof(f981,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 10.02/1.67    inference(forward_demodulation,[],[f951,f114])).
% 10.02/1.67  fof(f114,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 10.02/1.67    inference(forward_demodulation,[],[f98,f26])).
% 10.02/1.67  fof(f98,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 10.02/1.67    inference(superposition,[],[f97,f21])).
% 10.02/1.67  fof(f21,plain,(
% 10.02/1.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 10.02/1.67    inference(cnf_transformation,[],[f4])).
% 10.02/1.67  fof(f4,axiom,(
% 10.02/1.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 10.02/1.67  fof(f951,plain,(
% 10.02/1.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X2,X1))) )),
% 10.02/1.67    inference(superposition,[],[f104,f21])).
% 10.02/1.67  fof(f104,plain,(
% 10.02/1.67    ( ! [X6,X4,X5,X3] : (k2_enumset1(X5,X6,X3,X4) = k2_xboole_0(k2_tarski(X5,X6),k2_tarski(X4,X3))) )),
% 10.02/1.67    inference(superposition,[],[f97,f22])).
% 10.02/1.67  fof(f20,plain,(
% 10.02/1.67    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 10.02/1.67    inference(cnf_transformation,[],[f19])).
% 10.02/1.67  fof(f19,plain,(
% 10.02/1.67    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 10.02/1.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 10.02/1.67  fof(f18,plain,(
% 10.02/1.67    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 10.02/1.67    introduced(choice_axiom,[])).
% 10.02/1.67  fof(f17,plain,(
% 10.02/1.67    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 10.02/1.67    inference(ennf_transformation,[],[f16])).
% 10.02/1.67  fof(f16,negated_conjecture,(
% 10.02/1.67    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 10.02/1.67    inference(negated_conjecture,[],[f15])).
% 10.02/1.67  fof(f15,conjecture,(
% 10.02/1.67    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 10.02/1.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 10.02/1.67  % SZS output end Proof for theBenchmark
% 10.02/1.67  % (19453)------------------------------
% 10.02/1.67  % (19453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.02/1.67  % (19453)Termination reason: Refutation
% 10.02/1.67  
% 10.02/1.67  % (19453)Memory used [KB]: 21364
% 10.02/1.67  % (19453)Time elapsed: 1.229 s
% 10.02/1.67  % (19453)------------------------------
% 10.02/1.67  % (19453)------------------------------
% 10.02/1.68  % (19445)Success in time 1.316 s
%------------------------------------------------------------------------------
