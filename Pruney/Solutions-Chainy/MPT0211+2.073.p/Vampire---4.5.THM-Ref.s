%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:52 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 276 expanded)
%              Number of leaves         :   14 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :   50 ( 277 expanded)
%              Number of equality atoms :   49 ( 276 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1974,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1969])).

fof(f1969,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f1960,f291])).

fof(f291,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X2,X2,X3,X1) ),
    inference(superposition,[],[f80,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f30,f37,f35,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X3,X3,X3,X3,X0,X0,X1,X2) = k5_xboole_0(k1_tarski(X3),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1),k1_tarski(X3)))) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0) ),
    inference(definition_unfolding,[],[f26,f39,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f1960,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK2,sK0) ),
    inference(superposition,[],[f94,f125])).

fof(f125,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X2,X3,X4,X5,X6,X7,X0,X1) = k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7)))) ),
    inference(superposition,[],[f41,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f24,f39,f39])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f34,f35,f36,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f39])).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f94,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f93,f43])).

fof(f93,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1)))) ),
    inference(forward_demodulation,[],[f42,f43])).

fof(f42,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f39,f35,f40,f40])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (4945)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (4945)Refutation not found, incomplete strategy% (4945)------------------------------
% 0.20/0.41  % (4945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (4945)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (4945)Memory used [KB]: 10490
% 0.20/0.41  % (4945)Time elapsed: 0.003 s
% 0.20/0.41  % (4945)------------------------------
% 0.20/0.41  % (4945)------------------------------
% 0.20/0.44  % (4938)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.45  % (4944)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (4936)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (4935)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (4939)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (4950)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  % (4934)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (4946)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (4942)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (4947)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (4948)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (4943)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (4940)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (4941)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (4937)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (4951)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (4949)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.81/0.58  % (4938)Refutation found. Thanks to Tanya!
% 1.81/0.58  % SZS status Theorem for theBenchmark
% 1.81/0.58  % SZS output start Proof for theBenchmark
% 1.81/0.58  fof(f1974,plain,(
% 1.81/0.58    $false),
% 1.81/0.58    inference(trivial_inequality_removal,[],[f1969])).
% 1.81/0.58  fof(f1969,plain,(
% 1.81/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 1.81/0.58    inference(superposition,[],[f1960,f291])).
% 1.81/0.58  fof(f291,plain,(
% 1.81/0.58    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X2,X2,X3,X1)) )),
% 1.81/0.58    inference(superposition,[],[f80,f46])).
% 1.81/0.58  fof(f46,plain,(
% 1.81/0.58    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X2,X3,X4),k1_tarski(X0))))) )),
% 1.81/0.58    inference(definition_unfolding,[],[f30,f37,f35,f38])).
% 1.81/0.58  fof(f38,plain,(
% 1.81/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f28,f37])).
% 1.81/0.58  fof(f28,plain,(
% 1.81/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f10])).
% 1.81/0.58  fof(f10,axiom,(
% 1.81/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.81/0.58  fof(f35,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.81/0.58    inference(definition_unfolding,[],[f23,f22])).
% 1.81/0.58  fof(f22,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.81/0.58    inference(cnf_transformation,[],[f1])).
% 1.81/0.58  fof(f1,axiom,(
% 1.81/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.81/0.58  fof(f23,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.81/0.58    inference(cnf_transformation,[],[f2])).
% 1.81/0.58  fof(f2,axiom,(
% 1.81/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.81/0.58  fof(f37,plain,(
% 1.81/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f29,f36])).
% 1.81/0.58  fof(f36,plain,(
% 1.81/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f31,f33])).
% 1.81/0.58  fof(f33,plain,(
% 1.81/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f13])).
% 1.81/0.58  fof(f13,axiom,(
% 1.81/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.81/0.58  fof(f31,plain,(
% 1.81/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f12])).
% 1.81/0.58  fof(f12,axiom,(
% 1.81/0.58    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.81/0.58  fof(f29,plain,(
% 1.81/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f11])).
% 1.81/0.58  fof(f11,axiom,(
% 1.81/0.58    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.81/0.58  fof(f30,plain,(
% 1.81/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 1.81/0.58    inference(cnf_transformation,[],[f5])).
% 1.81/0.58  fof(f5,axiom,(
% 1.81/0.58    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 1.81/0.58  fof(f80,plain,(
% 1.81/0.58    ( ! [X2,X0,X3,X1] : (k6_enumset1(X3,X3,X3,X3,X0,X0,X1,X2) = k5_xboole_0(k1_tarski(X3),k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1),k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X0,X1),k1_tarski(X3))))) )),
% 1.81/0.58    inference(superposition,[],[f46,f45])).
% 1.81/0.58  fof(f45,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f26,f39,f39])).
% 1.81/0.58  fof(f39,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f27,f38])).
% 1.81/0.58  fof(f27,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f9])).
% 1.81/0.58  fof(f9,axiom,(
% 1.81/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.81/0.58  fof(f26,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f3])).
% 1.81/0.58  fof(f3,axiom,(
% 1.81/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 1.81/0.58  fof(f1960,plain,(
% 1.81/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK2,sK0)),
% 1.81/0.58    inference(superposition,[],[f94,f125])).
% 1.81/0.58  fof(f125,plain,(
% 1.81/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X2,X3,X4,X5,X6,X7,X0,X1) = k5_xboole_0(k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7),k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0),k3_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X0,X0),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))))) )),
% 1.81/0.58    inference(superposition,[],[f41,f43])).
% 1.81/0.58  fof(f43,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f24,f39,f39])).
% 1.81/0.58  fof(f24,plain,(
% 1.81/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f4])).
% 1.81/0.58  fof(f4,axiom,(
% 1.81/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 1.81/0.58  fof(f41,plain,(
% 1.81/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))))) )),
% 1.81/0.58    inference(definition_unfolding,[],[f34,f35,f36,f40])).
% 1.81/0.58  fof(f40,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.81/0.58    inference(definition_unfolding,[],[f21,f39])).
% 1.81/0.58  fof(f21,plain,(
% 1.81/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.81/0.58    inference(cnf_transformation,[],[f8])).
% 1.81/0.58  fof(f8,axiom,(
% 1.81/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.81/0.58  fof(f34,plain,(
% 1.81/0.58    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 1.81/0.58    inference(cnf_transformation,[],[f7])).
% 1.81/0.58  fof(f7,axiom,(
% 1.81/0.58    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 1.81/0.58  fof(f94,plain,(
% 1.81/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK2),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 1.81/0.58    inference(forward_demodulation,[],[f93,f43])).
% 1.81/0.58  fof(f93,plain,(
% 1.81/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK1))))),
% 1.81/0.58    inference(forward_demodulation,[],[f42,f43])).
% 1.81/0.58  fof(f42,plain,(
% 1.81/0.58    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0),k5_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))))),
% 1.81/0.58    inference(definition_unfolding,[],[f20,f39,f35,f40,f40])).
% 1.81/0.58  fof(f20,plain,(
% 1.81/0.58    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.81/0.58    inference(cnf_transformation,[],[f19])).
% 1.81/0.58  fof(f19,plain,(
% 1.81/0.58    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.81/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f18])).
% 1.81/0.58  fof(f18,plain,(
% 1.81/0.58    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.81/0.58    introduced(choice_axiom,[])).
% 1.81/0.58  fof(f17,plain,(
% 1.81/0.58    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.81/0.58    inference(ennf_transformation,[],[f16])).
% 1.81/0.58  fof(f16,negated_conjecture,(
% 1.81/0.58    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.81/0.58    inference(negated_conjecture,[],[f15])).
% 1.81/0.58  fof(f15,conjecture,(
% 1.81/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.81/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.81/0.58  % SZS output end Proof for theBenchmark
% 1.81/0.58  % (4938)------------------------------
% 1.81/0.58  % (4938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.58  % (4938)Termination reason: Refutation
% 1.81/0.58  
% 1.81/0.58  % (4938)Memory used [KB]: 8699
% 1.81/0.58  % (4938)Time elapsed: 0.170 s
% 1.81/0.58  % (4938)------------------------------
% 1.81/0.58  % (4938)------------------------------
% 1.81/0.58  % (4933)Success in time 0.23 s
%------------------------------------------------------------------------------
