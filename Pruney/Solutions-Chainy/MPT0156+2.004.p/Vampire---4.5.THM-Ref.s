%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   25 (  63 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   26 (  64 expanded)
%              Number of equality atoms :   25 (  63 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) ),
    inference(superposition,[],[f33,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f23,f29,f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f22,f19,f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f21,f19,f18,f18])).

% (23915)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f28,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f33,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f16,f27,f29])).

fof(f16,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (23909)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (23906)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (23913)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (23910)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (23906)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (23920)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (23914)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (23916)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))),
% 0.20/0.47    inference(superposition,[],[f33,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X0,X1,X2)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f23,f29,f19,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X1,X2),k4_xboole_0(k1_enumset1(X3,X3,X4),k1_enumset1(X1,X1,X2))),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f22,f19,f28,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X3),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f21,f19,f18,f18])).
% 0.20/0.47  % (23915)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f17,f18])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k4_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1))),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.47    inference(definition_unfolding,[],[f16,f27,f29])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (23906)------------------------------
% 0.20/0.47  % (23906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (23906)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (23906)Memory used [KB]: 1663
% 0.20/0.47  % (23906)Time elapsed: 0.053 s
% 0.20/0.47  % (23906)------------------------------
% 0.20/0.47  % (23906)------------------------------
% 0.20/0.47  % (23904)Success in time 0.114 s
%------------------------------------------------------------------------------
