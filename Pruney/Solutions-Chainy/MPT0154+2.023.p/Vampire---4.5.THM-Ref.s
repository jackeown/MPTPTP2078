%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  34 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :   27 (  35 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f263])).

fof(f263,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) ),
    inference(superposition,[],[f24,f235])).

fof(f235,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(forward_demodulation,[],[f233,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f233,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[],[f117,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f117,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0) ),
    inference(backward_demodulation,[],[f101,f116])).

fof(f116,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3) ),
    inference(forward_demodulation,[],[f115,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f115,plain,(
    ! [X4,X2,X3] : k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f38,f76])).

fof(f76,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0) ),
    inference(forward_demodulation,[],[f74,f33])).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0)) ),
    inference(superposition,[],[f36,f27])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f101,plain,(
    ! [X2,X0,X1] : k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) ),
    inference(superposition,[],[f39,f27])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:34:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22185)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (22181)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (22182)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (22182)Refutation not found, incomplete strategy% (22182)------------------------------
% 0.22/0.47  % (22182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22182)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (22182)Memory used [KB]: 10490
% 0.22/0.47  % (22182)Time elapsed: 0.050 s
% 0.22/0.47  % (22182)------------------------------
% 0.22/0.47  % (22182)------------------------------
% 0.22/0.48  % (22174)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (22176)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (22173)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (22174)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f267,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f263])).
% 0.22/0.48  fof(f263,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)),
% 0.22/0.48    inference(superposition,[],[f24,f235])).
% 0.22/0.48  fof(f235,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f233,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.48  fof(f233,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.48    inference(superposition,[],[f117,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,axiom,(
% 0.22/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)) = k1_enumset1(X1,X2,X0)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f101,f116])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k1_enumset1(X4,X2,X3)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f115,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X4,X2,X3] : (k2_enumset1(X4,X2,X3,X3) = k2_xboole_0(k1_tarski(X4),k2_tarski(X2,X3))) )),
% 0.22/0.48    inference(superposition,[],[f38,f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_tarski(X1,X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f74,f33])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_enumset1(X1,X0,X0) = k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) )),
% 0.22/0.48    inference(superposition,[],[f36,f27])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X1,X2,X0,X0) = k2_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) )),
% 0.22/0.48    inference(superposition,[],[f39,f27])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.22/0.48    inference(ennf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.48    inference(negated_conjecture,[],[f17])).
% 0.22/0.48  fof(f17,conjecture,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (22174)------------------------------
% 0.22/0.48  % (22174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (22174)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (22174)Memory used [KB]: 1791
% 0.22/0.48  % (22174)Time elapsed: 0.065 s
% 0.22/0.48  % (22174)------------------------------
% 0.22/0.48  % (22174)------------------------------
% 0.22/0.49  % (22170)Success in time 0.124 s
%------------------------------------------------------------------------------
