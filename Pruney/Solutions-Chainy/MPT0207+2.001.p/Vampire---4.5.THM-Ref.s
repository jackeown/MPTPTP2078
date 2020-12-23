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
% DateTime   : Thu Dec  3 12:34:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   22 (  57 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   23 (  58 expanded)
%              Number of equality atoms :   22 (  57 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X5,X6,X7,X8,X0,X1,X2,X3,X4) = k7_enumset1(X4,X5,X6,X7,X8,X0,X1,X2,X3) ),
    inference(superposition,[],[f35,f35])).

fof(f35,plain,(
    ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X14,X15,X16,X17,X9,X10,X11,X12,X13) ),
    inference(superposition,[],[f22,f14])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f22,plain,(
    ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k3_enumset1(X13,X14,X15,X16,X17),k2_enumset1(X9,X10,X11,X12)) ),
    inference(superposition,[],[f13,f11])).

fof(f11,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f13,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(f59,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK0) ),
    inference(superposition,[],[f50,f47])).

fof(f50,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK0,sK1) ),
    inference(superposition,[],[f19,f35])).

fof(f19,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(superposition,[],[f15,f12])).

fof(f12,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).

fof(f15,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k2_tarski(sK7,sK8),k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)) ),
    inference(superposition,[],[f10,f11])).

fof(f10,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (18352)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (18349)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (18355)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (18356)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (18361)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (18349)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f59,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X5,X6,X7,X8,X0,X1,X2,X3,X4) = k7_enumset1(X4,X5,X6,X7,X8,X0,X1,X2,X3)) )),
% 0.22/0.48    inference(superposition,[],[f35,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k7_enumset1(X14,X15,X16,X17,X9,X10,X11,X12,X13)) )),
% 0.22/0.48    inference(superposition,[],[f22,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k7_enumset1(X9,X10,X11,X12,X13,X14,X15,X16,X17) = k2_xboole_0(k3_enumset1(X13,X14,X15,X16,X17),k2_enumset1(X9,X10,X11,X12))) )),
% 0.22/0.48    inference(superposition,[],[f13,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK0)),
% 0.22/0.48    inference(superposition,[],[f50,f47])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK2,sK3,sK4,sK5,sK6,sK7,sK8,sK0,sK1)),
% 0.22/0.48    inference(superposition,[],[f19,f35])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k7_enumset1(sK7,sK8,sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 0.22/0.48    inference(superposition,[],[f15,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_tarski(X0,X1),k5_enumset1(X2,X3,X4,X5,X6,X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_enumset1)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k2_tarski(sK7,sK8),k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6))),
% 0.22/0.48    inference(superposition,[],[f10,f11])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6),k2_tarski(sK7,sK8))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k2_tarski(X7,X8))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (18349)------------------------------
% 0.22/0.48  % (18349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18349)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (18349)Memory used [KB]: 1663
% 0.22/0.48  % (18349)Time elapsed: 0.054 s
% 0.22/0.48  % (18349)------------------------------
% 0.22/0.48  % (18349)------------------------------
% 0.22/0.48  % (18345)Success in time 0.115 s
%------------------------------------------------------------------------------
