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
% DateTime   : Thu Dec  3 12:34:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   22 (  30 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   23 (  31 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f28])).

fof(f28,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) ),
    inference(superposition,[],[f18,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5)) ),
    inference(forward_demodulation,[],[f22,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),X5) ),
    inference(superposition,[],[f11,f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f18,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) ),
    inference(backward_demodulation,[],[f16,f11])).

fof(f16,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(definition_unfolding,[],[f10,f15,f12])).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_enumset1(X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(f10,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:14:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (27446)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.42  % (27446)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)))),
% 0.21/0.42    inference(superposition,[],[f18,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_enumset1(X1,X2,X3,X4),X5))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f22,f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)),X5)) )),
% 0.21/0.42    inference(superposition,[],[f11,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f13,f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8)))),
% 0.21/0.42    inference(backward_demodulation,[],[f16,f11])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_xboole_0(k1_tarski(sK4),k2_enumset1(sK5,sK6,sK7,sK8))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k2_enumset1(sK5,sK6,sK7,sK8))),
% 0.21/0.42    inference(definition_unfolding,[],[f10,f15,f12])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_xboole_0(k1_tarski(X4),k2_enumset1(X5,X6,X7,X8)))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f14,f12])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f7,f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_enumset1(sK5,sK6,sK7,sK8))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (27446)------------------------------
% 0.21/0.42  % (27446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (27446)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (27446)Memory used [KB]: 10618
% 0.21/0.42  % (27446)Time elapsed: 0.005 s
% 0.21/0.42  % (27446)------------------------------
% 0.21/0.42  % (27446)------------------------------
% 0.21/0.42  % (27436)Success in time 0.058 s
%------------------------------------------------------------------------------
