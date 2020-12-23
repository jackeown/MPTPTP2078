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
% DateTime   : Thu Dec  3 12:32:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  61 expanded)
%              Number of leaves         :    8 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :   34 (  62 expanded)
%              Number of equality atoms :   33 (  61 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f130,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f128,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f128,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f105,f14])).

fof(f105,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
    inference(backward_demodulation,[],[f19,f76])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f53,f28])).

fof(f28,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f26,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f22,f14])).

fof(f22,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f20,f13])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f45,f13])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f21,f42])).

fof(f42,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X8)) = X7 ),
    inference(forward_demodulation,[],[f34,f26])).

fof(f34,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,k4_xboole_0(X8,X8)) ),
    inference(superposition,[],[f21,f14])).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f18,f15])).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
    inference(definition_unfolding,[],[f12,f17])).

fof(f17,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f12,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:11:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (17820)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.46  % (17823)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (17821)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (17824)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (17823)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f130,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f129])).
% 0.22/0.47  fof(f129,plain,(
% 0.22/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(superposition,[],[f128,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f128,plain,(
% 0.22/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.47    inference(superposition,[],[f105,f14])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))),
% 0.22/0.47    inference(backward_demodulation,[],[f19,f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.22/0.47    inference(forward_demodulation,[],[f53,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 0.22/0.47    inference(superposition,[],[f26,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 0.22/0.47    inference(superposition,[],[f22,f14])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 0.22/0.47    inference(superposition,[],[f20,f13])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(definition_unfolding,[],[f16,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f45,f13])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(superposition,[],[f21,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X8)) = X7) )),
% 0.22/0.47    inference(forward_demodulation,[],[f34,f26])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,k4_xboole_0(X8,X8))) )),
% 0.22/0.47    inference(superposition,[],[f21,f14])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f18,f15])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))),
% 0.22/0.47    inference(definition_unfolding,[],[f12,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (17823)------------------------------
% 0.22/0.47  % (17823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (17823)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (17823)Memory used [KB]: 6140
% 0.22/0.47  % (17823)Time elapsed: 0.038 s
% 0.22/0.47  % (17823)------------------------------
% 0.22/0.47  % (17823)------------------------------
% 0.22/0.47  % (17822)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (17818)Success in time 0.113 s
%------------------------------------------------------------------------------
