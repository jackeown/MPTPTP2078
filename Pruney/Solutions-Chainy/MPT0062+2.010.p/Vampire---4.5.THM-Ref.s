%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  49 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :   25 (  50 expanded)
%              Number of equality atoms :   24 (  49 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f212,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f199])).

fof(f199,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f15,f86])).

fof(f86,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f85,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f13,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f85,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X6))),k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f70,f16])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f70,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(k4_xboole_0(X7,X6),X7)),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f34,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f17,f16])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f14,f16])).

fof(f14,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f15,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f10,f12])).

fof(f10,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:34:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (12076)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (12077)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (12077)Refutation not found, incomplete strategy% (12077)------------------------------
% 0.22/0.47  % (12077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12077)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (12077)Memory used [KB]: 10490
% 0.22/0.47  % (12077)Time elapsed: 0.057 s
% 0.22/0.47  % (12077)------------------------------
% 0.22/0.47  % (12077)------------------------------
% 0.22/0.47  % (12073)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (12068)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (12067)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (12067)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f212,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f199])).
% 0.22/0.47  fof(f199,plain,(
% 0.22/0.47    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.22/0.47    inference(superposition,[],[f15,f86])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(X6,X7))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f85,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f13,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,k4_xboole_0(X7,X6))),k4_xboole_0(X6,X7))) )),
% 0.22/0.47    inference(forward_demodulation,[],[f70,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f11,f12,f12])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X7,X6),k4_xboole_0(X7,k4_xboole_0(X7,X6))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X7,X6),k4_xboole_0(k4_xboole_0(X7,X6),X7)),k4_xboole_0(X6,X7))) )),
% 0.22/0.47    inference(superposition,[],[f34,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.22/0.47    inference(superposition,[],[f17,f16])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X0,X1)))) )),
% 0.22/0.47    inference(superposition,[],[f14,f16])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.47    inference(definition_unfolding,[],[f10,f12])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f5])).
% 0.22/0.47  fof(f5,conjecture,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (12067)------------------------------
% 0.22/0.47  % (12067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (12067)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (12067)Memory used [KB]: 6268
% 0.22/0.47  % (12067)Time elapsed: 0.055 s
% 0.22/0.47  % (12067)------------------------------
% 0.22/0.47  % (12067)------------------------------
% 0.22/0.47  % (12072)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (12060)Success in time 0.113 s
%------------------------------------------------------------------------------
