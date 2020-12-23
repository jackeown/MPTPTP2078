%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  23 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :    7
%              Number of atoms          :   20 (  24 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f21])).

fof(f21,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5)))) ),
    inference(superposition,[],[f17,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f17,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5)))) ),
    inference(definition_unfolding,[],[f10,f15,f16])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4))) ),
    inference(definition_unfolding,[],[f13,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f15,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)),k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5))) ),
    inference(definition_unfolding,[],[f14,f11,f11])).

fof(f14,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f10,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (8706)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (8706)Refutation not found, incomplete strategy% (8706)------------------------------
% 0.22/0.48  % (8706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8706)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (8706)Memory used [KB]: 10490
% 0.22/0.48  % (8706)Time elapsed: 0.026 s
% 0.22/0.48  % (8706)------------------------------
% 0.22/0.48  % (8706)------------------------------
% 0.22/0.48  % (8699)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (8699)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5))))),
% 0.22/0.48    inference(superposition,[],[f17,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k2_tarski(sK1,sK2),k2_xboole_0(k1_tarski(sK3),k2_tarski(sK4,sK5))))),
% 0.22/0.48    inference(definition_unfolding,[],[f10,f15,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k2_xboole_0(k1_tarski(X2),k2_tarski(X3,X4)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f13,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)),k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X5)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f14,f11,f11])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (8699)------------------------------
% 0.22/0.48  % (8699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (8699)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (8699)Memory used [KB]: 6012
% 0.22/0.48  % (8699)Time elapsed: 0.050 s
% 0.22/0.48  % (8699)------------------------------
% 0.22/0.48  % (8699)------------------------------
% 0.22/0.49  % (8694)Success in time 0.12 s
%------------------------------------------------------------------------------
