%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 ( 102 expanded)
%              Number of leaves         :    7 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   27 ( 103 expanded)
%              Number of equality atoms :   26 ( 102 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f80,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f68])).

fof(f68,plain,(
    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f19,f42])).

fof(f42,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X5,X5,X4,X6,X7) = k3_enumset1(X4,X4,X5,X7,X6) ),
    inference(superposition,[],[f24,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(superposition,[],[f21,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f12,f18,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f13,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f16,f15,f18,f18])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X2,X2,X3,X0,X1) = k2_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(superposition,[],[f21,f20])).

fof(f19,plain,(
    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK2,sK1) ),
    inference(definition_unfolding,[],[f11,f17,f17])).

fof(f11,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:45:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (25992)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (25992)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (25994)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (25996)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.22/0.51    inference(superposition,[],[f19,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X6,X4,X7,X5] : (k3_enumset1(X5,X5,X4,X6,X7) = k3_enumset1(X4,X4,X5,X7,X6)) )),
% 0.22/0.51    inference(superposition,[],[f24,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X1,X1,X1,X1,X0),k3_enumset1(X2,X2,X2,X2,X3))) )),
% 0.22/0.51    inference(superposition,[],[f21,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f12,f18,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f13,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f14,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X2,X3))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f16,f15,f18,f18])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X2,X2,X3,X0,X1) = k2_xboole_0(k3_enumset1(X2,X2,X2,X2,X3),k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.22/0.51    inference(superposition,[],[f21,f20])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK2,sK1)),
% 0.22/0.51    inference(definition_unfolding,[],[f11,f17,f17])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK2,sK1)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X0,X2,X1)),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.22/0.51    inference(negated_conjecture,[],[f6])).
% 0.22/0.51  fof(f6,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (25992)------------------------------
% 0.22/0.51  % (25992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25992)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (25992)Memory used [KB]: 6140
% 0.22/0.51  % (25992)Time elapsed: 0.068 s
% 0.22/0.51  % (25992)------------------------------
% 0.22/0.51  % (25992)------------------------------
% 0.22/0.51  % (25989)Success in time 0.146 s
%------------------------------------------------------------------------------
