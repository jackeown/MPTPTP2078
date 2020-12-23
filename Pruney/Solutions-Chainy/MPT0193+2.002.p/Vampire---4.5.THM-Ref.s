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
% DateTime   : Thu Dec  3 12:34:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   17 (  23 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(forward_demodulation,[],[f25,f10])).

fof(f10,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f25,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f13,f14])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X3,X1)) ),
    inference(definition_unfolding,[],[f11,f12,f12])).

% (5687)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f12,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f13,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK0,sK2)) ),
    inference(definition_unfolding,[],[f9,f12,f12])).

fof(f9,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (5690)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (5692)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (5692)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.47    inference(forward_demodulation,[],[f25,f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK3))),
% 0.22/0.47    inference(superposition,[],[f13,f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X3,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f11,f12,f12])).
% 0.22/0.47  % (5687)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_xboole_0(k2_tarski(sK1,sK3),k2_tarski(sK0,sK2))),
% 0.22/0.47    inference(definition_unfolding,[],[f9,f12,f12])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK3,sK0,sK2)),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.47    inference(negated_conjecture,[],[f4])).
% 0.22/0.47  fof(f4,conjecture,(
% 0.22/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (5692)------------------------------
% 0.22/0.47  % (5692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (5692)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (5692)Memory used [KB]: 6012
% 0.22/0.47  % (5692)Time elapsed: 0.052 s
% 0.22/0.47  % (5692)------------------------------
% 0.22/0.47  % (5692)------------------------------
% 0.22/0.47  % (5684)Success in time 0.11 s
%------------------------------------------------------------------------------
