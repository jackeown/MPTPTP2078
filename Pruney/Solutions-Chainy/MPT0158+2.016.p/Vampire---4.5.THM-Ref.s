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
% DateTime   : Thu Dec  3 12:33:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  26 expanded)
%              Number of leaves         :    6 (   9 expanded)
%              Depth                    :    7
%              Number of atoms          :   21 (  27 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    inference(superposition,[],[f17,f18])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4)),k1_tarski(X5)) ),
    inference(definition_unfolding,[],[f13,f12,f15])).

fof(f15,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f11,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f12,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).

fof(f13,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).

fof(f17,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k1_tarski(sK5)) ),
    inference(definition_unfolding,[],[f10,f12,f16])).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)),k1_tarski(X6)) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f14,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f10,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (7987)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (7974)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (7987)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.21/0.46    inference(superposition,[],[f17,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4)),k1_tarski(X5))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f13,f12,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f11,f12])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_enumset1)).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_enumset1)).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(sK0,sK0),k2_enumset1(sK1,sK2,sK3,sK4)),k1_tarski(sK5))),
% 0.21/0.46    inference(definition_unfolding,[],[f10,f12,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)),k1_tarski(X6))) )),
% 0.21/0.46    inference(definition_unfolding,[],[f14,f12])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k5_enumset1(sK0,sK0,sK1,sK2,sK3,sK4,sK5)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (7987)------------------------------
% 0.21/0.46  % (7987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (7987)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (7987)Memory used [KB]: 1535
% 0.21/0.46  % (7987)Time elapsed: 0.006 s
% 0.21/0.46  % (7987)------------------------------
% 0.21/0.46  % (7987)------------------------------
% 0.21/0.47  % (7972)Success in time 0.108 s
%------------------------------------------------------------------------------
