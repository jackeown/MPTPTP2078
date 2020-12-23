%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   16 (  20 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   17 (  21 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f9,f13,f14])).

fof(f14,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4)) ),
    inference(definition_unfolding,[],[f12,f10])).

fof(f10,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

fof(f12,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ),
    inference(definition_unfolding,[],[f11,f10,f10])).

fof(f11,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f9,plain,(
    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n005.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:46:33 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (31706)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.43  % (31707)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.43  % (31706)Refutation not found, incomplete strategy% (31706)------------------------------
% 0.21/0.43  % (31706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (31706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.43  
% 0.21/0.43  % (31706)Memory used [KB]: 10490
% 0.21/0.43  % (31706)Time elapsed: 0.026 s
% 0.21/0.43  % (31706)------------------------------
% 0.21/0.43  % (31706)------------------------------
% 0.21/0.44  % (31707)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.45    inference(definition_unfolding,[],[f9,f13,f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X4,X4))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f12,f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f11,f10,f10])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,plain,(
% 0.21/0.45    k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).
% 0.21/0.45  fof(f7,plain,(
% 0.21/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k3_enumset1(sK0,sK0,sK0,sK0,sK1)),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f6,plain,(
% 0.21/0.45    ? [X0,X1] : k2_tarski(X0,X1) != k3_enumset1(X0,X0,X0,X0,X1)),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 0.21/0.45    inference(negated_conjecture,[],[f4])).
% 0.21/0.45  fof(f4,conjecture,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (31707)------------------------------
% 0.21/0.45  % (31707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (31707)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (31707)Memory used [KB]: 1535
% 0.21/0.45  % (31707)Time elapsed: 0.003 s
% 0.21/0.45  % (31707)------------------------------
% 0.21/0.45  % (31707)------------------------------
% 0.21/0.45  % (31694)Success in time 0.082 s
%------------------------------------------------------------------------------
