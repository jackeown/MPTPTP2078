%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   24 (  38 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  39 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :   10 (   6 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f23,plain,(
    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)))) ),
    inference(definition_unfolding,[],[f12,f22,f13,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(definition_unfolding,[],[f16,f19,f13])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6))))) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).

fof(f12,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:55 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.40  % (12692)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (12692)Refutation not found, incomplete strategy% (12692)------------------------------
% 0.20/0.41  % (12692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (12692)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (12692)Memory used [KB]: 10618
% 0.20/0.41  % (12692)Time elapsed: 0.003 s
% 0.20/0.41  % (12692)------------------------------
% 0.20/0.41  % (12692)------------------------------
% 0.20/0.45  % (12684)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (12693)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (12693)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f23,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6))))),
% 0.20/0.45    inference(definition_unfolding,[],[f12,f22,f13,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f16,f19,f13])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f14,f13])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l57_enumset1)).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X2),k1_tarski(X3)),k1_tarski(X4)),k2_xboole_0(k1_tarski(X5),k1_tarski(X6)))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f18,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X1),k1_tarski(X2)),k1_tarski(X3)),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) )),
% 0.20/0.45    inference(definition_unfolding,[],[f17,f20])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_enumset1)).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f9,f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k2_tarski(sK0,sK1),k3_enumset1(sK2,sK3,sK4,sK5,sK6))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (12693)------------------------------
% 0.20/0.45  % (12693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (12693)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (12693)Memory used [KB]: 1535
% 0.20/0.45  % (12693)Time elapsed: 0.047 s
% 0.20/0.45  % (12693)------------------------------
% 0.20/0.45  % (12693)------------------------------
% 0.20/0.45  % (12680)Success in time 0.101 s
%------------------------------------------------------------------------------
