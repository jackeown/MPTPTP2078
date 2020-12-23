%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   23 (  25 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f174,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f170])).

% (28881)Termination reason: Refutation not found, incomplete strategy

% (28881)Memory used [KB]: 10490
fof(f170,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(superposition,[],[f13,f142])).

% (28881)Time elapsed: 0.070 s
% (28881)------------------------------
% (28881)------------------------------
fof(f142,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_enumset1(X17,X18,X14,X15),k1_tarski(X16)) = k3_enumset1(X17,X18,X14,X15,X16) ),
    inference(forward_demodulation,[],[f135,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f135,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_enumset1(X17,X18,X14,X15),k1_tarski(X16)) = k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X14,X15,X16)) ),
    inference(superposition,[],[f70,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f70,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18)) = k2_xboole_0(k2_enumset1(X16,X17,X14,X15),X18) ),
    inference(forward_demodulation,[],[f61,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f61,plain,(
    ! [X14,X17,X15,X18,X16] : k2_xboole_0(k2_xboole_0(k1_enumset1(X16,X17,X14),k1_tarski(X15)),X18) = k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18)) ),
    inference(superposition,[],[f23,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f23,plain,(
    ! [X6,X4,X8,X7,X5] : k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_xboole_0(k1_tarski(X6),X7),X8)) = k2_xboole_0(k2_xboole_0(k1_enumset1(X4,X5,X6),X7),X8) ),
    inference(superposition,[],[f18,f16])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).

fof(f13,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (28870)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (28872)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (28874)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (28873)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (28885)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (28881)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (28877)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (28873)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (28880)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (28882)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (28881)Refutation not found, incomplete strategy% (28881)------------------------------
% 0.21/0.48  % (28881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f170])).
% 0.21/0.48  % (28881)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (28881)Memory used [KB]: 10490
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 0.21/0.48    inference(superposition,[],[f13,f142])).
% 0.21/0.48  % (28881)Time elapsed: 0.070 s
% 0.21/0.48  % (28881)------------------------------
% 0.21/0.48  % (28881)------------------------------
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_enumset1(X17,X18,X14,X15),k1_tarski(X16)) = k3_enumset1(X17,X18,X14,X15,X16)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f135,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_enumset1(X17,X18,X14,X15),k1_tarski(X16)) = k2_xboole_0(k2_tarski(X17,X18),k1_enumset1(X14,X15,X16))) )),
% 0.21/0.49    inference(superposition,[],[f70,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18)) = k2_xboole_0(k2_enumset1(X16,X17,X14,X15),X18)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f61,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X14,X17,X15,X18,X16] : (k2_xboole_0(k2_xboole_0(k1_enumset1(X16,X17,X14),k1_tarski(X15)),X18) = k2_xboole_0(k2_tarski(X16,X17),k2_xboole_0(k2_tarski(X14,X15),X18))) )),
% 0.21/0.49    inference(superposition,[],[f23,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X6,X4,X8,X7,X5] : (k2_xboole_0(k2_tarski(X4,X5),k2_xboole_0(k2_xboole_0(k1_tarski(X6),X7),X8)) = k2_xboole_0(k2_xboole_0(k1_enumset1(X4,X5,X6),X7),X8)) )),
% 0.21/0.49    inference(superposition,[],[f18,f16])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) = k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_xboole_1)).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k1_tarski(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (28873)------------------------------
% 0.21/0.49  % (28873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28873)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (28873)Memory used [KB]: 1918
% 0.21/0.49  % (28873)Time elapsed: 0.061 s
% 0.21/0.49  % (28873)------------------------------
% 0.21/0.49  % (28873)------------------------------
% 0.21/0.49  % (28866)Success in time 0.129 s
%------------------------------------------------------------------------------
