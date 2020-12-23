%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 114 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   43 ( 115 expanded)
%              Number of equality atoms :   42 ( 114 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f37,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X0,X0))) ),
    inference(superposition,[],[f69,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f23,f21,f19,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f69,plain,(
    ! [X6,X10,X8,X7,X9] : k5_xboole_0(k2_tarski(X10,X10),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_tarski(X10,X10))) = k5_xboole_0(k2_tarski(X10,X6),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X10,X6))) ),
    inference(forward_demodulation,[],[f68,f36])).

fof(f68,plain,(
    ! [X6,X10,X8,X7,X9] : k5_xboole_0(k2_tarski(X10,X6),k4_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X7,X7))),k2_tarski(X10,X6))) = k5_xboole_0(k2_tarski(X10,X10),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_tarski(X10,X10))) ),
    inference(forward_demodulation,[],[f60,f36])).

fof(f60,plain,(
    ! [X6,X10,X8,X7,X9] : k5_xboole_0(k2_tarski(X10,X6),k4_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X7,X7))),k2_tarski(X10,X6))) = k5_xboole_0(k2_tarski(X10,X10),k4_xboole_0(k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X6,X6))),k2_tarski(X10,X10))) ),
    inference(superposition,[],[f38,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_enumset1(X4,X4,X0,X0),k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X0,X0))) = k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X4))) ),
    inference(superposition,[],[f43,f36])).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_enumset1(X2,X2,X0,X0),k4_xboole_0(k2_enumset1(X1,X3,X4,X5),k2_enumset1(X2,X2,X0,X0))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_enumset1(X3,X3,X4,X5),k2_tarski(X0,X1))),k2_tarski(X2,X2))) ),
    inference(superposition,[],[f39,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f22])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3))),k2_tarski(X0,X0))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f28,f33,f21,f22])).

fof(f33,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3))),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f26,f21,f19,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X4,X5),k2_enumset1(X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f25,f21,f22,f22])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_tarski(X2,X2))),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f33,f21,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f24,f21,f19])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(f37,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f18,f32])).

fof(f18,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (14346)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (14355)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (14355)Refutation not found, incomplete strategy% (14355)------------------------------
% 0.21/0.47  % (14355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (14355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (14355)Memory used [KB]: 10618
% 0.21/0.47  % (14355)Time elapsed: 0.005 s
% 0.21/0.47  % (14355)------------------------------
% 0.21/0.47  % (14355)------------------------------
% 0.21/0.48  % (14354)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (14348)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (14357)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (14348)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f113])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)),
% 0.21/0.50    inference(superposition,[],[f37,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X0,X0)))) )),
% 0.21/0.50    inference(superposition,[],[f69,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_enumset1(X1,X1,X2,X3),k2_tarski(X0,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f23,f21,f19,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X6,X10,X8,X7,X9] : (k5_xboole_0(k2_tarski(X10,X10),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_tarski(X10,X10))) = k5_xboole_0(k2_tarski(X10,X6),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X10,X6)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f68,f36])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X6,X10,X8,X7,X9] : (k5_xboole_0(k2_tarski(X10,X6),k4_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X7,X7))),k2_tarski(X10,X6))) = k5_xboole_0(k2_tarski(X10,X10),k4_xboole_0(k2_enumset1(X6,X7,X8,X9),k2_tarski(X10,X10)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f60,f36])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X6,X10,X8,X7,X9] : (k5_xboole_0(k2_tarski(X10,X6),k4_xboole_0(k5_xboole_0(k2_tarski(X7,X7),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X7,X7))),k2_tarski(X10,X6))) = k5_xboole_0(k2_tarski(X10,X10),k4_xboole_0(k5_xboole_0(k2_tarski(X6,X6),k4_xboole_0(k2_enumset1(X7,X7,X8,X9),k2_tarski(X6,X6))),k2_tarski(X10,X10)))) )),
% 0.21/0.50    inference(superposition,[],[f38,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_enumset1(X4,X4,X0,X0),k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X0,X0))) = k5_xboole_0(k2_tarski(X4,X4),k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X4)))) )),
% 0.21/0.50    inference(superposition,[],[f43,f36])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X2,X2,X0,X0),k4_xboole_0(k2_enumset1(X1,X3,X4,X5),k2_enumset1(X2,X2,X0,X0))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_enumset1(X3,X3,X4,X5),k2_tarski(X0,X1))),k2_tarski(X2,X2)))) )),
% 0.21/0.50    inference(superposition,[],[f39,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f22])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3))),k2_tarski(X0,X0))) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_enumset1(X0,X0,X1,X2)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f28,f33,f21,f22])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3))),k2_tarski(X0,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f26,f21,f19,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k2_enumset1(X0,X0,X1,X2),k4_xboole_0(k2_enumset1(X3,X3,X4,X5),k2_enumset1(X0,X0,X1,X2)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f25,f21,f22,f22])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X1,X2,X3),k4_xboole_0(k2_enumset1(X4,X4,X5,X6),k2_enumset1(X1,X1,X2,X3))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k2_tarski(X2,X2))),k2_tarski(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f27,f33,f21,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k2_tarski(X0,X0)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f24,f21,f19])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK0,sK0)))),
% 0.21/0.50    inference(definition_unfolding,[],[f18,f32])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (14348)------------------------------
% 0.21/0.51  % (14348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14348)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (14348)Memory used [KB]: 6268
% 0.21/0.51  % (14348)Time elapsed: 0.062 s
% 0.21/0.51  % (14348)------------------------------
% 0.21/0.51  % (14348)------------------------------
% 0.21/0.51  % (14339)Success in time 0.147 s
%------------------------------------------------------------------------------
