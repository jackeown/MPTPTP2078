%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 139 expanded)
%              Number of leaves         :    9 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   34 ( 140 expanded)
%              Number of equality atoms :   33 ( 139 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f260])).

fof(f260,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) ),
    inference(superposition,[],[f37,f197])).

fof(f197,plain,(
    ! [X17,X18,X16] : k1_enumset1(X16,X17,X18) = k5_xboole_0(k1_enumset1(X16,X16,X16),k4_xboole_0(k1_enumset1(X16,X17,X18),k1_enumset1(X16,X16,X16))) ),
    inference(superposition,[],[f58,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0))) ),
    inference(superposition,[],[f46,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f22,f21,f20,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f19,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X2,X3,X0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X0))) = k5_xboole_0(k1_enumset1(X2,X2,X3),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(superposition,[],[f39,f36])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f27,f33,f21])).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f21,f20,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f23,f21,f31])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f58,plain,(
    ! [X6,X4,X7,X5,X3] : k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X6,X6,X7))) ),
    inference(forward_demodulation,[],[f54,f36])).

fof(f54,plain,(
    ! [X6,X4,X7,X5,X3] : k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k1_enumset1(X5,X5,X5),k1_enumset1(X3,X3,X4))),k1_enumset1(X6,X6,X7))) ),
    inference(superposition,[],[f39,f46])).

fof(f37,plain,(
    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f18,f32])).

fof(f18,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (22021)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.43  % (22021)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f268,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f260])).
% 0.20/0.43  fof(f260,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)),
% 0.20/0.43    inference(superposition,[],[f37,f197])).
% 0.20/0.43  fof(f197,plain,(
% 0.20/0.43    ( ! [X17,X18,X16] : (k1_enumset1(X16,X17,X18) = k5_xboole_0(k1_enumset1(X16,X16,X16),k4_xboole_0(k1_enumset1(X16,X17,X18),k1_enumset1(X16,X16,X16)))) )),
% 0.20/0.43    inference(superposition,[],[f58,f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X1,X2),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.43    inference(superposition,[],[f46,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k1_enumset1(X2,X2,X2),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f22,f21,f20,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f19,f20])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X2,X3,X0),k4_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X0))) = k5_xboole_0(k1_enumset1(X2,X2,X3),k4_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 0.20/0.43    inference(superposition,[],[f39,f36])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X0,X1,X2)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f27,f33,f21])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_enumset1(X0,X0,X1),k4_xboole_0(k5_xboole_0(k1_enumset1(X2,X2,X2),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X2,X2,X2))),k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f26,f21,f20,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f23,f21,f31])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X6,X4,X7,X5,X3] : (k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k1_enumset1(X3,X4,X5),k1_enumset1(X6,X6,X7)))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f54,f36])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X6,X4,X7,X5,X3] : (k5_xboole_0(k1_enumset1(X6,X7,X3),k4_xboole_0(k1_enumset1(X4,X4,X5),k1_enumset1(X6,X7,X3))) = k5_xboole_0(k1_enumset1(X6,X6,X7),k4_xboole_0(k5_xboole_0(k1_enumset1(X3,X3,X4),k4_xboole_0(k1_enumset1(X5,X5,X5),k1_enumset1(X3,X3,X4))),k1_enumset1(X6,X6,X7)))) )),
% 0.20/0.43    inference(superposition,[],[f39,f46])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK1,sK2) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK0,sK0,sK0)))),
% 0.20/0.43    inference(definition_unfolding,[],[f18,f32])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.43    inference(negated_conjecture,[],[f13])).
% 0.20/0.43  fof(f13,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (22021)------------------------------
% 0.20/0.43  % (22021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (22021)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (22021)Memory used [KB]: 1918
% 0.20/0.43  % (22021)Time elapsed: 0.021 s
% 0.20/0.43  % (22021)------------------------------
% 0.20/0.43  % (22021)------------------------------
% 0.20/0.43  % (22007)Success in time 0.079 s
%------------------------------------------------------------------------------
