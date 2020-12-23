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
% DateTime   : Thu Dec  3 12:34:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  41 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  42 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f26,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k2_tarski(X4,X5)),k3_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k2_tarski(X4,X5))) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)),k3_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ),
    inference(definition_unfolding,[],[f20,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0))),k2_tarski(X0,X1)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0))),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f14,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2))),k2_tarski(X3,X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2))),k2_tarski(X3,X4))) ),
    inference(definition_unfolding,[],[f17,f15,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2))) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k2_tarski(X5,X6)),k3_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k2_tarski(sK0,sK1)),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f13,f21])).

fof(f13,plain,(
    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)
   => k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (31602)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.42  % (31602)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f27,f28])).
% 0.20/0.42  fof(f28,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X1)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X1)))) )),
% 0.20/0.42    inference(forward_demodulation,[],[f26,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k2_tarski(X4,X5)),k3_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k2_tarski(X4,X5)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f18,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)),k3_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f20,f15])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_enumset1)).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0))),k2_tarski(X0,X1)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X0,X0))),k2_tarski(X0,X1)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f14,f24])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2))),k2_tarski(X3,X4)),k3_xboole_0(k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2))),k2_tarski(X3,X4)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f17,f15,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2)),k3_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k2_tarski(X1,X2)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f16,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k2_tarski(X5,X6)),k3_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k2_tarski(X5,X6)))) )),
% 0.20/0.42    inference(definition_unfolding,[],[f19,f21])).
% 0.20/0.42  fof(f19,plain,(
% 0.20/0.42    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_enumset1)).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f6])).
% 0.20/0.42  fof(f6,axiom,(
% 0.20/0.42    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    k2_tarski(sK0,sK1) != k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k2_tarski(sK0,sK1)),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k2_tarski(sK0,sK1)))),
% 0.20/0.42    inference(definition_unfolding,[],[f13,f21])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) => k2_tarski(sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1] : k2_tarski(X0,X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.20/0.42    inference(ennf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.20/0.42    inference(negated_conjecture,[],[f8])).
% 0.20/0.42  fof(f8,conjecture,(
% 0.20/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.20/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_enumset1)).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (31602)------------------------------
% 0.20/0.42  % (31602)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (31602)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (31602)Memory used [KB]: 1535
% 0.20/0.42  % (31602)Time elapsed: 0.004 s
% 0.20/0.42  % (31602)------------------------------
% 0.20/0.42  % (31602)------------------------------
% 0.20/0.42  % (31588)Success in time 0.061 s
%------------------------------------------------------------------------------
