%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:10 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   29 (  71 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  72 expanded)
%              Number of equality atoms :   29 (  71 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f46,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f17,f19,f14])).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f16,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

fof(f46,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k1_tarski(sK5),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0))) ),
    inference(superposition,[],[f22,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))),k1_tarski(X0))) ),
    inference(forward_demodulation,[],[f27,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f15,f14,f14,f14,f14])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))),k4_xboole_0(X5,k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))))) ),
    inference(superposition,[],[f23,f24])).

fof(f22,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(definition_unfolding,[],[f12,f20,f14,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f18,f14,f19])).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).

fof(f12,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:28:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (366)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.13/0.42  % (366)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f51,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(trivial_inequality_removal,[],[f50])).
% 0.13/0.42  fof(f50,plain,(
% 0.13/0.42    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0)))),
% 0.13/0.42    inference(forward_demodulation,[],[f46,f24])).
% 0.13/0.42  fof(f24,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k1_tarski(X4),k2_enumset1(X0,X1,X2,X3)))) )),
% 0.13/0.42    inference(definition_unfolding,[],[f17,f19,f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)))) )),
% 0.13/0.42    inference(definition_unfolding,[],[f16,f14])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).
% 0.13/0.42  fof(f46,plain,(
% 0.13/0.42    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k2_enumset1(sK1,sK2,sK3,sK4),k4_xboole_0(k1_tarski(sK5),k2_enumset1(sK1,sK2,sK3,sK4))),k1_tarski(sK0)))),
% 0.13/0.42    inference(superposition,[],[f22,f28])).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k2_enumset1(X1,X2,X3,X4),k4_xboole_0(X5,k2_enumset1(X1,X2,X3,X4))),k1_tarski(X0)))) )),
% 0.13/0.42    inference(forward_demodulation,[],[f27,f23])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.13/0.42    inference(definition_unfolding,[],[f15,f14,f14,f14,f14])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(X5,k1_tarski(X4))),k2_enumset1(X0,X1,X2,X3))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))),k4_xboole_0(X5,k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0)))))) )),
% 0.13/0.42    inference(superposition,[],[f23,f24])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_tarski(sK5),k1_tarski(sK4))),k2_enumset1(sK0,sK1,sK2,sK3)))),
% 0.13/0.42    inference(definition_unfolding,[],[f12,f20,f14,f21])).
% 0.13/0.42  fof(f21,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.13/0.42    inference(definition_unfolding,[],[f13,f14])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_enumset1(X2,X3,X4,X5),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.13/0.42    inference(definition_unfolding,[],[f18,f14,f19])).
% 0.13/0.42  fof(f18,plain,(
% 0.13/0.42    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.13/0.42    inference(cnf_transformation,[],[f6])).
% 0.13/0.42  fof(f6,axiom,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_enumset1)).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.13/0.42    inference(cnf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.13/0.42    inference(ennf_transformation,[],[f8])).
% 0.13/0.42  fof(f8,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.13/0.42    inference(negated_conjecture,[],[f7])).
% 0.13/0.42  fof(f7,conjecture,(
% 0.13/0.42    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.13/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_enumset1)).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (366)------------------------------
% 0.13/0.42  % (366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (366)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (366)Memory used [KB]: 1663
% 0.13/0.42  % (366)Time elapsed: 0.005 s
% 0.13/0.42  % (366)------------------------------
% 0.13/0.42  % (366)------------------------------
% 0.13/0.42  % (353)Success in time 0.058 s
%------------------------------------------------------------------------------
