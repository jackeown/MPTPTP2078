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
% DateTime   : Thu Dec  3 12:33:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 129 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   31 ( 130 expanded)
%              Number of equality atoms :   30 ( 129 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(subsumption_resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X3,X3))),k2_tarski(X2,X2))) = k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) ),
    inference(superposition,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19,f17])).

fof(f17,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f29,f19,f27])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X1,X1))),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f22,f19,f17,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X2))),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f21,f19,f17,f27])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f40,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f32,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X2,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X0))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(superposition,[],[f36,f31])).

fof(f32,plain,(
    k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))),k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f16,f27,f28])).

fof(f16,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (3520)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.45  % (3522)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (3522)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f40,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X3,X3))),k2_tarski(X2,X2))) = k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)))) )),
% 0.21/0.45    inference(superposition,[],[f33,f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f20,f19,f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X0,X1)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f23,f29,f19,f27])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X1,X1))),k2_tarski(X0,X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f19,f17,f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X2))),k2_tarski(X0,X0)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f21,f19,f17,f27])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)))),
% 0.21/0.46    inference(backward_demodulation,[],[f32,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X2,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X0))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 0.21/0.46    inference(superposition,[],[f36,f31])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))),k2_tarski(sK0,sK0)))),
% 0.21/0.46    inference(definition_unfolding,[],[f16,f27,f28])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    inference(negated_conjecture,[],[f11])).
% 0.21/0.46  fof(f11,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (3522)------------------------------
% 0.21/0.46  % (3522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (3522)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (3522)Memory used [KB]: 1663
% 0.21/0.46  % (3522)Time elapsed: 0.008 s
% 0.21/0.46  % (3522)------------------------------
% 0.21/0.46  % (3522)------------------------------
% 0.21/0.46  % (3507)Success in time 0.103 s
%------------------------------------------------------------------------------
