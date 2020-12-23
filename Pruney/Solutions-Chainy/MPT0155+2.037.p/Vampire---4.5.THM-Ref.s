%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 130 expanded)
%              Number of leaves         :    9 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   32 ( 131 expanded)
%              Number of equality atoms :   31 ( 130 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9106)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f61,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f40,f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:39:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (9094)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (9094)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (9095)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (9100)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  % (9106)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),
% 0.21/0.47    inference(superposition,[],[f40,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k5_xboole_0(k2_tarski(X3,X3),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X3,X3))),k2_tarski(X2,X2))) = k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)))) )),
% 0.21/0.47    inference(superposition,[],[f33,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f18,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f20,f19,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X1,X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f23,f29,f19,f27])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k5_xboole_0(k2_tarski(X2,X3),k4_xboole_0(k2_tarski(X4,X4),k2_tarski(X2,X3))),k2_tarski(X1,X1))),k2_tarski(X0,X0)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f22,f19,f17,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k2_tarski(X1,X2),k4_xboole_0(k2_tarski(X3,X3),k2_tarski(X1,X2))),k2_tarski(X0,X0)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f21,f19,f17,f27])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_enumset1)).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f32,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X2,X0),k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X2,X0))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 0.21/0.47    inference(superposition,[],[f36,f31])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))),k2_tarski(sK0,sK0)))),
% 0.21/0.47    inference(definition_unfolding,[],[f16,f27,f28])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k2_enumset1(sK0,sK0,sK1,sK2)),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.47    inference(negated_conjecture,[],[f11])).
% 0.21/0.47  fof(f11,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (9094)------------------------------
% 0.21/0.47  % (9094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9094)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (9094)Memory used [KB]: 6140
% 0.21/0.47  % (9094)Time elapsed: 0.046 s
% 0.21/0.47  % (9094)------------------------------
% 0.21/0.47  % (9094)------------------------------
% 0.21/0.47  % (9093)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (9091)Success in time 0.114 s
%------------------------------------------------------------------------------
