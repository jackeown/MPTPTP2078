%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:51 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 136 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   38 ( 137 expanded)
%              Number of equality atoms :   37 ( 136 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f41,plain,(
    $false ),
    inference(subsumption_resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(superposition,[],[f32,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f15,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k2_tarski(X0,X0))) ),
    inference(forward_demodulation,[],[f29,f27])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f19,f26,f16,f23])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f22,f16,f23,f23])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f39,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f31,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) ),
    inference(superposition,[],[f35,f27])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k2_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f30,f27])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f21,f25,f16,f23])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).

fof(f31,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k2_tarski(sK0,sK0))) ),
    inference(forward_demodulation,[],[f28,f27])).

fof(f28,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f14,f23,f25])).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2)
   => k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:16:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.43  % (634)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.43  % (634)Refutation found. Thanks to Tanya!
% 0.23/0.43  % SZS status Theorem for theBenchmark
% 0.23/0.43  % SZS output start Proof for theBenchmark
% 0.23/0.43  fof(f41,plain,(
% 0.23/0.43    $false),
% 0.23/0.43    inference(subsumption_resolution,[],[f39,f33])).
% 0.23/0.43  fof(f33,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) = k5_xboole_0(k2_tarski(X2,X2),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 0.23/0.43    inference(superposition,[],[f32,f27])).
% 0.23/0.43  fof(f27,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0)))) )),
% 0.23/0.43    inference(definition_unfolding,[],[f15,f23])).
% 0.23/0.43  fof(f23,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)))) )),
% 0.23/0.43    inference(definition_unfolding,[],[f17,f16])).
% 0.23/0.43  fof(f16,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f1])).
% 0.23/0.43  fof(f1,axiom,(
% 0.23/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.23/0.43  fof(f17,plain,(
% 0.23/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f3])).
% 0.23/0.43  fof(f3,axiom,(
% 0.23/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.23/0.43  fof(f15,plain,(
% 0.23/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f6])).
% 0.23/0.43  fof(f6,axiom,(
% 0.23/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.43  fof(f32,plain,(
% 0.23/0.43    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k2_tarski(X0,X0)))) )),
% 0.23/0.43    inference(forward_demodulation,[],[f29,f27])).
% 0.23/0.43  fof(f29,plain,(
% 0.23/0.43    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.23/0.43    inference(definition_unfolding,[],[f19,f26,f16,f23])).
% 0.23/0.43  fof(f26,plain,(
% 0.23/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X0),k1_tarski(X0)))))) )),
% 0.23/0.43    inference(definition_unfolding,[],[f18,f25])).
% 0.23/0.43  fof(f25,plain,(
% 0.23/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0)))))) )),
% 0.23/0.43    inference(definition_unfolding,[],[f20,f24])).
% 0.23/0.43  fof(f24,plain,(
% 0.23/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k2_tarski(X4,X5),k1_tarski(X3))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)))))) )),
% 0.23/0.43    inference(definition_unfolding,[],[f22,f16,f23,f23])).
% 0.23/0.43  fof(f22,plain,(
% 0.23/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f2])).
% 0.23/0.43  fof(f2,axiom,(
% 0.23/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l62_enumset1)).
% 0.23/0.43  fof(f20,plain,(
% 0.23/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f8])).
% 0.23/0.43  fof(f8,axiom,(
% 0.23/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.43  fof(f18,plain,(
% 0.23/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.23/0.43    inference(cnf_transformation,[],[f7])).
% 0.23/0.43  fof(f7,axiom,(
% 0.23/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.43  fof(f19,plain,(
% 0.23/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f4])).
% 0.23/0.43  fof(f4,axiom,(
% 0.23/0.43    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.23/0.43  fof(f39,plain,(
% 0.23/0.43    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK1,sK2),k2_tarski(sK0,sK0)))),
% 0.23/0.43    inference(superposition,[],[f31,f36])).
% 0.23/0.43  fof(f36,plain,(
% 0.23/0.43    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k2_tarski(X2,X3),k1_tarski(X1))),k2_tarski(X0,X0))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) )),
% 0.23/0.43    inference(superposition,[],[f35,f27])).
% 0.23/0.43  fof(f35,plain,(
% 0.23/0.43    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))))) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k2_tarski(X0,X1)))) )),
% 0.23/0.43    inference(forward_demodulation,[],[f30,f27])).
% 0.23/0.43  fof(f30,plain,(
% 0.23/0.43    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_tarski(X3,X4),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X0))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0))),k4_xboole_0(k2_tarski(X3,X4),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_tarski(X1,X2),k1_tarski(X0)))))) )),
% 0.23/0.43    inference(definition_unfolding,[],[f21,f25,f16,f23])).
% 0.23/0.43  fof(f21,plain,(
% 0.23/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 0.23/0.43    inference(cnf_transformation,[],[f5])).
% 0.23/0.43  fof(f5,axiom,(
% 0.23/0.43    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_enumset1)).
% 0.23/0.43  fof(f31,plain,(
% 0.23/0.43    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k2_tarski(sK0,sK0)))),
% 0.23/0.43    inference(forward_demodulation,[],[f28,f27])).
% 0.23/0.43  fof(f28,plain,(
% 0.23/0.43    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK0))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_tarski(sK0)))))),
% 0.23/0.43    inference(definition_unfolding,[],[f14,f23,f25])).
% 0.23/0.43  fof(f14,plain,(
% 0.23/0.43    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.23/0.43    inference(cnf_transformation,[],[f13])).
% 0.23/0.43  fof(f13,plain,(
% 0.23/0.43    k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.23/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.23/0.43  fof(f12,plain,(
% 0.23/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2) => k1_enumset1(sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)),
% 0.23/0.43    introduced(choice_axiom,[])).
% 0.23/0.43  fof(f11,plain,(
% 0.23/0.43    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k3_enumset1(X0,X0,X0,X1,X2)),
% 0.23/0.43    inference(ennf_transformation,[],[f10])).
% 0.23/0.43  fof(f10,negated_conjecture,(
% 0.23/0.43    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.23/0.43    inference(negated_conjecture,[],[f9])).
% 0.23/0.43  fof(f9,conjecture,(
% 0.23/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)),
% 0.23/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_enumset1)).
% 0.23/0.43  % SZS output end Proof for theBenchmark
% 0.23/0.43  % (634)------------------------------
% 0.23/0.43  % (634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.43  % (634)Termination reason: Refutation
% 0.23/0.43  
% 0.23/0.43  % (634)Memory used [KB]: 1663
% 0.23/0.43  % (634)Time elapsed: 0.006 s
% 0.23/0.43  % (634)------------------------------
% 0.23/0.43  % (634)------------------------------
% 0.23/0.43  % (616)Success in time 0.065 s
%------------------------------------------------------------------------------
