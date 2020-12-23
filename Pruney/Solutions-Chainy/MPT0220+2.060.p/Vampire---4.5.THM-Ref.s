%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  74 expanded)
%              Number of leaves         :   11 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  75 expanded)
%              Number of equality atoms :   34 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f33])).

fof(f33,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f32,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3)))) ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X0,X0,X1,X2,X3,X4)))) ),
    inference(definition_unfolding,[],[f24,f25,f22,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f17,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f20,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f32,plain,(
    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f15,f28,f25,f30,f28])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f28])).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:39:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.40  % (2863)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.40  % (2863)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.40  % SZS output start Proof for theBenchmark
% 0.19/0.40  fof(f34,plain,(
% 0.19/0.40    $false),
% 0.19/0.40    inference(trivial_inequality_removal,[],[f33])).
% 0.19/0.40  fof(f33,plain,(
% 0.19/0.40    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),
% 0.19/0.40    inference(superposition,[],[f32,f31])).
% 0.19/0.40  fof(f31,plain,(
% 0.19/0.40    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k4_enumset1(X0,X0,X0,X1,X2,X3),k5_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k3_xboole_0(k4_enumset1(X4,X4,X4,X4,X4,X5),k4_enumset1(X0,X0,X0,X1,X2,X3))))) )),
% 0.19/0.40    inference(definition_unfolding,[],[f23,f29])).
% 0.19/0.40  fof(f29,plain,(
% 0.19/0.40    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k4_enumset1(X0,X0,X1,X2,X3,X4),k5_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k3_xboole_0(k4_enumset1(X5,X5,X5,X5,X5,X6),k4_enumset1(X0,X0,X1,X2,X3,X4))))) )),
% 0.19/0.40    inference(definition_unfolding,[],[f24,f25,f22,f28])).
% 0.19/0.40  fof(f28,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.40    inference(definition_unfolding,[],[f17,f27])).
% 0.19/0.40  fof(f27,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.40    inference(definition_unfolding,[],[f20,f26])).
% 0.19/0.40  fof(f26,plain,(
% 0.19/0.40    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.40    inference(definition_unfolding,[],[f21,f22])).
% 0.19/0.40  fof(f21,plain,(
% 0.19/0.40    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f7])).
% 0.19/0.40  fof(f7,axiom,(
% 0.19/0.40    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.40  fof(f20,plain,(
% 0.19/0.40    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f6])).
% 0.19/0.40  fof(f6,axiom,(
% 0.19/0.40    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.40  fof(f17,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f5])).
% 0.19/0.40  fof(f5,axiom,(
% 0.19/0.40    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.40  fof(f22,plain,(
% 0.19/0.40    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.19/0.40    inference(cnf_transformation,[],[f8])).
% 0.19/0.40  fof(f8,axiom,(
% 0.19/0.40    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.40  fof(f25,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.19/0.40    inference(definition_unfolding,[],[f19,f18])).
% 0.19/0.40  fof(f18,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f1])).
% 0.19/0.40  fof(f1,axiom,(
% 0.19/0.40    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.40  fof(f19,plain,(
% 0.19/0.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f2])).
% 0.19/0.40  fof(f2,axiom,(
% 0.19/0.40    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.40    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.19/0.40  fof(f24,plain,(
% 0.19/0.40    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 0.19/0.40    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,axiom,(
% 0.19/0.41    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0))))),
% 0.19/0.41    inference(definition_unfolding,[],[f15,f28,f25,f30,f28])).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f16,f28])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f11])).
% 0.19/0.41  fof(f11,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.19/0.41    inference(negated_conjecture,[],[f10])).
% 0.19/0.41  fof(f10,conjecture,(
% 0.19/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (2863)------------------------------
% 0.19/0.41  % (2863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (2863)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (2863)Memory used [KB]: 1535
% 0.19/0.41  % (2863)Time elapsed: 0.004 s
% 0.19/0.41  % (2863)------------------------------
% 0.19/0.41  % (2863)------------------------------
% 0.19/0.41  % (2850)Success in time 0.056 s
%------------------------------------------------------------------------------
