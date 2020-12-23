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
% DateTime   : Thu Dec  3 12:34:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 148 expanded)
%              Number of leaves         :   11 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   40 ( 149 expanded)
%              Number of equality atoms :   39 ( 148 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f44])).

fof(f44,plain,(
    ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : k5_xboole_0(k1_enumset1(X9,X10,X11),k4_xboole_0(k5_enumset1(X12,X12,X13,X14,X15,X16,X17),k1_enumset1(X9,X10,X11))) = k5_xboole_0(k2_enumset1(X9,X10,X11,X12),k4_xboole_0(k3_enumset1(X13,X14,X15,X16,X17),k2_enumset1(X9,X10,X11,X12))) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f22,f26,f19,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f21,f19,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (16420)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f21,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k2_enumset1(X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f23,f26,f19])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).

fof(f137,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k2_enumset1(sK0,sK1,sK2,sK3))) ),
    inference(superposition,[],[f106,f98])).

fof(f98,plain,(
    ! [X26,X24,X23,X21,X19,X25,X22,X20,X18] : k5_xboole_0(k2_enumset1(X18,X19,X20,X21),k4_xboole_0(k3_enumset1(X22,X23,X24,X25,X26),k2_enumset1(X18,X19,X20,X21))) = k5_xboole_0(k2_enumset1(X23,X24,X25,X26),k4_xboole_0(k3_enumset1(X18,X19,X20,X21,X22),k2_enumset1(X23,X24,X25,X26))) ),
    inference(superposition,[],[f81,f30])).

fof(f81,plain,(
    ! [X26,X24,X23,X21,X19,X25,X22,X20,X18] : k5_xboole_0(k1_enumset1(X18,X18,X18),k4_xboole_0(k6_enumset1(X19,X20,X21,X22,X23,X24,X25,X26),k1_enumset1(X18,X18,X18))) = k5_xboole_0(k2_enumset1(X23,X24,X25,X26),k4_xboole_0(k3_enumset1(X18,X19,X20,X21,X22),k2_enumset1(X23,X24,X25,X26))) ),
    inference(superposition,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f17,f19,f19])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k3_enumset1(X0,X1,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f24,f26,f19])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).

fof(f106,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k4_xboole_0(k3_enumset1(sK8,sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7))) ),
    inference(superposition,[],[f33,f81])).

fof(f33,plain,(
    k5_xboole_0(k1_enumset1(sK8,sK8,sK8),k4_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_enumset1(sK8,sK8,sK8))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2))) ),
    inference(superposition,[],[f32,f28])).

fof(f32,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k4_xboole_0(k1_enumset1(sK8,sK8,sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f27,f29])).

fof(f27,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK0,sK0))) != k5_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k4_xboole_0(k1_enumset1(sK8,sK8,sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))) ),
    inference(definition_unfolding,[],[f15,f26,f19,f25])).

fof(f15,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))
   => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 15:54:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (16433)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (16432)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (16427)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (16426)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (16424)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (16433)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f137,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X14,X12,X10,X17,X15,X13,X11,X9,X16] : (k5_xboole_0(k1_enumset1(X9,X10,X11),k4_xboole_0(k5_enumset1(X12,X12,X13,X14,X15,X16,X17),k1_enumset1(X9,X10,X11))) = k5_xboole_0(k2_enumset1(X9,X10,X11,X12),k4_xboole_0(k3_enumset1(X13,X14,X15,X16,X17),k2_enumset1(X9,X10,X11,X12)))) )),
% 0.21/0.48    inference(superposition,[],[f30,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_enumset1(X3,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X1,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f26,f19,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f21,f19,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f16,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  % (16420)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_enumset1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_enumset1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k2_enumset1(X0,X1,X2,X3),k4_xboole_0(k3_enumset1(X4,X5,X6,X7,X8),k2_enumset1(X0,X1,X2,X3)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f26,f19])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l142_enumset1)).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k4_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k2_enumset1(sK0,sK1,sK2,sK3)))),
% 0.21/0.48    inference(superposition,[],[f106,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ( ! [X26,X24,X23,X21,X19,X25,X22,X20,X18] : (k5_xboole_0(k2_enumset1(X18,X19,X20,X21),k4_xboole_0(k3_enumset1(X22,X23,X24,X25,X26),k2_enumset1(X18,X19,X20,X21))) = k5_xboole_0(k2_enumset1(X23,X24,X25,X26),k4_xboole_0(k3_enumset1(X18,X19,X20,X21,X22),k2_enumset1(X23,X24,X25,X26)))) )),
% 0.21/0.48    inference(superposition,[],[f81,f30])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ( ! [X26,X24,X23,X21,X19,X25,X22,X20,X18] : (k5_xboole_0(k1_enumset1(X18,X18,X18),k4_xboole_0(k6_enumset1(X19,X20,X21,X22,X23,X24,X25,X26),k1_enumset1(X18,X18,X18))) = k5_xboole_0(k2_enumset1(X23,X24,X25,X26),k4_xboole_0(k3_enumset1(X18,X19,X20,X21,X22),k2_enumset1(X23,X24,X25,X26)))) )),
% 0.21/0.48    inference(superposition,[],[f31,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f17,f19,f19])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k4_xboole_0(k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8),k1_enumset1(X0,X0,X0))) = k5_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_xboole_0(k2_enumset1(X5,X6,X7,X8),k3_enumset1(X0,X1,X2,X3,X4)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f26,f19])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_enumset1)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2))) != k5_xboole_0(k2_enumset1(sK4,sK5,sK6,sK7),k4_xboole_0(k3_enumset1(sK8,sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)))),
% 0.21/0.48    inference(superposition,[],[f33,f81])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    k5_xboole_0(k1_enumset1(sK8,sK8,sK8),k4_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_enumset1(sK8,sK8,sK8))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2)))),
% 0.21/0.48    inference(superposition,[],[f32,f28])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k5_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k4_xboole_0(k1_enumset1(sK8,sK8,sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7))) != k5_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_xboole_0(k5_enumset1(sK3,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK1,sK2)))),
% 0.21/0.48    inference(backward_demodulation,[],[f27,f29])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8),k1_enumset1(sK0,sK0,sK0))) != k5_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k4_xboole_0(k1_enumset1(sK8,sK8,sK8),k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)))),
% 0.21/0.48    inference(definition_unfolding,[],[f15,f26,f19,f25])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f12,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8)) => k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7),k1_tarski(sK8))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7),k1_tarski(X8))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (16433)------------------------------
% 0.21/0.48  % (16433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16433)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (16433)Memory used [KB]: 1791
% 0.21/0.48  % (16433)Time elapsed: 0.022 s
% 0.21/0.48  % (16433)------------------------------
% 0.21/0.48  % (16433)------------------------------
% 0.21/0.48  % (16422)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (16419)Success in time 0.123 s
%------------------------------------------------------------------------------
