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
% DateTime   : Thu Dec  3 12:32:20 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 432 expanded)
%              Number of leaves         :   12 ( 142 expanded)
%              Depth                    :   18
%              Number of atoms          :   71 ( 433 expanded)
%              Number of equality atoms :   70 ( 432 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2517,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2516])).

fof(f2516,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f2515,f102])).

fof(f102,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f37,f62])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f37,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f19,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f26,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2515,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f2514,f20])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f2514,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2513,f322])).

fof(f322,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f320,f321])).

fof(f321,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f316,f116])).

fof(f116,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(superposition,[],[f102,f20])).

fof(f316,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k5_xboole_0(X3,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f264,f313])).

fof(f313,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) ),
    inference(forward_demodulation,[],[f312,f18])).

fof(f312,plain,(
    ! [X6,X7] : k1_xboole_0 = k3_xboole_0(X7,k5_xboole_0(X6,X6)) ),
    inference(forward_demodulation,[],[f289,f18])).

fof(f289,plain,(
    ! [X6,X7] : k3_xboole_0(X7,k5_xboole_0(X6,X6)) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X7,X6)) ),
    inference(superposition,[],[f36,f115])).

fof(f115,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f102,f62])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f32,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f25,f24,f24])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f264,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f259,f36])).

fof(f259,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0)))) ),
    inference(superposition,[],[f189,f27])).

fof(f189,plain,(
    ! [X9] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f175,f102])).

fof(f175,plain,(
    ! [X9] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)))) ),
    inference(superposition,[],[f31,f102])).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f22,f24,f28])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f320,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f315,f116])).

fof(f315,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(backward_demodulation,[],[f262,f313])).

fof(f262,plain,(
    ! [X0,X1] : k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X1)) ),
    inference(superposition,[],[f27,f189])).

fof(f2513,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f2512,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2512,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f2509,f18])).

fof(f2509,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f485,f2508])).

fof(f2508,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1 ),
    inference(forward_demodulation,[],[f2430,f20])).

fof(f2430,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),X1))) = X1 ),
    inference(superposition,[],[f191,f43])).

fof(f43,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f26,f20])).

fof(f191,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(forward_demodulation,[],[f176,f116])).

fof(f176,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f104,f31])).

fof(f104,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f37,f102])).

fof(f485,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f484,f36])).

fof(f484,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f483,f26])).

fof(f483,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) ),
    inference(superposition,[],[f35,f26])).

fof(f35,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f34,f27])).

fof(f34,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f33,f21])).

fof(f33,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f29,f21])).

fof(f29,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f24,f28])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (4616)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (4615)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (4617)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (4613)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (4612)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (4625)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (4627)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (4622)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (4623)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (4629)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (4623)Refutation not found, incomplete strategy% (4623)------------------------------
% 0.21/0.48  % (4623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (4623)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (4623)Memory used [KB]: 10490
% 0.21/0.48  % (4623)Time elapsed: 0.070 s
% 0.21/0.48  % (4623)------------------------------
% 0.21/0.48  % (4623)------------------------------
% 0.21/0.49  % (4619)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (4618)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (4611)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (4621)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (4624)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (4626)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (4628)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (4620)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.59/0.59  % (4612)Refutation found. Thanks to Tanya!
% 1.59/0.59  % SZS status Theorem for theBenchmark
% 1.59/0.59  % SZS output start Proof for theBenchmark
% 1.59/0.59  fof(f2517,plain,(
% 1.59/0.59    $false),
% 1.59/0.59    inference(trivial_inequality_removal,[],[f2516])).
% 1.59/0.59  fof(f2516,plain,(
% 1.59/0.59    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1)),
% 1.59/0.59    inference(forward_demodulation,[],[f2515,f102])).
% 1.59/0.59  fof(f102,plain,(
% 1.59/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.59/0.59    inference(superposition,[],[f37,f62])).
% 1.59/0.59  fof(f62,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0) )),
% 1.59/0.59    inference(superposition,[],[f37,f30])).
% 1.59/0.59  fof(f30,plain,(
% 1.59/0.59    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 1.59/0.59    inference(definition_unfolding,[],[f19,f28])).
% 1.59/0.59  fof(f28,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f23,f24])).
% 1.59/0.59  fof(f24,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f4])).
% 1.59/0.59  fof(f4,axiom,(
% 1.59/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.59  fof(f23,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f10])).
% 1.59/0.59  fof(f10,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.59/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.59/0.59  fof(f19,plain,(
% 1.59/0.59    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.59/0.59    inference(cnf_transformation,[],[f13])).
% 1.59/0.59  fof(f13,plain,(
% 1.59/0.59    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.59/0.59    inference(rectify,[],[f3])).
% 1.59/0.59  fof(f3,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.59/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.59/0.59  fof(f37,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.59/0.59    inference(superposition,[],[f26,f18])).
% 1.59/0.59  fof(f18,plain,(
% 1.59/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f9])).
% 1.59/0.59  fof(f9,axiom,(
% 1.59/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.59/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.59/0.59  fof(f26,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f8])).
% 1.59/0.60  fof(f8,axiom,(
% 1.59/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.59/0.60  fof(f2515,plain,(
% 1.59/0.60    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k1_xboole_0,sK1))),
% 1.59/0.60    inference(forward_demodulation,[],[f2514,f20])).
% 1.59/0.60  fof(f20,plain,(
% 1.59/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f2])).
% 1.59/0.60  fof(f2,axiom,(
% 1.59/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.59/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.59/0.60  fof(f2514,plain,(
% 1.59/0.60    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),
% 1.59/0.60    inference(forward_demodulation,[],[f2513,f322])).
% 1.59/0.60  fof(f322,plain,(
% 1.59/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.59/0.60    inference(backward_demodulation,[],[f320,f321])).
% 1.59/0.60  fof(f321,plain,(
% 1.59/0.60    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,X3))) )),
% 1.59/0.60    inference(forward_demodulation,[],[f316,f116])).
% 1.59/0.60  fof(f116,plain,(
% 1.59/0.60    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.59/0.60    inference(superposition,[],[f102,f20])).
% 1.59/0.60  fof(f316,plain,(
% 1.59/0.60    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k5_xboole_0(X3,k1_xboole_0)))) )),
% 1.59/0.60    inference(backward_demodulation,[],[f264,f313])).
% 1.59/0.60  fof(f313,plain,(
% 1.59/0.60    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)) )),
% 1.59/0.60    inference(forward_demodulation,[],[f312,f18])).
% 1.59/0.60  fof(f312,plain,(
% 1.59/0.60    ( ! [X6,X7] : (k1_xboole_0 = k3_xboole_0(X7,k5_xboole_0(X6,X6))) )),
% 1.59/0.60    inference(forward_demodulation,[],[f289,f18])).
% 1.59/0.60  fof(f289,plain,(
% 1.59/0.60    ( ! [X6,X7] : (k3_xboole_0(X7,k5_xboole_0(X6,X6)) = k5_xboole_0(k3_xboole_0(X7,X6),k3_xboole_0(X7,X6))) )),
% 1.59/0.60    inference(superposition,[],[f36,f115])).
% 1.59/0.60  fof(f115,plain,(
% 1.59/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.59/0.60    inference(superposition,[],[f102,f62])).
% 1.59/0.60  fof(f36,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 1.59/0.60    inference(backward_demodulation,[],[f32,f27])).
% 1.59/0.61  fof(f27,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.59/0.61    inference(cnf_transformation,[],[f5])).
% 1.59/0.61  fof(f5,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.59/0.61  fof(f32,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f25,f24,f24])).
% 1.59/0.61  fof(f25,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f7])).
% 1.59/0.61  fof(f7,axiom,(
% 1.59/0.61    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.59/0.61  fof(f264,plain,(
% 1.59/0.61    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0))))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f259,f36])).
% 1.59/0.61  fof(f259,plain,(
% 1.59/0.61    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,k3_xboole_0(X3,k1_xboole_0))))) )),
% 1.59/0.61    inference(superposition,[],[f189,f27])).
% 1.59/0.61  fof(f189,plain,(
% 1.59/0.61    ( ! [X9] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0)))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f175,f102])).
% 1.59/0.61  fof(f175,plain,(
% 1.59/0.61    ( ! [X9] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X9,k3_xboole_0(X9,k1_xboole_0))))) )),
% 1.59/0.61    inference(superposition,[],[f31,f102])).
% 1.59/0.61  fof(f31,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 1.59/0.61    inference(definition_unfolding,[],[f22,f24,f28])).
% 1.59/0.61  fof(f22,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.59/0.61    inference(cnf_transformation,[],[f6])).
% 1.59/0.61  fof(f6,axiom,(
% 1.59/0.61    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.59/0.61  fof(f320,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) )),
% 1.59/0.61    inference(forward_demodulation,[],[f315,f116])).
% 1.59/0.61  fof(f315,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X1))) )),
% 1.59/0.61    inference(backward_demodulation,[],[f262,f313])).
% 1.59/0.61  fof(f262,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(k1_xboole_0,X1) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)),X1))) )),
% 1.59/0.61    inference(superposition,[],[f27,f189])).
% 1.59/0.61  fof(f2513,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK0)))),
% 1.59/0.61    inference(forward_demodulation,[],[f2512,f21])).
% 1.59/0.61  fof(f21,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f1])).
% 1.59/0.61  fof(f1,axiom,(
% 1.59/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.59/0.61  fof(f2512,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0)))),
% 1.59/0.61    inference(forward_demodulation,[],[f2509,f18])).
% 1.59/0.61  fof(f2509,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 1.59/0.61    inference(backward_demodulation,[],[f485,f2508])).
% 1.59/0.61  fof(f2508,plain,(
% 1.59/0.61    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X1) )),
% 1.59/0.61    inference(forward_demodulation,[],[f2430,f20])).
% 1.59/0.61  fof(f2430,plain,(
% 1.59/0.61    ( ! [X2,X1] : (k3_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),X1))) = X1) )),
% 1.59/0.61    inference(superposition,[],[f191,f43])).
% 1.59/0.61  fof(f43,plain,(
% 1.59/0.61    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 1.59/0.61    inference(superposition,[],[f26,f20])).
% 1.59/0.61  fof(f191,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 1.59/0.61    inference(forward_demodulation,[],[f176,f116])).
% 1.59/0.61  fof(f176,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k5_xboole_0(X0,k1_xboole_0)) )),
% 1.59/0.61    inference(superposition,[],[f104,f31])).
% 1.59/0.61  fof(f104,plain,(
% 1.59/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.59/0.61    inference(backward_demodulation,[],[f37,f102])).
% 1.59/0.61  fof(f485,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 1.59/0.61    inference(forward_demodulation,[],[f484,f36])).
% 1.59/0.61  fof(f484,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 1.59/0.61    inference(forward_demodulation,[],[f483,f26])).
% 1.59/0.61  fof(f483,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))),
% 1.59/0.61    inference(superposition,[],[f35,f26])).
% 1.59/0.61  fof(f35,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.59/0.61    inference(backward_demodulation,[],[f34,f27])).
% 1.59/0.61  fof(f34,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 1.59/0.61    inference(forward_demodulation,[],[f33,f21])).
% 1.59/0.61  fof(f33,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 1.59/0.61    inference(backward_demodulation,[],[f29,f21])).
% 1.59/0.61  fof(f29,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 1.59/0.61    inference(definition_unfolding,[],[f17,f24,f28])).
% 1.59/0.61  fof(f17,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.59/0.61    inference(cnf_transformation,[],[f16])).
% 1.59/0.61  fof(f16,plain,(
% 1.59/0.61    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.59/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 1.59/0.61  fof(f15,plain,(
% 1.59/0.61    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.59/0.61    introduced(choice_axiom,[])).
% 1.59/0.61  fof(f14,plain,(
% 1.59/0.61    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.59/0.61    inference(ennf_transformation,[],[f12])).
% 1.59/0.61  fof(f12,negated_conjecture,(
% 1.59/0.61    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.59/0.61    inference(negated_conjecture,[],[f11])).
% 1.59/0.61  fof(f11,conjecture,(
% 1.59/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.59/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 1.59/0.61  % SZS output end Proof for theBenchmark
% 1.59/0.61  % (4612)------------------------------
% 1.59/0.61  % (4612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (4612)Termination reason: Refutation
% 1.59/0.61  
% 1.59/0.61  % (4612)Memory used [KB]: 4221
% 1.59/0.61  % (4612)Time elapsed: 0.147 s
% 1.59/0.61  % (4612)------------------------------
% 1.59/0.61  % (4612)------------------------------
% 1.59/0.61  % (4610)Success in time 0.255 s
%------------------------------------------------------------------------------
