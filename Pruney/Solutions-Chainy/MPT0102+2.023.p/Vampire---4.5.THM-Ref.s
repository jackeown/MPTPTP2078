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
% DateTime   : Thu Dec  3 12:31:59 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   75 (1145 expanded)
%              Number of leaves         :   12 ( 393 expanded)
%              Depth                    :   24
%              Number of atoms          :   76 (1146 expanded)
%              Number of equality atoms :   75 (1145 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1754,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1753])).

fof(f1753,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1397,f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1397,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1396,f294])).

fof(f294,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f289,f260])).

fof(f260,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4) ),
    inference(backward_demodulation,[],[f185,f233])).

fof(f233,plain,(
    ! [X7] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f30,f142])).

fof(f142,plain,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f101,f45])).

fof(f45,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6) ),
    inference(superposition,[],[f23,f32])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f29,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f185,plain,(
    ! [X4] : k4_xboole_0(k1_xboole_0,X4) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,X4)) ),
    inference(superposition,[],[f31,f142])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f28,f19])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f17,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f289,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f100,f262])).

fof(f262,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(backward_demodulation,[],[f45,f260])).

fof(f100,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f98,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f98,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f26,f73])).

fof(f73,plain,(
    ! [X6] : k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X6),X6) ),
    inference(superposition,[],[f43,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f31,f45])).

fof(f43,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f23,f21])).

fof(f1396,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1395,f507])).

fof(f507,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f488,f18])).

fof(f488,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0) ),
    inference(superposition,[],[f319,f316])).

fof(f316,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(backward_demodulation,[],[f282,f315])).

fof(f315,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(X10,k4_xboole_0(X11,X10)) ),
    inference(forward_demodulation,[],[f243,f297])).

fof(f297,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f295,f19])).

fof(f295,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0) ),
    inference(backward_demodulation,[],[f103,f294])).

fof(f103,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f29,f43])).

fof(f243,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)),k4_xboole_0(X11,X10)) ),
    inference(superposition,[],[f30,f43])).

fof(f282,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(backward_demodulation,[],[f57,f260])).

fof(f57,plain,(
    ! [X6,X5] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f45])).

fof(f319,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(X9,k4_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f242,f318])).

fof(f318,plain,(
    ! [X6,X7] : k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7 ),
    inference(forward_demodulation,[],[f317,f19])).

fof(f317,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f102,f316])).

fof(f102,plain,(
    ! [X6,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) ),
    inference(superposition,[],[f29,f23])).

fof(f242,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f30,f23])).

fof(f1395,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1393,f26])).

fof(f1393,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f453,f1355])).

fof(f1355,plain,(
    ! [X45,X43,X44] : k4_xboole_0(k2_xboole_0(X45,k4_xboole_0(X43,X44)),k2_xboole_0(X44,X43)) = k4_xboole_0(X45,k2_xboole_0(X44,X43)) ),
    inference(superposition,[],[f60,f653])).

fof(f653,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X9,X8),X8) ),
    inference(forward_demodulation,[],[f623,f43])).

fof(f623,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X8),X8) ),
    inference(superposition,[],[f30,f297])).

fof(f60,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f53,f26])).

fof(f53,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6) ),
    inference(superposition,[],[f26,f23])).

fof(f453,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f451,f29])).

fof(f451,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f27,f440])).

fof(f440,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k4_xboole_0(X8,X9),X10)) ),
    inference(superposition,[],[f26,f318])).

fof(f27,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f16,f22,f25,f25])).

fof(f16,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (25936)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (25937)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (25942)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (25943)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (25938)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (25935)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (25934)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (25941)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (25933)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (25945)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (25944)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (25946)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (25942)Refutation not found, incomplete strategy% (25942)------------------------------
% 0.22/0.52  % (25942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25942)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25942)Memory used [KB]: 10490
% 0.22/0.52  % (25942)Time elapsed: 0.082 s
% 0.22/0.52  % (25942)------------------------------
% 0.22/0.52  % (25942)------------------------------
% 0.22/0.57  % (25931)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.58  % (25940)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.58  % (25948)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.58  % (25939)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.59  % (25932)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.79/0.59  % (25947)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.96/0.62  % (25932)Refutation found. Thanks to Tanya!
% 1.96/0.62  % SZS status Theorem for theBenchmark
% 1.96/0.64  % SZS output start Proof for theBenchmark
% 1.96/0.64  fof(f1754,plain,(
% 1.96/0.64    $false),
% 1.96/0.64    inference(trivial_inequality_removal,[],[f1753])).
% 1.96/0.64  fof(f1753,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.96/0.64    inference(superposition,[],[f1397,f32])).
% 1.96/0.64  fof(f32,plain,(
% 1.96/0.64    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.96/0.64    inference(superposition,[],[f21,f18])).
% 1.96/0.64  fof(f18,plain,(
% 1.96/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.64    inference(cnf_transformation,[],[f4])).
% 1.96/0.64  fof(f4,axiom,(
% 1.96/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.96/0.64  fof(f21,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f1])).
% 1.96/0.64  fof(f1,axiom,(
% 1.96/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.96/0.64  fof(f1397,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.96/0.64    inference(forward_demodulation,[],[f1396,f294])).
% 1.96/0.64  fof(f294,plain,(
% 1.96/0.64    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,X2))) )),
% 1.96/0.64    inference(forward_demodulation,[],[f289,f260])).
% 1.96/0.64  fof(f260,plain,(
% 1.96/0.64    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X4)) )),
% 1.96/0.64    inference(backward_demodulation,[],[f185,f233])).
% 1.96/0.64  fof(f233,plain,(
% 1.96/0.64    ( ! [X7] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X7),k4_xboole_0(k1_xboole_0,X7))) )),
% 1.96/0.64    inference(superposition,[],[f30,f142])).
% 1.96/0.64  fof(f142,plain,(
% 1.96/0.64    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) )),
% 1.96/0.64    inference(superposition,[],[f101,f45])).
% 1.96/0.64  fof(f45,plain,(
% 1.96/0.64    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6)) )),
% 1.96/0.64    inference(superposition,[],[f23,f32])).
% 1.96/0.64  fof(f23,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f6])).
% 1.96/0.64  fof(f6,axiom,(
% 1.96/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.96/0.64  fof(f101,plain,(
% 1.96/0.64    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.96/0.64    inference(superposition,[],[f29,f19])).
% 1.96/0.64  fof(f19,plain,(
% 1.96/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.64    inference(cnf_transformation,[],[f5])).
% 1.96/0.64  fof(f5,axiom,(
% 1.96/0.64    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.96/0.64  fof(f29,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.96/0.64    inference(definition_unfolding,[],[f20,f22,f22])).
% 1.96/0.64  fof(f22,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.96/0.64    inference(cnf_transformation,[],[f8])).
% 1.96/0.64  fof(f8,axiom,(
% 1.96/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.96/0.64  fof(f20,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.96/0.64    inference(cnf_transformation,[],[f2])).
% 1.96/0.64  fof(f2,axiom,(
% 1.96/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.96/0.64  fof(f30,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.96/0.64    inference(definition_unfolding,[],[f24,f22])).
% 1.96/0.64  fof(f24,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.96/0.64    inference(cnf_transformation,[],[f9])).
% 1.96/0.64  fof(f9,axiom,(
% 1.96/0.64    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.96/0.64  fof(f185,plain,(
% 1.96/0.64    ( ! [X4] : (k4_xboole_0(k1_xboole_0,X4) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X4),k4_xboole_0(k1_xboole_0,X4))) )),
% 1.96/0.64    inference(superposition,[],[f31,f142])).
% 1.96/0.64  fof(f31,plain,(
% 1.96/0.64    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.96/0.64    inference(backward_demodulation,[],[f28,f19])).
% 1.96/0.64  fof(f28,plain,(
% 1.96/0.64    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 1.96/0.64    inference(definition_unfolding,[],[f17,f25])).
% 1.96/0.64  fof(f25,plain,(
% 1.96/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.96/0.64    inference(cnf_transformation,[],[f3])).
% 1.96/0.64  fof(f3,axiom,(
% 1.96/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.96/0.64  fof(f17,plain,(
% 1.96/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.96/0.64    inference(cnf_transformation,[],[f10])).
% 1.96/0.64  fof(f10,axiom,(
% 1.96/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.96/0.64  fof(f289,plain,(
% 1.96/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,X2))) )),
% 1.96/0.64    inference(backward_demodulation,[],[f100,f262])).
% 1.96/0.64  fof(f262,plain,(
% 1.96/0.64    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 1.96/0.64    inference(backward_demodulation,[],[f45,f260])).
% 1.96/0.64  fof(f100,plain,(
% 1.96/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X2))) )),
% 1.96/0.64    inference(forward_demodulation,[],[f98,f26])).
% 1.96/0.64  fof(f26,plain,(
% 1.96/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.96/0.64    inference(cnf_transformation,[],[f7])).
% 1.96/0.64  fof(f7,axiom,(
% 1.96/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.96/0.64  fof(f98,plain,(
% 1.96/0.64    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X1),X2) = k4_xboole_0(k4_xboole_0(X1,X1),k2_xboole_0(X1,X2))) )),
% 1.96/0.64    inference(superposition,[],[f26,f73])).
% 1.96/0.64  fof(f73,plain,(
% 1.96/0.64    ( ! [X6] : (k4_xboole_0(X6,X6) = k4_xboole_0(k4_xboole_0(X6,X6),X6)) )),
% 1.96/0.64    inference(superposition,[],[f43,f50])).
% 1.96/0.64  fof(f50,plain,(
% 1.96/0.64    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.96/0.64    inference(superposition,[],[f31,f45])).
% 1.96/0.64  fof(f43,plain,(
% 1.96/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 1.96/0.64    inference(superposition,[],[f23,f21])).
% 1.96/0.64  fof(f1396,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.96/0.64    inference(forward_demodulation,[],[f1395,f507])).
% 1.96/0.64  fof(f507,plain,(
% 1.96/0.64    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.96/0.64    inference(forward_demodulation,[],[f488,f18])).
% 1.96/0.64  fof(f488,plain,(
% 1.96/0.64    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X2,X1)) = k2_xboole_0(k2_xboole_0(X2,X1),k1_xboole_0)) )),
% 1.96/0.64    inference(superposition,[],[f319,f316])).
% 1.96/0.64  fof(f316,plain,(
% 1.96/0.64    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.96/0.64    inference(backward_demodulation,[],[f282,f315])).
% 1.96/0.64  fof(f315,plain,(
% 1.96/0.64    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(X10,k4_xboole_0(X11,X10))) )),
% 1.96/0.64    inference(forward_demodulation,[],[f243,f297])).
% 1.96/0.64  fof(f297,plain,(
% 1.96/0.64    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = X8) )),
% 1.96/0.64    inference(forward_demodulation,[],[f295,f19])).
% 1.96/0.64  fof(f295,plain,(
% 1.96/0.64    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(X8,k1_xboole_0)) )),
% 1.96/0.64    inference(backward_demodulation,[],[f103,f294])).
% 1.96/0.64  fof(f103,plain,(
% 1.96/0.64    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k2_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X9,X8))) )),
% 1.96/0.64    inference(superposition,[],[f29,f43])).
% 1.96/0.64  fof(f243,plain,(
% 1.96/0.64    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X11,X10)),k4_xboole_0(X11,X10))) )),
% 1.96/0.64    inference(superposition,[],[f30,f43])).
% 1.96/0.64  fof(f282,plain,(
% 1.96/0.64    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.96/0.64    inference(backward_demodulation,[],[f57,f260])).
% 1.96/0.64  fof(f57,plain,(
% 1.96/0.64    ( ! [X6,X5] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.96/0.64    inference(superposition,[],[f26,f45])).
% 1.96/0.64  fof(f319,plain,(
% 1.96/0.64    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(X9,k4_xboole_0(X8,X9))) )),
% 1.96/0.64    inference(backward_demodulation,[],[f242,f318])).
% 1.96/0.64  fof(f318,plain,(
% 1.96/0.64    ( ! [X6,X7] : (k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7)) = X7) )),
% 1.96/0.64    inference(forward_demodulation,[],[f317,f19])).
% 1.96/0.64  fof(f317,plain,(
% 1.96/0.64    ( ! [X6,X7] : (k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 1.96/0.64    inference(backward_demodulation,[],[f102,f316])).
% 1.96/0.64  fof(f102,plain,(
% 1.96/0.64    ( ! [X6,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X6,X7))) = k4_xboole_0(k2_xboole_0(X6,X7),k4_xboole_0(X6,X7))) )),
% 1.96/0.64    inference(superposition,[],[f29,f23])).
% 1.96/0.64  fof(f242,plain,(
% 1.96/0.64    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),k4_xboole_0(X8,X9)),k4_xboole_0(X8,X9))) )),
% 1.96/0.64    inference(superposition,[],[f30,f23])).
% 1.96/0.64  fof(f1395,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.96/0.64    inference(forward_demodulation,[],[f1393,f26])).
% 1.96/0.64  fof(f1393,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.96/0.64    inference(backward_demodulation,[],[f453,f1355])).
% 1.96/0.64  fof(f1355,plain,(
% 1.96/0.64    ( ! [X45,X43,X44] : (k4_xboole_0(k2_xboole_0(X45,k4_xboole_0(X43,X44)),k2_xboole_0(X44,X43)) = k4_xboole_0(X45,k2_xboole_0(X44,X43))) )),
% 1.96/0.64    inference(superposition,[],[f60,f653])).
% 1.96/0.64  fof(f653,plain,(
% 1.96/0.64    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X9,X8),X8)) )),
% 1.96/0.64    inference(forward_demodulation,[],[f623,f43])).
% 1.96/0.64  fof(f623,plain,(
% 1.96/0.64    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X8),X8)) )),
% 1.96/0.64    inference(superposition,[],[f30,f297])).
% 1.96/0.64  fof(f60,plain,(
% 1.96/0.64    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) )),
% 1.96/0.64    inference(forward_demodulation,[],[f53,f26])).
% 1.96/0.64  fof(f53,plain,(
% 1.96/0.64    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 1.96/0.64    inference(superposition,[],[f26,f23])).
% 1.96/0.64  fof(f453,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.96/0.64    inference(forward_demodulation,[],[f451,f29])).
% 1.96/0.64  fof(f451,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 1.96/0.64    inference(backward_demodulation,[],[f27,f440])).
% 1.96/0.64  fof(f440,plain,(
% 1.96/0.64    ( ! [X10,X8,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(k4_xboole_0(X8,X9),X10))) )),
% 1.96/0.64    inference(superposition,[],[f26,f318])).
% 1.96/0.64  fof(f27,plain,(
% 1.96/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 1.96/0.64    inference(definition_unfolding,[],[f16,f22,f25,f25])).
% 1.96/0.64  fof(f16,plain,(
% 1.96/0.64    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.96/0.64    inference(cnf_transformation,[],[f15])).
% 1.96/0.64  fof(f15,plain,(
% 1.96/0.64    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.96/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 1.96/0.64  fof(f14,plain,(
% 1.96/0.64    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.96/0.64    introduced(choice_axiom,[])).
% 1.96/0.64  fof(f13,plain,(
% 1.96/0.64    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.96/0.64    inference(ennf_transformation,[],[f12])).
% 1.96/0.64  fof(f12,negated_conjecture,(
% 1.96/0.64    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.96/0.64    inference(negated_conjecture,[],[f11])).
% 1.96/0.64  fof(f11,conjecture,(
% 1.96/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.96/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.96/0.64  % SZS output end Proof for theBenchmark
% 1.96/0.64  % (25932)------------------------------
% 1.96/0.64  % (25932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.64  % (25932)Termination reason: Refutation
% 1.96/0.64  
% 1.96/0.64  % (25932)Memory used [KB]: 2686
% 1.96/0.64  % (25932)Time elapsed: 0.136 s
% 1.96/0.64  % (25932)------------------------------
% 1.96/0.64  % (25932)------------------------------
% 2.18/0.64  % (25930)Success in time 0.275 s
%------------------------------------------------------------------------------
