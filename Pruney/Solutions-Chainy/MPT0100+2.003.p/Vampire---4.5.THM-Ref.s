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
% DateTime   : Thu Dec  3 12:31:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 380 expanded)
%              Number of leaves         :   15 ( 125 expanded)
%              Depth                    :   26
%              Number of atoms          :   79 ( 381 expanded)
%              Number of equality atoms :   78 ( 380 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1740,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1739])).

fof(f1739,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f1737,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1737,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f1735,f1620])).

fof(f1620,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f1619,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1619,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f1618,f1416])).

fof(f1416,plain,(
    ! [X24,X23,X21,X22] : k4_xboole_0(X21,k2_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),X24)) = k4_xboole_0(X21,X24) ),
    inference(superposition,[],[f31,f1329])).

fof(f1329,plain,(
    ! [X37,X35,X36] : k4_xboole_0(X37,k4_xboole_0(X35,k2_xboole_0(X36,X37))) = X37 ),
    inference(superposition,[],[f1292,f31])).

fof(f1292,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9 ),
    inference(forward_demodulation,[],[f1241,f22])).

fof(f1241,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f38,f1198])).

fof(f1198,plain,(
    ! [X10,X11] : k1_xboole_0 = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f1180,f43])).

fof(f43,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f35,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f21,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1180,plain,(
    ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X11)) ),
    inference(superposition,[],[f36,f1106])).

fof(f1106,plain,(
    ! [X10,X9] : k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(forward_demodulation,[],[f1105,f22])).

fof(f1105,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),X10) ),
    inference(forward_demodulation,[],[f1104,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f46,f43])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f37,f22])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1104,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1103,f94])).

fof(f94,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f81,f90])).

fof(f90,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f80,f43])).

fof(f80,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f55,f23])).

fof(f55,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f31,f43])).

fof(f81,plain,(
    ! [X2,X1] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f55,f25])).

fof(f1103,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X9)))) ),
    inference(forward_demodulation,[],[f1102,f31])).

fof(f1102,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,X10),X9))) ),
    inference(forward_demodulation,[],[f1018,f25])).

fof(f1018,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X9),X10)) ),
    inference(superposition,[],[f41,f43])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f39,f31])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f27,f27])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f24,f27,f27])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1618,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X4)),X3))) ),
    inference(forward_demodulation,[],[f1536,f41])).

fof(f1536,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k2_xboole_0(X3,X4),X3)))) ),
    inference(superposition,[],[f40,f58])).

fof(f58,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f31,f43])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f33,f27,f27])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f1735,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1692,f25])).

fof(f1692,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f710,f1690])).

fof(f1690,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X12,X11))) = X11 ),
    inference(forward_demodulation,[],[f1689,f503])).

fof(f503,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,X12)) = X11 ),
    inference(backward_demodulation,[],[f259,f473])).

fof(f473,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f38,f36])).

fof(f259,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X11)))) = X11 ),
    inference(superposition,[],[f37,f36])).

fof(f1689,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X12,X11))) ),
    inference(forward_demodulation,[],[f1643,f25])).

fof(f1643,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,X12),X11) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X12,X11))) ),
    inference(superposition,[],[f1620,f36])).

fof(f710,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f20,f29,f27])).

fof(f20,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (18875)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.44  % (18870)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (18871)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (18880)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (18880)Refutation not found, incomplete strategy% (18880)------------------------------
% 0.21/0.47  % (18880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18880)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (18880)Memory used [KB]: 10618
% 0.21/0.47  % (18880)Time elapsed: 0.053 s
% 0.21/0.47  % (18880)------------------------------
% 0.21/0.47  % (18880)------------------------------
% 0.21/0.48  % (18870)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1740,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f1739])).
% 0.21/0.48  fof(f1739,plain,(
% 0.21/0.48    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(superposition,[],[f1737,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.48  fof(f1737,plain,(
% 0.21/0.48    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)),
% 0.21/0.48    inference(superposition,[],[f1735,f1620])).
% 0.21/0.48  fof(f1620,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1619,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f1619,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1618,f1416])).
% 0.21/0.48  fof(f1416,plain,(
% 0.21/0.48    ( ! [X24,X23,X21,X22] : (k4_xboole_0(X21,k2_xboole_0(k4_xboole_0(X22,k2_xboole_0(X23,X21)),X24)) = k4_xboole_0(X21,X24)) )),
% 0.21/0.48    inference(superposition,[],[f31,f1329])).
% 0.21/0.48  fof(f1329,plain,(
% 0.21/0.48    ( ! [X37,X35,X36] : (k4_xboole_0(X37,k4_xboole_0(X35,k2_xboole_0(X36,X37))) = X37) )),
% 0.21/0.48    inference(superposition,[],[f1292,f31])).
% 0.21/0.48  fof(f1292,plain,(
% 0.21/0.48    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1241,f22])).
% 0.21/0.48  fof(f1241,plain,(
% 0.21/0.48    ( ! [X10,X9] : (k4_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 0.21/0.48    inference(superposition,[],[f38,f1198])).
% 0.21/0.48  fof(f1198,plain,(
% 0.21/0.48    ( ! [X10,X11] : (k1_xboole_0 = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1180,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.21/0.48    inference(superposition,[],[f35,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    inference(rectify,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f21,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.48  fof(f1180,plain,(
% 0.21/0.48    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X10,X11))) = k4_xboole_0(k4_xboole_0(X10,X11),k4_xboole_0(X10,X11))) )),
% 0.21/0.48    inference(superposition,[],[f36,f1106])).
% 0.21/0.48  fof(f1106,plain,(
% 0.21/0.48    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k4_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1105,f22])).
% 0.21/0.48  fof(f1105,plain,(
% 0.21/0.48    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),X10)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1104,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f46,f43])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.48    inference(superposition,[],[f37,f22])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f26,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.49  fof(f1104,plain,(
% 0.21/0.49    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k1_xboole_0))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1103,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f81,f90])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(forward_demodulation,[],[f80,f43])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(superposition,[],[f55,f23])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 0.21/0.49    inference(superposition,[],[f31,f43])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.21/0.49    inference(superposition,[],[f55,f25])).
% 0.21/0.49  fof(f1103,plain,(
% 0.21/0.49    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(X9,k2_xboole_0(X10,X9))))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1102,f31])).
% 0.21/0.49  fof(f1102,plain,(
% 0.21/0.49    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X10,k4_xboole_0(k4_xboole_0(X9,X10),X9)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1018,f25])).
% 0.21/0.49  fof(f1018,plain,(
% 0.21/0.49    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k4_xboole_0(k4_xboole_0(X9,X10),X9),X10))) )),
% 0.21/0.49    inference(superposition,[],[f41,f43])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 0.21/0.49    inference(backward_demodulation,[],[f39,f31])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f30,f27,f27])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f24,f27,f27])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f28,f27])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.49  fof(f1618,plain,(
% 0.21/0.49    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X4)),X3)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1536,f41])).
% 0.21/0.49  fof(f1536,plain,(
% 0.21/0.49    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(k2_xboole_0(X3,X4),X3))))) )),
% 0.21/0.49    inference(superposition,[],[f40,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.21/0.49    inference(superposition,[],[f31,f43])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f33,f27,f27])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 0.21/0.49  fof(f1735,plain,(
% 0.21/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.21/0.49    inference(superposition,[],[f1692,f25])).
% 0.21/0.49  fof(f1692,plain,(
% 0.21/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.49    inference(backward_demodulation,[],[f710,f1690])).
% 0.21/0.49  fof(f1690,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X12,X11))) = X11) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1689,f503])).
% 0.21/0.49  fof(f503,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,X12)) = X11) )),
% 0.21/0.49    inference(backward_demodulation,[],[f259,f473])).
% 0.21/0.49  fof(f473,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.21/0.49    inference(superposition,[],[f38,f36])).
% 0.21/0.49  fof(f259,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X11)))) = X11) )),
% 0.21/0.49    inference(superposition,[],[f37,f36])).
% 0.21/0.49  fof(f1689,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X12,X11)))) )),
% 0.21/0.49    inference(forward_demodulation,[],[f1643,f25])).
% 0.21/0.49  fof(f1643,plain,(
% 0.21/0.49    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),X11) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X12,X11)))) )),
% 0.21/0.49    inference(superposition,[],[f1620,f36])).
% 0.21/0.49  fof(f710,plain,(
% 0.21/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.21/0.49    inference(superposition,[],[f34,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.49    inference(definition_unfolding,[],[f20,f29,f27])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (18870)------------------------------
% 0.21/0.49  % (18870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18870)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (18870)Memory used [KB]: 2942
% 0.21/0.49  % (18870)Time elapsed: 0.051 s
% 0.21/0.49  % (18870)------------------------------
% 0.21/0.49  % (18870)------------------------------
% 0.21/0.49  % (18868)Success in time 0.124 s
%------------------------------------------------------------------------------
