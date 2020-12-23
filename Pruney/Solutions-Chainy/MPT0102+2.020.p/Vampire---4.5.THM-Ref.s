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

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 950 expanded)
%              Number of leaves         :   13 ( 324 expanded)
%              Depth                    :   21
%              Number of atoms          :   81 ( 951 expanded)
%              Number of equality atoms :   80 ( 950 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3564,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3563])).

fof(f3563,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f3452,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3452,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3451,f1555])).

fof(f1555,plain,(
    ! [X10,X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X8,X10))) ),
    inference(superposition,[],[f540,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f540,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f531,f309])).

fof(f309,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f288,f193])).

fof(f193,plain,(
    ! [X7] : k2_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0)) = X7 ),
    inference(superposition,[],[f32,f161])).

fof(f161,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(X12,k4_xboole_0(X12,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f136,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f57,f45])).

fof(f45,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f25,f35])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f57,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f32,f35])).

fof(f136,plain,(
    ! [X12] : k4_xboole_0(X12,k4_xboole_0(X12,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X12,X12)) ),
    inference(superposition,[],[f31,f45])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f288,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(superposition,[],[f162,f28])).

fof(f162,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(X8,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f106,f161])).

fof(f106,plain,(
    ! [X8] : k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0)) ),
    inference(superposition,[],[f43,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f43,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f25,f21])).

fof(f531,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X4)) ),
    inference(superposition,[],[f28,f514])).

fof(f514,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f512,f311])).

fof(f311,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f45,f309])).

fof(f512,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f43,f489])).

fof(f489,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f147,f464])).

fof(f464,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f147,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5)))) = X5 ),
    inference(superposition,[],[f32,f31])).

fof(f3451,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3448,f28])).

fof(f3448,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f612,f3384])).

fof(f3384,plain,(
    ! [X61,X62,X63] : k4_xboole_0(X63,k2_xboole_0(X62,X61)) = k4_xboole_0(k2_xboole_0(X63,k4_xboole_0(X61,X62)),k2_xboole_0(X62,X61)) ),
    inference(superposition,[],[f68,f978])).

fof(f978,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),X12) ),
    inference(forward_demodulation,[],[f944,f43])).

fof(f944,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),X12),X12) ),
    inference(superposition,[],[f34,f372])).

fof(f372,plain,(
    ! [X8,X7] : k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7 ),
    inference(backward_demodulation,[],[f331,f354])).

fof(f354,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f310,f19])).

fof(f310,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f30,f309])).

fof(f331,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) ),
    inference(backward_demodulation,[],[f134,f330])).

fof(f330,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f316,f309])).

fof(f316,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f59,f309])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(superposition,[],[f28,f45])).

fof(f134,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X7,X8))) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f31,f43])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f68,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f60,f28])).

fof(f60,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f28,f25])).

fof(f612,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f611,f31])).

fof(f611,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f29,f588])).

fof(f588,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f28,f446])).

fof(f446,plain,(
    ! [X6,X5] : k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X6 ),
    inference(forward_demodulation,[],[f445,f354])).

fof(f445,plain,(
    ! [X6,X5] : k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f133,f433])).

fof(f433,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f330,f21])).

fof(f133,plain,(
    ! [X6,X5] : k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f31,f25])).

fof(f29,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f17,f23,f27,f27])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (3449)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (3451)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (3454)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (3459)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (3458)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (3457)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (3447)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (3457)Refutation not found, incomplete strategy% (3457)------------------------------
% 0.21/0.48  % (3457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3457)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (3457)Memory used [KB]: 10490
% 0.21/0.48  % (3457)Time elapsed: 0.072 s
% 0.21/0.48  % (3457)------------------------------
% 0.21/0.48  % (3457)------------------------------
% 0.21/0.48  % (3460)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (3450)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (3462)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.49  % (3446)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (3448)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (3452)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (3456)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (3455)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (3453)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (3461)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.29/0.53  % (3463)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.16/0.64  % (3447)Refutation found. Thanks to Tanya!
% 2.16/0.64  % SZS status Theorem for theBenchmark
% 2.16/0.64  % SZS output start Proof for theBenchmark
% 2.16/0.64  fof(f3564,plain,(
% 2.16/0.64    $false),
% 2.16/0.64    inference(trivial_inequality_removal,[],[f3563])).
% 2.16/0.64  fof(f3563,plain,(
% 2.16/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.16/0.64    inference(superposition,[],[f3452,f35])).
% 2.16/0.64  fof(f35,plain,(
% 2.16/0.64    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.16/0.64    inference(superposition,[],[f21,f19])).
% 2.16/0.64  fof(f19,plain,(
% 2.16/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f4])).
% 2.16/0.64  fof(f4,axiom,(
% 2.16/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.16/0.64  fof(f21,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f1])).
% 2.16/0.64  fof(f1,axiom,(
% 2.16/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.16/0.64  fof(f3452,plain,(
% 2.16/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.16/0.64    inference(forward_demodulation,[],[f3451,f1555])).
% 2.16/0.64  fof(f1555,plain,(
% 2.16/0.64    ( ! [X10,X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k2_xboole_0(X9,k2_xboole_0(X8,X10)))) )),
% 2.16/0.64    inference(superposition,[],[f540,f28])).
% 2.16/0.64  fof(f28,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f7])).
% 2.16/0.64  fof(f7,axiom,(
% 2.16/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.16/0.64  fof(f540,plain,(
% 2.16/0.64    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X4))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f531,f309])).
% 2.16/0.64  fof(f309,plain,(
% 2.16/0.64    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 2.16/0.64    inference(forward_demodulation,[],[f288,f193])).
% 2.16/0.64  fof(f193,plain,(
% 2.16/0.64    ( ! [X7] : (k2_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0)) = X7) )),
% 2.16/0.64    inference(superposition,[],[f32,f161])).
% 2.16/0.64  fof(f161,plain,(
% 2.16/0.64    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(X12,k4_xboole_0(X12,k1_xboole_0))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f136,f74])).
% 2.16/0.64  fof(f74,plain,(
% 2.16/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(X0,X0))) )),
% 2.16/0.64    inference(superposition,[],[f57,f45])).
% 2.16/0.64  fof(f45,plain,(
% 2.16/0.64    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5)) )),
% 2.16/0.64    inference(superposition,[],[f25,f35])).
% 2.16/0.64  fof(f25,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f6])).
% 2.16/0.64  fof(f6,axiom,(
% 2.16/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.16/0.64  fof(f57,plain,(
% 2.16/0.64    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 2.16/0.64    inference(superposition,[],[f32,f35])).
% 2.16/0.64  fof(f136,plain,(
% 2.16/0.64    ( ! [X12] : (k4_xboole_0(X12,k4_xboole_0(X12,k1_xboole_0)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X12,X12))) )),
% 2.16/0.64    inference(superposition,[],[f31,f45])).
% 2.16/0.64  fof(f31,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.16/0.64    inference(definition_unfolding,[],[f20,f23,f23])).
% 2.16/0.64  fof(f23,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f9])).
% 2.16/0.64  fof(f9,axiom,(
% 2.16/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.16/0.64  fof(f20,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f2])).
% 2.16/0.64  fof(f2,axiom,(
% 2.16/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.16/0.64  fof(f32,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 2.16/0.64    inference(definition_unfolding,[],[f22,f23])).
% 2.16/0.64  fof(f22,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f5])).
% 2.16/0.64  fof(f5,axiom,(
% 2.16/0.64    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.16/0.64  fof(f288,plain,(
% 2.16/0.64    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 2.16/0.64    inference(superposition,[],[f162,f28])).
% 2.16/0.64  fof(f162,plain,(
% 2.16/0.64    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(X8,k1_xboole_0))) )),
% 2.16/0.64    inference(backward_demodulation,[],[f106,f161])).
% 2.16/0.64  fof(f106,plain,(
% 2.16/0.64    ( ! [X8] : (k4_xboole_0(k4_xboole_0(k1_xboole_0,X8),k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(X8,k4_xboole_0(X8,k1_xboole_0))) )),
% 2.16/0.64    inference(superposition,[],[f43,f30])).
% 2.16/0.64  fof(f30,plain,(
% 2.16/0.64    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 2.16/0.64    inference(definition_unfolding,[],[f18,f27])).
% 2.16/0.64  fof(f27,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f3])).
% 2.16/0.64  fof(f3,axiom,(
% 2.16/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.16/0.64  fof(f18,plain,(
% 2.16/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f11])).
% 2.16/0.64  fof(f11,axiom,(
% 2.16/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.16/0.64  fof(f43,plain,(
% 2.16/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 2.16/0.64    inference(superposition,[],[f25,f21])).
% 2.16/0.64  fof(f531,plain,(
% 2.16/0.64    ( ! [X4,X2,X3] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X4))) )),
% 2.16/0.64    inference(superposition,[],[f28,f514])).
% 2.16/0.64  fof(f514,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.16/0.64    inference(forward_demodulation,[],[f512,f311])).
% 2.16/0.64  fof(f311,plain,(
% 2.16/0.64    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) )),
% 2.16/0.64    inference(backward_demodulation,[],[f45,f309])).
% 2.16/0.64  fof(f512,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.16/0.64    inference(superposition,[],[f43,f489])).
% 2.16/0.64  fof(f489,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 2.16/0.64    inference(backward_demodulation,[],[f147,f464])).
% 2.16/0.64  fof(f464,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 2.16/0.64    inference(superposition,[],[f33,f31])).
% 2.16/0.64  fof(f33,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.16/0.64    inference(definition_unfolding,[],[f24,f23])).
% 2.16/0.64  fof(f24,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f8])).
% 2.16/0.64  fof(f8,axiom,(
% 2.16/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.16/0.64  fof(f147,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X6,k4_xboole_0(X6,X5)))) = X5) )),
% 2.16/0.64    inference(superposition,[],[f32,f31])).
% 2.16/0.64  fof(f3451,plain,(
% 2.16/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,k2_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.16/0.64    inference(forward_demodulation,[],[f3448,f28])).
% 2.16/0.64  fof(f3448,plain,(
% 2.16/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.16/0.64    inference(backward_demodulation,[],[f612,f3384])).
% 2.16/0.64  fof(f3384,plain,(
% 2.16/0.64    ( ! [X61,X62,X63] : (k4_xboole_0(X63,k2_xboole_0(X62,X61)) = k4_xboole_0(k2_xboole_0(X63,k4_xboole_0(X61,X62)),k2_xboole_0(X62,X61))) )),
% 2.16/0.64    inference(superposition,[],[f68,f978])).
% 2.16/0.64  fof(f978,plain,(
% 2.16/0.64    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(X13,X12),X12)) )),
% 2.16/0.64    inference(forward_demodulation,[],[f944,f43])).
% 2.16/0.64  fof(f944,plain,(
% 2.16/0.64    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X12,X13),X12),X12)) )),
% 2.16/0.64    inference(superposition,[],[f34,f372])).
% 2.16/0.64  fof(f372,plain,(
% 2.16/0.64    ( ! [X8,X7] : (k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7) )),
% 2.16/0.64    inference(backward_demodulation,[],[f331,f354])).
% 2.16/0.64  fof(f354,plain,(
% 2.16/0.64    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.16/0.64    inference(superposition,[],[f310,f19])).
% 2.16/0.64  fof(f310,plain,(
% 2.16/0.64    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 2.16/0.64    inference(backward_demodulation,[],[f30,f309])).
% 2.16/0.64  fof(f331,plain,(
% 2.16/0.64    ( ! [X8,X7] : (k4_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7))) )),
% 2.16/0.64    inference(backward_demodulation,[],[f134,f330])).
% 2.16/0.64  fof(f330,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f316,f309])).
% 2.16/0.64  fof(f316,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.16/0.64    inference(backward_demodulation,[],[f59,f309])).
% 2.16/0.64  fof(f59,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) )),
% 2.16/0.64    inference(superposition,[],[f28,f45])).
% 2.16/0.64  fof(f134,plain,(
% 2.16/0.64    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(X7,X8))) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7))) )),
% 2.16/0.64    inference(superposition,[],[f31,f43])).
% 2.16/0.64  fof(f34,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.16/0.64    inference(definition_unfolding,[],[f26,f23])).
% 2.16/0.64  fof(f26,plain,(
% 2.16/0.64    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.16/0.64    inference(cnf_transformation,[],[f10])).
% 2.16/0.64  fof(f10,axiom,(
% 2.16/0.64    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.16/0.64  fof(f68,plain,(
% 2.16/0.64    ( ! [X4,X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X3,X4))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f60,f28])).
% 2.16/0.64  fof(f60,plain,(
% 2.16/0.64    ( ! [X4,X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 2.16/0.64    inference(superposition,[],[f28,f25])).
% 2.16/0.64  fof(f612,plain,(
% 2.16/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.16/0.64    inference(forward_demodulation,[],[f611,f31])).
% 2.16/0.64  fof(f611,plain,(
% 2.16/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 2.16/0.64    inference(backward_demodulation,[],[f29,f588])).
% 2.16/0.64  fof(f588,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 2.16/0.64    inference(superposition,[],[f28,f446])).
% 2.16/0.64  fof(f446,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = X6) )),
% 2.16/0.64    inference(forward_demodulation,[],[f445,f354])).
% 2.16/0.64  fof(f445,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k4_xboole_0(X6,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.16/0.64    inference(backward_demodulation,[],[f133,f433])).
% 2.16/0.64  fof(f433,plain,(
% 2.16/0.64    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.16/0.64    inference(superposition,[],[f330,f21])).
% 2.16/0.64  fof(f133,plain,(
% 2.16/0.64    ( ! [X6,X5] : (k4_xboole_0(X6,k4_xboole_0(X6,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.16/0.64    inference(superposition,[],[f31,f25])).
% 2.16/0.64  fof(f29,plain,(
% 2.16/0.64    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 2.16/0.64    inference(definition_unfolding,[],[f17,f23,f27,f27])).
% 2.16/0.64  fof(f17,plain,(
% 2.16/0.64    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.16/0.64    inference(cnf_transformation,[],[f16])).
% 2.16/0.64  fof(f16,plain,(
% 2.16/0.64    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.16/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 2.16/0.64  fof(f15,plain,(
% 2.16/0.64    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 2.16/0.64    introduced(choice_axiom,[])).
% 2.16/0.64  fof(f14,plain,(
% 2.16/0.64    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.16/0.64    inference(ennf_transformation,[],[f13])).
% 2.16/0.64  fof(f13,negated_conjecture,(
% 2.16/0.64    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.16/0.64    inference(negated_conjecture,[],[f12])).
% 2.16/0.64  fof(f12,conjecture,(
% 2.16/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.16/0.64  % SZS output end Proof for theBenchmark
% 2.16/0.64  % (3447)------------------------------
% 2.16/0.64  % (3447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.64  % (3447)Termination reason: Refutation
% 2.16/0.64  
% 2.16/0.64  % (3447)Memory used [KB]: 3582
% 2.16/0.64  % (3447)Time elapsed: 0.220 s
% 2.16/0.64  % (3447)------------------------------
% 2.16/0.64  % (3447)------------------------------
% 2.16/0.64  % (3445)Success in time 0.278 s
%------------------------------------------------------------------------------
