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
% DateTime   : Thu Dec  3 12:31:56 EST 2020

% Result     : Theorem 11.63s
% Output     : Refutation 11.63s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 546 expanded)
%              Number of leaves         :   15 ( 189 expanded)
%              Depth                    :   18
%              Number of atoms          :   90 ( 547 expanded)
%              Number of equality atoms :   89 ( 546 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25664,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25662,f2373])).

fof(f2373,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X36,k4_xboole_0(X36,X35))) ),
    inference(forward_demodulation,[],[f2295,f490])).

fof(f490,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f25,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2295,plain,(
    ! [X35,X36] : k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,k4_xboole_0(X35,X36))))) ),
    inference(superposition,[],[f1155,f359])).

fof(f359,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9) ),
    inference(superposition,[],[f331,f183])).

fof(f183,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2 ),
    inference(superposition,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f331,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f293,f26])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f293,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f231,f272])).

fof(f272,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f229,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(backward_demodulation,[],[f35,f22])).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f21,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f229,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f202,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f202,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f174,f53])).

fof(f53,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f37,f41])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f174,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f36,f22])).

fof(f231,plain,(
    ! [X4,X3] : k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f32,f202])).

fof(f1155,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13 ),
    inference(forward_demodulation,[],[f1116,f490])).

fof(f1116,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,X13))),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13 ),
    inference(superposition,[],[f39,f36])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f25662,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f5383,f25661])).

fof(f25661,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X23,X24) = k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24)) ),
    inference(forward_demodulation,[],[f25660,f41])).

fof(f25660,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k4_xboole_0(X23,k2_xboole_0(k1_xboole_0,X24)) ),
    inference(forward_demodulation,[],[f25659,f32])).

fof(f25659,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k4_xboole_0(k4_xboole_0(X23,k1_xboole_0),X24) ),
    inference(forward_demodulation,[],[f25426,f331])).

fof(f25426,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,k2_xboole_0(X22,X23))),X24) = k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24)) ),
    inference(superposition,[],[f185,f25106])).

fof(f25106,plain,(
    ! [X10,X11] : k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X10,X11),X11) ),
    inference(forward_demodulation,[],[f25105,f41])).

fof(f25105,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(X10,k2_xboole_0(k1_xboole_0,X11)) ),
    inference(forward_demodulation,[],[f25104,f32])).

fof(f25104,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k4_xboole_0(X10,k1_xboole_0),X11) ),
    inference(forward_demodulation,[],[f24940,f293])).

fof(f24940,plain,(
    ! [X10,X11] : k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X10,X11))),X11) = k4_xboole_0(k2_xboole_0(X10,X11),X11) ),
    inference(superposition,[],[f185,f24644])).

fof(f24644,plain,(
    ! [X48,X49] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X49,X48),X49),X48) = X48 ),
    inference(superposition,[],[f101,f24396])).

fof(f24396,plain,(
    ! [X30,X31] : k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),X30)) = X31 ),
    inference(forward_demodulation,[],[f24172,f23])).

fof(f24172,plain,(
    ! [X30,X31] : k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),k2_xboole_0(X30,k1_xboole_0))) = X31 ),
    inference(superposition,[],[f261,f202])).

fof(f261,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X9,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9))))) = X9 ),
    inference(forward_demodulation,[],[f246,f32])).

fof(f246,plain,(
    ! [X8,X7,X9] : k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9)))) = X9 ),
    inference(superposition,[],[f183,f32])).

fof(f101,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f75,f26])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f185,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8) ),
    inference(superposition,[],[f32,f36])).

fof(f5383,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f34,f5292])).

fof(f5292,plain,(
    ! [X72,X71,X73] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X71,X73),k4_xboole_0(X72,X71)),k2_xboole_0(X71,X72)) ),
    inference(superposition,[],[f2466,f1567])).

fof(f1567,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f428,f1459])).

fof(f1459,plain,(
    ! [X57,X58,X56] : k2_xboole_0(X58,X56) = k2_xboole_0(X56,k2_xboole_0(X58,k4_xboole_0(X56,X57))) ),
    inference(superposition,[],[f85,f522])).

fof(f522,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),X4) = X4 ),
    inference(backward_demodulation,[],[f184,f490])).

fof(f184,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))),X4) = X4 ),
    inference(superposition,[],[f123,f36])).

fof(f123,plain,(
    ! [X10,X11] : k2_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X10) = X10 ),
    inference(superposition,[],[f101,f37])).

fof(f85,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f33,f26])).

fof(f428,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f403,f22])).

fof(f403,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k2_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f182,f229])).

fof(f182,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = X0 ),
    inference(superposition,[],[f123,f36])).

fof(f2466,plain,(
    ! [X47,X48,X49] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X47,X48),X49),k2_xboole_0(X47,X49)) ),
    inference(superposition,[],[f331,f544])).

fof(f544,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,X8) = k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)) ),
    inference(superposition,[],[f33,f521])).

fof(f521,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = X9 ),
    inference(backward_demodulation,[],[f186,f490])).

fof(f186,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9)))) = X9 ),
    inference(superposition,[],[f37,f36])).

fof(f34,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f20,f28,f31,f31])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (1308)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (1297)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (1296)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (1300)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (1307)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (1298)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (1299)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (1301)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (1303)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (1293)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (1294)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (1304)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (1304)Refutation not found, incomplete strategy% (1304)------------------------------
% 0.20/0.49  % (1304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1304)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (1304)Memory used [KB]: 10490
% 0.20/0.49  % (1304)Time elapsed: 0.071 s
% 0.20/0.49  % (1304)------------------------------
% 0.20/0.49  % (1304)------------------------------
% 0.20/0.49  % (1305)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (1302)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (1295)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (1310)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (1309)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.52  % (1306)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 4.96/1.04  % (1297)Time limit reached!
% 4.96/1.04  % (1297)------------------------------
% 4.96/1.04  % (1297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.96/1.04  % (1297)Termination reason: Time limit
% 4.96/1.04  
% 4.96/1.04  % (1297)Memory used [KB]: 16502
% 4.96/1.04  % (1297)Time elapsed: 0.622 s
% 4.96/1.04  % (1297)------------------------------
% 4.96/1.04  % (1297)------------------------------
% 11.63/1.84  % (1302)Refutation found. Thanks to Tanya!
% 11.63/1.84  % SZS status Theorem for theBenchmark
% 11.63/1.85  % SZS output start Proof for theBenchmark
% 11.63/1.85  fof(f25664,plain,(
% 11.63/1.85    $false),
% 11.63/1.85    inference(subsumption_resolution,[],[f25662,f2373])).
% 11.63/1.85  fof(f2373,plain,(
% 11.63/1.85    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X36,k4_xboole_0(X36,X35)))) )),
% 11.63/1.85    inference(forward_demodulation,[],[f2295,f490])).
% 11.63/1.85  fof(f490,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 11.63/1.85    inference(superposition,[],[f38,f36])).
% 11.63/1.85  fof(f36,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.63/1.85    inference(definition_unfolding,[],[f25,f28,f28])).
% 11.63/1.85  fof(f28,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.63/1.85    inference(cnf_transformation,[],[f10])).
% 11.63/1.85  fof(f10,axiom,(
% 11.63/1.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 11.63/1.85  fof(f25,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.63/1.85    inference(cnf_transformation,[],[f2])).
% 11.63/1.85  fof(f2,axiom,(
% 11.63/1.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 11.63/1.85  fof(f38,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.63/1.85    inference(definition_unfolding,[],[f29,f28])).
% 11.63/1.85  fof(f29,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.63/1.85    inference(cnf_transformation,[],[f9])).
% 11.63/1.85  fof(f9,axiom,(
% 11.63/1.85    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 11.63/1.85  fof(f2295,plain,(
% 11.63/1.85    ( ! [X35,X36] : (k4_xboole_0(X35,k4_xboole_0(X35,X36)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X35,k4_xboole_0(X35,X36)))))) )),
% 11.63/1.85    inference(superposition,[],[f1155,f359])).
% 11.63/1.85  fof(f359,plain,(
% 11.63/1.85    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X9)),X9)) )),
% 11.63/1.85    inference(superposition,[],[f331,f183])).
% 11.63/1.85  fof(f183,plain,(
% 11.63/1.85    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))) = X2) )),
% 11.63/1.85    inference(superposition,[],[f37,f36])).
% 11.63/1.85  fof(f37,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 11.63/1.85    inference(definition_unfolding,[],[f27,f28])).
% 11.63/1.85  fof(f27,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 11.63/1.85    inference(cnf_transformation,[],[f6])).
% 11.63/1.85  fof(f6,axiom,(
% 11.63/1.85    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 11.63/1.85  fof(f331,plain,(
% 11.63/1.85    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 11.63/1.85    inference(superposition,[],[f293,f26])).
% 11.63/1.85  fof(f26,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.63/1.85    inference(cnf_transformation,[],[f1])).
% 11.63/1.85  fof(f1,axiom,(
% 11.63/1.85    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 11.63/1.85  fof(f293,plain,(
% 11.63/1.85    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 11.63/1.85    inference(backward_demodulation,[],[f231,f272])).
% 11.63/1.85  fof(f272,plain,(
% 11.63/1.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 11.63/1.85    inference(superposition,[],[f229,f40])).
% 11.63/1.85  fof(f40,plain,(
% 11.63/1.85    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 11.63/1.85    inference(backward_demodulation,[],[f35,f22])).
% 11.63/1.85  fof(f22,plain,(
% 11.63/1.85    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.63/1.85    inference(cnf_transformation,[],[f7])).
% 11.63/1.85  fof(f7,axiom,(
% 11.63/1.85    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 11.63/1.85  fof(f35,plain,(
% 11.63/1.85    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 11.63/1.85    inference(definition_unfolding,[],[f21,f31])).
% 11.63/1.85  fof(f31,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 11.63/1.85    inference(cnf_transformation,[],[f3])).
% 11.63/1.85  fof(f3,axiom,(
% 11.63/1.85    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 11.63/1.85  fof(f21,plain,(
% 11.63/1.85    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.63/1.85    inference(cnf_transformation,[],[f13])).
% 11.63/1.85  fof(f13,axiom,(
% 11.63/1.85    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 11.63/1.85  fof(f229,plain,(
% 11.63/1.85    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 11.63/1.85    inference(superposition,[],[f202,f32])).
% 11.63/1.85  fof(f32,plain,(
% 11.63/1.85    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.63/1.85    inference(cnf_transformation,[],[f8])).
% 11.63/1.85  fof(f8,axiom,(
% 11.63/1.85    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 11.63/1.85  fof(f202,plain,(
% 11.63/1.85    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 11.63/1.85    inference(forward_demodulation,[],[f174,f53])).
% 11.63/1.85  fof(f53,plain,(
% 11.63/1.85    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 11.63/1.85    inference(superposition,[],[f37,f41])).
% 11.63/1.85  fof(f41,plain,(
% 11.63/1.85    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 11.63/1.85    inference(superposition,[],[f26,f23])).
% 11.63/1.85  fof(f23,plain,(
% 11.63/1.85    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.63/1.85    inference(cnf_transformation,[],[f5])).
% 11.63/1.85  fof(f5,axiom,(
% 11.63/1.85    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 11.63/1.85  fof(f174,plain,(
% 11.63/1.85    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 11.63/1.85    inference(superposition,[],[f36,f22])).
% 11.63/1.85  fof(f231,plain,(
% 11.63/1.85    ( ! [X4,X3] : (k4_xboole_0(k1_xboole_0,X4) = k4_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 11.63/1.85    inference(superposition,[],[f32,f202])).
% 11.63/1.85  fof(f1155,plain,(
% 11.63/1.85    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,X14),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13) )),
% 11.63/1.85    inference(forward_demodulation,[],[f1116,f490])).
% 11.63/1.85  fof(f1116,plain,(
% 11.63/1.85    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X14,k4_xboole_0(X14,X13))),k4_xboole_0(X14,k4_xboole_0(X14,X13))) = X13) )),
% 11.63/1.85    inference(superposition,[],[f39,f36])).
% 11.63/1.85  fof(f39,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 11.63/1.85    inference(definition_unfolding,[],[f30,f28])).
% 11.63/1.85  fof(f30,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 11.63/1.85    inference(cnf_transformation,[],[f12])).
% 11.63/1.85  fof(f12,axiom,(
% 11.63/1.85    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 11.63/1.85  fof(f25662,plain,(
% 11.63/1.85    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 11.63/1.85    inference(backward_demodulation,[],[f5383,f25661])).
% 11.63/1.85  fof(f25661,plain,(
% 11.63/1.85    ( ! [X24,X23,X22] : (k4_xboole_0(X23,X24) = k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24))) )),
% 11.63/1.85    inference(forward_demodulation,[],[f25660,f41])).
% 11.63/1.85  fof(f25660,plain,(
% 11.63/1.85    ( ! [X24,X23,X22] : (k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k4_xboole_0(X23,k2_xboole_0(k1_xboole_0,X24))) )),
% 11.63/1.85    inference(forward_demodulation,[],[f25659,f32])).
% 11.63/1.85  fof(f25659,plain,(
% 11.63/1.85    ( ! [X24,X23,X22] : (k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k4_xboole_0(k4_xboole_0(X23,k1_xboole_0),X24)) )),
% 11.63/1.85    inference(forward_demodulation,[],[f25426,f331])).
% 11.63/1.85  fof(f25426,plain,(
% 11.63/1.85    ( ! [X24,X23,X22] : (k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X23,k2_xboole_0(X22,X23))),X24) = k4_xboole_0(k2_xboole_0(X22,X23),k2_xboole_0(k4_xboole_0(X22,X23),X24))) )),
% 11.63/1.85    inference(superposition,[],[f185,f25106])).
% 11.63/1.85  fof(f25106,plain,(
% 11.63/1.85    ( ! [X10,X11] : (k4_xboole_0(X10,X11) = k4_xboole_0(k2_xboole_0(X10,X11),X11)) )),
% 11.63/1.85    inference(forward_demodulation,[],[f25105,f41])).
% 11.63/1.85  fof(f25105,plain,(
% 11.63/1.85    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(X10,k2_xboole_0(k1_xboole_0,X11))) )),
% 11.63/1.85    inference(forward_demodulation,[],[f25104,f32])).
% 11.63/1.85  fof(f25104,plain,(
% 11.63/1.85    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),X11) = k4_xboole_0(k4_xboole_0(X10,k1_xboole_0),X11)) )),
% 11.63/1.85    inference(forward_demodulation,[],[f24940,f293])).
% 11.63/1.85  fof(f24940,plain,(
% 11.63/1.85    ( ! [X10,X11] : (k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,k2_xboole_0(X10,X11))),X11) = k4_xboole_0(k2_xboole_0(X10,X11),X11)) )),
% 11.63/1.85    inference(superposition,[],[f185,f24644])).
% 11.63/1.85  fof(f24644,plain,(
% 11.63/1.85    ( ! [X48,X49] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X49,X48),X49),X48) = X48) )),
% 11.63/1.85    inference(superposition,[],[f101,f24396])).
% 11.63/1.85  fof(f24396,plain,(
% 11.63/1.85    ( ! [X30,X31] : (k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),X30)) = X31) )),
% 11.63/1.85    inference(forward_demodulation,[],[f24172,f23])).
% 11.63/1.85  fof(f24172,plain,(
% 11.63/1.85    ( ! [X30,X31] : (k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),k2_xboole_0(X30,k1_xboole_0))) = X31) )),
% 11.63/1.85    inference(superposition,[],[f261,f202])).
% 11.63/1.85  fof(f261,plain,(
% 11.63/1.85    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9))))) = X9) )),
% 11.63/1.85    inference(forward_demodulation,[],[f246,f32])).
% 11.63/1.85  fof(f246,plain,(
% 11.63/1.85    ( ! [X8,X7,X9] : (k2_xboole_0(X9,k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9)))) = X9) )),
% 11.63/1.85    inference(superposition,[],[f183,f32])).
% 11.63/1.85  fof(f101,plain,(
% 11.63/1.85    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 11.63/1.85    inference(superposition,[],[f75,f26])).
% 11.63/1.85  fof(f75,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 11.63/1.85    inference(superposition,[],[f33,f24])).
% 11.63/1.85  fof(f24,plain,(
% 11.63/1.85    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 11.63/1.85    inference(cnf_transformation,[],[f16])).
% 11.63/1.85  fof(f16,plain,(
% 11.63/1.85    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 11.63/1.85    inference(rectify,[],[f4])).
% 11.63/1.85  fof(f4,axiom,(
% 11.63/1.85    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 11.63/1.85  fof(f33,plain,(
% 11.63/1.85    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 11.63/1.85    inference(cnf_transformation,[],[f11])).
% 11.63/1.85  fof(f11,axiom,(
% 11.63/1.85    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 11.63/1.85  fof(f185,plain,(
% 11.63/1.85    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8)) = k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X8)) )),
% 11.63/1.85    inference(superposition,[],[f32,f36])).
% 11.63/1.85  fof(f5383,plain,(
% 11.63/1.85    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 11.63/1.85    inference(backward_demodulation,[],[f34,f5292])).
% 11.63/1.85  fof(f5292,plain,(
% 11.63/1.85    ( ! [X72,X71,X73] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X71,X73),k4_xboole_0(X72,X71)),k2_xboole_0(X71,X72))) )),
% 11.63/1.85    inference(superposition,[],[f2466,f1567])).
% 11.63/1.85  fof(f1567,plain,(
% 11.63/1.85    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 11.63/1.85    inference(backward_demodulation,[],[f428,f1459])).
% 11.63/1.85  fof(f1459,plain,(
% 11.63/1.85    ( ! [X57,X58,X56] : (k2_xboole_0(X58,X56) = k2_xboole_0(X56,k2_xboole_0(X58,k4_xboole_0(X56,X57)))) )),
% 11.63/1.85    inference(superposition,[],[f85,f522])).
% 11.63/1.85  fof(f522,plain,(
% 11.63/1.85    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),X4) = X4) )),
% 11.63/1.85    inference(backward_demodulation,[],[f184,f490])).
% 11.63/1.85  fof(f184,plain,(
% 11.63/1.85    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4))),X4) = X4) )),
% 11.63/1.85    inference(superposition,[],[f123,f36])).
% 11.63/1.85  fof(f123,plain,(
% 11.63/1.85    ( ! [X10,X11] : (k2_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),X10) = X10) )),
% 11.63/1.85    inference(superposition,[],[f101,f37])).
% 11.63/1.85  fof(f85,plain,(
% 11.63/1.85    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k2_xboole_0(X6,X7))) )),
% 11.63/1.85    inference(superposition,[],[f33,f26])).
% 11.63/1.85  fof(f428,plain,(
% 11.63/1.85    ( ! [X2,X1] : (k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 11.63/1.85    inference(forward_demodulation,[],[f403,f22])).
% 11.63/1.85  fof(f403,plain,(
% 11.63/1.85    ( ! [X2,X1] : (k2_xboole_0(X2,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k2_xboole_0(X2,k4_xboole_0(X1,X2)))) )),
% 11.63/1.85    inference(superposition,[],[f182,f229])).
% 11.63/1.85  fof(f182,plain,(
% 11.63/1.85    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) = X0) )),
% 11.63/1.85    inference(superposition,[],[f123,f36])).
% 11.63/1.85  fof(f2466,plain,(
% 11.63/1.85    ( ! [X47,X48,X49] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X47,X48),X49),k2_xboole_0(X47,X49))) )),
% 11.63/1.85    inference(superposition,[],[f331,f544])).
% 11.63/1.85  fof(f544,plain,(
% 11.63/1.85    ( ! [X6,X8,X7] : (k2_xboole_0(X6,X8) = k2_xboole_0(X6,k2_xboole_0(k4_xboole_0(X6,X7),X8))) )),
% 11.63/1.85    inference(superposition,[],[f33,f521])).
% 11.63/1.85  fof(f521,plain,(
% 11.63/1.85    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = X9) )),
% 11.63/1.85    inference(backward_demodulation,[],[f186,f490])).
% 11.63/1.85  fof(f186,plain,(
% 11.63/1.85    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X10,X9)))) = X9) )),
% 11.63/1.85    inference(superposition,[],[f37,f36])).
% 11.63/1.85  fof(f34,plain,(
% 11.63/1.85    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 11.63/1.85    inference(definition_unfolding,[],[f20,f28,f31,f31])).
% 11.63/1.85  fof(f20,plain,(
% 11.63/1.85    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.63/1.85    inference(cnf_transformation,[],[f19])).
% 11.63/1.85  fof(f19,plain,(
% 11.63/1.85    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.63/1.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f18])).
% 11.63/1.85  fof(f18,plain,(
% 11.63/1.85    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.63/1.85    introduced(choice_axiom,[])).
% 11.63/1.85  fof(f17,plain,(
% 11.63/1.85    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.63/1.85    inference(ennf_transformation,[],[f15])).
% 11.63/1.85  fof(f15,negated_conjecture,(
% 11.63/1.85    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.63/1.85    inference(negated_conjecture,[],[f14])).
% 11.63/1.85  fof(f14,conjecture,(
% 11.63/1.85    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.63/1.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 11.63/1.85  % SZS output end Proof for theBenchmark
% 11.63/1.85  % (1302)------------------------------
% 11.63/1.85  % (1302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.63/1.85  % (1302)Termination reason: Refutation
% 11.63/1.85  
% 11.63/1.85  % (1302)Memory used [KB]: 33261
% 11.63/1.85  % (1302)Time elapsed: 1.430 s
% 11.63/1.85  % (1302)------------------------------
% 11.63/1.85  % (1302)------------------------------
% 11.63/1.85  % (1292)Success in time 1.496 s
%------------------------------------------------------------------------------
