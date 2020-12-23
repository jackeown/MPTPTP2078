%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:22 EST 2020

% Result     : Theorem 2.30s
% Output     : Refutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   83 (3318 expanded)
%              Number of leaves         :   12 (1095 expanded)
%              Depth                    :   29
%              Number of atoms          :   89 (3879 expanded)
%              Number of equality atoms :   76 (2915 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4076,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f4075])).

fof(f4075,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f4074,f18])).

fof(f18,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f4074,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f4073,f170])).

fof(f170,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f160,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f160,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f148,f48])).

fof(f48,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f42,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(resolution,[],[f24,f31])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f148,plain,(
    ! [X6,X8,X7] : r1_xboole_0(k3_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X8))),X8) ),
    inference(forward_demodulation,[],[f138,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f33,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f27,f23,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f138,plain,(
    ! [X6,X8,X7] : r1_xboole_0(k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,k3_xboole_0(X7,X8))),X8) ),
    inference(superposition,[],[f31,f28])).

fof(f4073,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK0))) ),
    inference(forward_demodulation,[],[f4072,f20])).

fof(f4072,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f4070,f745])).

fof(f745,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(superposition,[],[f717,f242])).

fof(f242,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f241,f18])).

fof(f241,plain,(
    ! [X0] : k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f218,f57])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f26,f18])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f218,plain,(
    ! [X0] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0 ),
    inference(superposition,[],[f32,f170])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f717,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(X2,k5_xboole_0(X3,X3)) ),
    inference(backward_demodulation,[],[f415,f691])).

fof(f691,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(resolution,[],[f168,f24])).

fof(f168,plain,(
    ! [X14,X12,X13] : r1_xboole_0(k3_xboole_0(X14,X12),k5_xboole_0(X13,k3_xboole_0(X13,X12))) ),
    inference(forward_demodulation,[],[f157,f18])).

fof(f157,plain,(
    ! [X14,X12,X13] : r1_xboole_0(k3_xboole_0(X14,k5_xboole_0(X12,k1_xboole_0)),k5_xboole_0(X13,k3_xboole_0(X13,X12))) ),
    inference(superposition,[],[f148,f48])).

fof(f415,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X3,X3)) ),
    inference(forward_demodulation,[],[f414,f350])).

fof(f350,plain,(
    ! [X2,X3] : k3_xboole_0(X3,k5_xboole_0(X2,X2)) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f37,f242])).

fof(f414,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f413,f259])).

fof(f259,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f28,f242])).

fof(f413,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X2,X3)),k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f362,f20])).

fof(f362,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X2,X3),X2),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f37,f242])).

fof(f4070,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) ),
    inference(backward_demodulation,[],[f528,f4039])).

fof(f4039,plain,(
    ! [X28,X27] : k3_xboole_0(X27,k5_xboole_0(X28,k5_xboole_0(X27,k3_xboole_0(X28,X27)))) = X27 ),
    inference(backward_demodulation,[],[f3720,f3997])).

fof(f3997,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f3737,f3946])).

fof(f3946,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f3922,f18])).

fof(f3922,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f3737,f890])).

fof(f890,plain,(
    ! [X2,X3] : k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3))) ),
    inference(superposition,[],[f745,f26])).

fof(f3737,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(backward_demodulation,[],[f892,f3735])).

fof(f3735,plain,(
    ! [X8] : k5_xboole_0(k1_xboole_0,X8) = X8 ),
    inference(forward_demodulation,[],[f3681,f18])).

fof(f3681,plain,(
    ! [X8] : k5_xboole_0(X8,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X8) ),
    inference(superposition,[],[f892,f745])).

fof(f892,plain,(
    ! [X2,X3] : k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f26,f745])).

fof(f3720,plain,(
    ! [X28,X27] : k3_xboole_0(X27,k5_xboole_0(X28,k5_xboole_0(k3_xboole_0(X28,X27),X27))) = X27 ),
    inference(backward_demodulation,[],[f1708,f3719])).

fof(f3719,plain,(
    ! [X6,X7] : k5_xboole_0(X6,X7) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f3680,f57])).

fof(f3680,plain,(
    ! [X6,X7] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f892,f892])).

fof(f1708,plain,(
    ! [X28,X27] : k3_xboole_0(X27,k5_xboole_0(k1_xboole_0,k5_xboole_0(X28,k5_xboole_0(k3_xboole_0(X28,X27),X27)))) = X27 ),
    inference(forward_demodulation,[],[f1707,f26])).

fof(f1707,plain,(
    ! [X28,X27] : k3_xboole_0(X27,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X28,k3_xboole_0(X28,X27)),X27))) = X27 ),
    inference(forward_demodulation,[],[f1706,f892])).

fof(f1706,plain,(
    ! [X28,X27] : k3_xboole_0(X27,k5_xboole_0(X27,k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X28,k3_xboole_0(X28,X27)),X27)))) = X27 ),
    inference(forward_demodulation,[],[f1645,f26])).

fof(f1645,plain,(
    ! [X28,X27] : k3_xboole_0(X27,k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X27,k5_xboole_0(X28,k3_xboole_0(X28,X27))),X27))) = X27 ),
    inference(superposition,[],[f219,f32])).

fof(f219,plain,(
    ! [X2,X1] : k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2 ),
    inference(superposition,[],[f32,f20])).

fof(f528,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f527,f37])).

fof(f527,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) ),
    inference(forward_demodulation,[],[f526,f26])).

fof(f526,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) ),
    inference(superposition,[],[f36,f26])).

fof(f36,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f35,f28])).

fof(f35,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f34,f20])).

fof(f34,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f30,f20])).

fof(f30,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f23,f29])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (3859)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (3853)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (3853)Refutation not found, incomplete strategy% (3853)------------------------------
% 0.20/0.46  % (3853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (3853)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (3853)Memory used [KB]: 10490
% 0.20/0.46  % (3853)Time elapsed: 0.005 s
% 0.20/0.46  % (3853)------------------------------
% 0.20/0.46  % (3853)------------------------------
% 0.20/0.47  % (3849)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (3850)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (3842)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (3848)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (3843)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (3856)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.51  % (3846)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (3845)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.51  % (3855)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (3851)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.52  % (3847)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.52  % (3844)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.54  % (3852)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.55  % (3858)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.55  % (3857)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.56  % (3854)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 2.30/0.66  % (3843)Refutation found. Thanks to Tanya!
% 2.30/0.66  % SZS status Theorem for theBenchmark
% 2.30/0.66  % SZS output start Proof for theBenchmark
% 2.30/0.66  fof(f4076,plain,(
% 2.30/0.66    $false),
% 2.30/0.66    inference(trivial_inequality_removal,[],[f4075])).
% 2.30/0.66  fof(f4075,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1)),
% 2.30/0.66    inference(forward_demodulation,[],[f4074,f18])).
% 2.30/0.66  fof(f18,plain,(
% 2.30/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.30/0.66    inference(cnf_transformation,[],[f7])).
% 2.30/0.66  fof(f7,axiom,(
% 2.30/0.66    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.30/0.66  fof(f4074,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k1_xboole_0))),
% 2.30/0.66    inference(forward_demodulation,[],[f4073,f170])).
% 2.30/0.66  fof(f170,plain,(
% 2.30/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.30/0.66    inference(resolution,[],[f160,f24])).
% 2.30/0.66  fof(f24,plain,(
% 2.30/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.30/0.66    inference(cnf_transformation,[],[f16])).
% 2.30/0.66  fof(f16,plain,(
% 2.30/0.66    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.30/0.66    inference(nnf_transformation,[],[f2])).
% 2.30/0.66  fof(f2,axiom,(
% 2.30/0.66    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.30/0.66  fof(f160,plain,(
% 2.30/0.66    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.30/0.66    inference(superposition,[],[f148,f48])).
% 2.30/0.66  fof(f48,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 2.30/0.66    inference(superposition,[],[f42,f20])).
% 2.30/0.66  fof(f20,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f1])).
% 2.30/0.66  fof(f1,axiom,(
% 2.30/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.30/0.66  fof(f42,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.30/0.66    inference(resolution,[],[f24,f31])).
% 2.30/0.66  fof(f31,plain,(
% 2.30/0.66    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.30/0.66    inference(definition_unfolding,[],[f19,f23])).
% 2.30/0.66  fof(f23,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.30/0.66    inference(cnf_transformation,[],[f3])).
% 2.30/0.66  fof(f3,axiom,(
% 2.30/0.66    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.30/0.66  fof(f19,plain,(
% 2.30/0.66    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f8])).
% 2.30/0.66  fof(f8,axiom,(
% 2.30/0.66    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.30/0.66  fof(f148,plain,(
% 2.30/0.66    ( ! [X6,X8,X7] : (r1_xboole_0(k3_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X8))),X8)) )),
% 2.30/0.66    inference(forward_demodulation,[],[f138,f37])).
% 2.30/0.66  fof(f37,plain,(
% 2.30/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2)))) )),
% 2.30/0.66    inference(backward_demodulation,[],[f33,f28])).
% 2.30/0.66  fof(f28,plain,(
% 2.30/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.30/0.66    inference(cnf_transformation,[],[f4])).
% 2.30/0.66  fof(f4,axiom,(
% 2.30/0.66    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.30/0.66  fof(f33,plain,(
% 2.30/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 2.30/0.66    inference(definition_unfolding,[],[f27,f23,f23])).
% 2.30/0.66  fof(f27,plain,(
% 2.30/0.66    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.30/0.66    inference(cnf_transformation,[],[f6])).
% 2.30/0.66  fof(f6,axiom,(
% 2.30/0.66    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.30/0.66  fof(f138,plain,(
% 2.30/0.66    ( ! [X6,X8,X7] : (r1_xboole_0(k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,k3_xboole_0(X7,X8))),X8)) )),
% 2.30/0.66    inference(superposition,[],[f31,f28])).
% 2.30/0.66  fof(f4073,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,sK0)))),
% 2.30/0.66    inference(forward_demodulation,[],[f4072,f20])).
% 2.30/0.66  fof(f4072,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k1_xboole_0)))),
% 2.30/0.66    inference(forward_demodulation,[],[f4070,f745])).
% 2.30/0.66  fof(f745,plain,(
% 2.30/0.66    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 2.30/0.66    inference(superposition,[],[f717,f242])).
% 2.30/0.66  fof(f242,plain,(
% 2.30/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.30/0.66    inference(forward_demodulation,[],[f241,f18])).
% 2.30/0.66  fof(f241,plain,(
% 2.30/0.66    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.30/0.66    inference(forward_demodulation,[],[f218,f57])).
% 2.30/0.66  fof(f57,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 2.30/0.66    inference(superposition,[],[f26,f18])).
% 2.30/0.66  fof(f26,plain,(
% 2.30/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.30/0.66    inference(cnf_transformation,[],[f9])).
% 2.30/0.66  fof(f9,axiom,(
% 2.30/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.30/0.66  fof(f218,plain,(
% 2.30/0.66    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X0) )),
% 2.30/0.66    inference(superposition,[],[f32,f170])).
% 2.30/0.66  fof(f32,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 2.30/0.66    inference(definition_unfolding,[],[f21,f29])).
% 2.30/0.66  fof(f29,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.30/0.66    inference(definition_unfolding,[],[f22,f23])).
% 2.30/0.66  fof(f22,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.30/0.66    inference(cnf_transformation,[],[f10])).
% 2.30/0.66  fof(f10,axiom,(
% 2.30/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.30/0.66  fof(f21,plain,(
% 2.30/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.30/0.66    inference(cnf_transformation,[],[f5])).
% 2.30/0.66  fof(f5,axiom,(
% 2.30/0.66    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.30/0.66  fof(f717,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(X2,k5_xboole_0(X3,X3))) )),
% 2.30/0.66    inference(backward_demodulation,[],[f415,f691])).
% 2.30/0.66  fof(f691,plain,(
% 2.30/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X2,k3_xboole_0(X2,X1)))) )),
% 2.30/0.66    inference(resolution,[],[f168,f24])).
% 2.30/0.66  fof(f168,plain,(
% 2.30/0.66    ( ! [X14,X12,X13] : (r1_xboole_0(k3_xboole_0(X14,X12),k5_xboole_0(X13,k3_xboole_0(X13,X12)))) )),
% 2.30/0.66    inference(forward_demodulation,[],[f157,f18])).
% 2.30/0.66  fof(f157,plain,(
% 2.30/0.66    ( ! [X14,X12,X13] : (r1_xboole_0(k3_xboole_0(X14,k5_xboole_0(X12,k1_xboole_0)),k5_xboole_0(X13,k3_xboole_0(X13,X12)))) )),
% 2.30/0.66    inference(superposition,[],[f148,f48])).
% 2.30/0.66  fof(f415,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k3_xboole_0(X2,k5_xboole_0(X3,X3))) )),
% 2.30/0.66    inference(forward_demodulation,[],[f414,f350])).
% 2.30/0.66  fof(f350,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k3_xboole_0(X3,k5_xboole_0(X2,X2)) = k5_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X3,X2))) )),
% 2.30/0.66    inference(superposition,[],[f37,f242])).
% 2.30/0.66  fof(f414,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 2.30/0.66    inference(forward_demodulation,[],[f413,f259])).
% 2.30/0.66  fof(f259,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.30/0.66    inference(superposition,[],[f28,f242])).
% 2.30/0.66  fof(f413,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(X2,k3_xboole_0(X2,X3)),k3_xboole_0(X2,X3))) )),
% 2.30/0.66    inference(forward_demodulation,[],[f362,f20])).
% 2.30/0.66  fof(f362,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,k3_xboole_0(X2,X3))) = k5_xboole_0(k3_xboole_0(k3_xboole_0(X2,X3),X2),k3_xboole_0(X2,X3))) )),
% 2.30/0.66    inference(superposition,[],[f37,f242])).
% 2.30/0.66  fof(f4070,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))))),
% 2.30/0.66    inference(backward_demodulation,[],[f528,f4039])).
% 2.30/0.66  fof(f4039,plain,(
% 2.30/0.66    ( ! [X28,X27] : (k3_xboole_0(X27,k5_xboole_0(X28,k5_xboole_0(X27,k3_xboole_0(X28,X27)))) = X27) )),
% 2.30/0.66    inference(backward_demodulation,[],[f3720,f3997])).
% 2.30/0.66  fof(f3997,plain,(
% 2.30/0.66    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 2.30/0.66    inference(superposition,[],[f3737,f3946])).
% 2.30/0.66  fof(f3946,plain,(
% 2.30/0.66    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 2.30/0.66    inference(forward_demodulation,[],[f3922,f18])).
% 2.30/0.66  fof(f3922,plain,(
% 2.30/0.66    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 2.30/0.66    inference(superposition,[],[f3737,f890])).
% 2.30/0.66  fof(f890,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k1_xboole_0 = k5_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,X3)))) )),
% 2.30/0.66    inference(superposition,[],[f745,f26])).
% 2.30/0.66  fof(f3737,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 2.30/0.66    inference(backward_demodulation,[],[f892,f3735])).
% 2.30/0.66  fof(f3735,plain,(
% 2.30/0.66    ( ! [X8] : (k5_xboole_0(k1_xboole_0,X8) = X8) )),
% 2.30/0.66    inference(forward_demodulation,[],[f3681,f18])).
% 2.30/0.66  fof(f3681,plain,(
% 2.30/0.66    ( ! [X8] : (k5_xboole_0(X8,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X8)) )),
% 2.30/0.66    inference(superposition,[],[f892,f745])).
% 2.30/0.66  fof(f892,plain,(
% 2.30/0.66    ( ! [X2,X3] : (k5_xboole_0(k1_xboole_0,X3) = k5_xboole_0(X2,k5_xboole_0(X2,X3))) )),
% 2.30/0.66    inference(superposition,[],[f26,f745])).
% 2.30/0.66  fof(f3720,plain,(
% 2.30/0.66    ( ! [X28,X27] : (k3_xboole_0(X27,k5_xboole_0(X28,k5_xboole_0(k3_xboole_0(X28,X27),X27))) = X27) )),
% 2.30/0.66    inference(backward_demodulation,[],[f1708,f3719])).
% 2.30/0.66  fof(f3719,plain,(
% 2.30/0.66    ( ! [X6,X7] : (k5_xboole_0(X6,X7) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7))) )),
% 2.30/0.66    inference(forward_demodulation,[],[f3680,f57])).
% 2.30/0.66  fof(f3680,plain,(
% 2.30/0.66    ( ! [X6,X7] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k1_xboole_0,X7))) )),
% 2.30/0.66    inference(superposition,[],[f892,f892])).
% 2.30/0.66  fof(f1708,plain,(
% 2.30/0.66    ( ! [X28,X27] : (k3_xboole_0(X27,k5_xboole_0(k1_xboole_0,k5_xboole_0(X28,k5_xboole_0(k3_xboole_0(X28,X27),X27)))) = X27) )),
% 2.30/0.66    inference(forward_demodulation,[],[f1707,f26])).
% 2.30/0.66  fof(f1707,plain,(
% 2.30/0.66    ( ! [X28,X27] : (k3_xboole_0(X27,k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(X28,k3_xboole_0(X28,X27)),X27))) = X27) )),
% 2.30/0.66    inference(forward_demodulation,[],[f1706,f892])).
% 2.30/0.66  fof(f1706,plain,(
% 2.30/0.66    ( ! [X28,X27] : (k3_xboole_0(X27,k5_xboole_0(X27,k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X28,k3_xboole_0(X28,X27)),X27)))) = X27) )),
% 2.30/0.66    inference(forward_demodulation,[],[f1645,f26])).
% 2.30/0.66  fof(f1645,plain,(
% 2.30/0.66    ( ! [X28,X27] : (k3_xboole_0(X27,k5_xboole_0(X27,k5_xboole_0(k5_xboole_0(X27,k5_xboole_0(X28,k3_xboole_0(X28,X27))),X27))) = X27) )),
% 2.30/0.66    inference(superposition,[],[f219,f32])).
% 2.30/0.66  fof(f219,plain,(
% 2.30/0.66    ( ! [X2,X1] : (k3_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) = X2) )),
% 2.30/0.66    inference(superposition,[],[f32,f20])).
% 2.30/0.66  fof(f528,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 2.30/0.66    inference(forward_demodulation,[],[f527,f37])).
% 2.30/0.66  fof(f527,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))))),
% 2.30/0.66    inference(forward_demodulation,[],[f526,f26])).
% 2.30/0.66  fof(f526,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))),
% 2.30/0.66    inference(superposition,[],[f36,f26])).
% 2.30/0.66  fof(f36,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 2.30/0.66    inference(backward_demodulation,[],[f35,f28])).
% 2.30/0.66  fof(f35,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 2.30/0.66    inference(forward_demodulation,[],[f34,f20])).
% 2.30/0.66  fof(f34,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 2.30/0.66    inference(backward_demodulation,[],[f30,f20])).
% 2.30/0.66  fof(f30,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 2.30/0.66    inference(definition_unfolding,[],[f17,f23,f29])).
% 2.30/0.66  fof(f17,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.30/0.66    inference(cnf_transformation,[],[f15])).
% 2.30/0.66  fof(f15,plain,(
% 2.30/0.66    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.30/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 2.30/0.66  fof(f14,plain,(
% 2.30/0.66    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.30/0.66    introduced(choice_axiom,[])).
% 2.30/0.66  fof(f13,plain,(
% 2.30/0.66    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.30/0.66    inference(ennf_transformation,[],[f12])).
% 2.30/0.66  fof(f12,negated_conjecture,(
% 2.30/0.66    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.30/0.66    inference(negated_conjecture,[],[f11])).
% 2.30/0.66  fof(f11,conjecture,(
% 2.30/0.66    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.30/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 2.30/0.66  % SZS output end Proof for theBenchmark
% 2.30/0.66  % (3843)------------------------------
% 2.30/0.66  % (3843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.66  % (3843)Termination reason: Refutation
% 2.30/0.66  
% 2.30/0.66  % (3843)Memory used [KB]: 4349
% 2.30/0.66  % (3843)Time elapsed: 0.223 s
% 2.30/0.66  % (3843)------------------------------
% 2.30/0.66  % (3843)------------------------------
% 2.30/0.67  % (3841)Success in time 0.314 s
%------------------------------------------------------------------------------
