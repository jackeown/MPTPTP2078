%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:21 EST 2020

% Result     : Theorem 45.67s
% Output     : Refutation 45.67s
% Verified   : 
% Statistics : Number of formulae       :  188 (22549 expanded)
%              Number of leaves         :   16 (7924 expanded)
%              Depth                    :   41
%              Number of atoms          :  197 (22562 expanded)
%              Number of equality atoms :  182 (22543 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62943,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f56,f57,f418,f62834])).

fof(f62834,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f62833])).

fof(f62833,plain,
    ( $false
    | spl2_3 ),
    inference(subsumption_resolution,[],[f417,f62832])).

fof(f62832,plain,(
    ! [X159,X160] : k5_xboole_0(X159,X160) = k4_xboole_0(k5_xboole_0(X159,k4_xboole_0(X160,X159)),k5_xboole_0(X159,k4_xboole_0(X159,X160))) ),
    inference(forward_demodulation,[],[f62550,f62727])).

fof(f62727,plain,(
    ! [X52,X53] : k5_xboole_0(X52,k4_xboole_0(X52,X53)) = k4_xboole_0(X52,k5_xboole_0(X52,X53)) ),
    inference(forward_demodulation,[],[f62726,f1453])).

fof(f1453,plain,(
    ! [X30,X31,X32] : k5_xboole_0(X30,k5_xboole_0(X32,k5_xboole_0(X31,k4_xboole_0(X31,X30)))) = k5_xboole_0(X32,k4_xboole_0(X30,X31)) ),
    inference(superposition,[],[f511,f385])).

fof(f385,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f88,f372])).

fof(f372,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f294,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f294,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f292,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f292,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f268])).

fof(f268,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f226,f241])).

fof(f241,plain,(
    ! [X10] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10) ),
    inference(superposition,[],[f212,f111])).

fof(f111,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f107,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f107,plain,(
    ! [X2] : k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f29,f86])).

fof(f86,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f32,f76])).

fof(f76,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f29,f42])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f24,f24])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f212,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    inference(superposition,[],[f41,f29])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f33,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f24,f24])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f22,f23,f24])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f226,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f108,f212])).

fof(f108,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,X5))) ),
    inference(superposition,[],[f29,f86])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f29,f32])).

fof(f511,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X5)) = k5_xboole_0(X3,k5_xboole_0(X4,X5)) ),
    inference(superposition,[],[f60,f28])).

fof(f60,plain,(
    ! [X4,X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f28,f21])).

fof(f62726,plain,(
    ! [X52,X53] : k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(X52,k5_xboole_0(X53,k4_xboole_0(X53,X52)))) ),
    inference(forward_demodulation,[],[f62508,f28])).

fof(f62508,plain,(
    ! [X52,X53] : k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X53,X52))) ),
    inference(superposition,[],[f385,f61789])).

fof(f61789,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f61571,f21])).

fof(f61571,plain,(
    ! [X45,X46] : k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X45,X46),X46) ),
    inference(forward_demodulation,[],[f61549,f941])).

fof(f941,plain,(
    ! [X30,X29] : k4_xboole_0(X29,X30) = k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29) ),
    inference(forward_demodulation,[],[f906,f42])).

fof(f906,plain,(
    ! [X30,X29] : k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X29,X30)) ),
    inference(superposition,[],[f587,f385])).

fof(f587,plain,(
    ! [X24,X25] : k5_xboole_0(X25,X24) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X24,X25)) ),
    inference(superposition,[],[f66,f42])).

fof(f66,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f28,f21])).

fof(f61549,plain,(
    ! [X45,X46] : k4_xboole_0(k5_xboole_0(X45,X46),X46) = k5_xboole_0(k5_xboole_0(X46,k4_xboole_0(X46,X45)),X45) ),
    inference(backward_demodulation,[],[f5210,f61547])).

fof(f61547,plain,(
    ! [X33,X32] : k5_xboole_0(X33,k4_xboole_0(X33,X32)) = k4_xboole_0(X33,k5_xboole_0(X32,X33)) ),
    inference(forward_demodulation,[],[f61157,f372])).

fof(f61157,plain,(
    ! [X33,X32] : k4_xboole_0(X33,k4_xboole_0(X33,X32)) = k4_xboole_0(X33,k5_xboole_0(X32,X33)) ),
    inference(superposition,[],[f49417,f55439])).

fof(f55439,plain,(
    ! [X74,X75] : k4_xboole_0(X75,X74) = k4_xboole_0(k5_xboole_0(X74,X75),k4_xboole_0(X74,X75)) ),
    inference(forward_demodulation,[],[f55435,f19])).

fof(f55435,plain,(
    ! [X74,X75] : k4_xboole_0(k5_xboole_0(X74,X75),k4_xboole_0(X74,X75)) = k5_xboole_0(k4_xboole_0(X75,X74),k1_xboole_0) ),
    inference(backward_demodulation,[],[f6320,f55218])).

fof(f55218,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,X0)) ),
    inference(superposition,[],[f4309,f4956])).

fof(f4956,plain,(
    ! [X41,X40] : k5_xboole_0(X41,X40) = k5_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(X41,X40)) ),
    inference(superposition,[],[f426,f4824])).

fof(f4824,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3 ),
    inference(forward_demodulation,[],[f4823,f111])).

fof(f4823,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ),
    inference(forward_demodulation,[],[f4822,f2127])).

fof(f2127,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)))) ),
    inference(forward_demodulation,[],[f2126,f66])).

fof(f2126,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k5_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X9,k4_xboole_0(X9,X8)))) ),
    inference(forward_demodulation,[],[f2091,f372])).

fof(f2091,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X8,k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8)))) ),
    inference(superposition,[],[f2069,f32])).

fof(f2069,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) ),
    inference(forward_demodulation,[],[f2068,f268])).

fof(f2068,plain,(
    ! [X8,X9] : k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f926,f2067])).

fof(f2067,plain,(
    ! [X19,X20,X18] : k5_xboole_0(k4_xboole_0(X19,X18),X20) = k5_xboole_0(X18,k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X18,X19),X20))) ),
    inference(forward_demodulation,[],[f2016,f28])).

fof(f2016,plain,(
    ! [X19,X20,X18] : k5_xboole_0(k4_xboole_0(X19,X18),X20) = k5_xboole_0(X18,k5_xboole_0(k5_xboole_0(X19,k4_xboole_0(X18,X19)),X20)) ),
    inference(superposition,[],[f28,f933])).

fof(f933,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f892,f21])).

fof(f892,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X3),X3)) ),
    inference(superposition,[],[f385,f66])).

fof(f926,plain,(
    ! [X8,X9] : k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(X9,k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9)))) ),
    inference(forward_demodulation,[],[f925,f66])).

fof(f925,plain,(
    ! [X8,X9] : k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X8,k4_xboole_0(X9,X8)))) ),
    inference(forward_demodulation,[],[f886,f21])).

fof(f886,plain,(
    ! [X8,X9] : k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f385,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f4822,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))))) ),
    inference(forward_demodulation,[],[f4579,f111])).

fof(f4579,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),k1_xboole_0) ),
    inference(superposition,[],[f32,f917])).

fof(f917,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))),X4) ),
    inference(backward_demodulation,[],[f404,f916])).

fof(f916,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f915,f268])).

fof(f915,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f914,f385])).

fof(f914,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f881,f372])).

fof(f881,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f385,f32])).

fof(f404,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))),X4) ),
    inference(forward_demodulation,[],[f387,f66])).

fof(f387,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X5,k4_xboole_0(X5,X4))),X4) ),
    inference(backward_demodulation,[],[f177,f372])).

fof(f177,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))),X4) ),
    inference(superposition,[],[f34,f32])).

fof(f426,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f370,f370])).

fof(f370,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f294,f21])).

fof(f4309,plain,(
    ! [X74,X75,X73] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X73,X74),k5_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(X73,X74))) ),
    inference(superposition,[],[f1049,f1262])).

fof(f1262,plain,(
    ! [X17,X15,X16] : k4_xboole_0(X16,X15) = k4_xboole_0(k4_xboole_0(X16,X15),k4_xboole_0(X15,X17)) ),
    inference(superposition,[],[f1242,f212])).

fof(f1242,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X24,k4_xboole_0(k4_xboole_0(X23,X24),X25)) = X24 ),
    inference(forward_demodulation,[],[f1198,f19])).

fof(f1198,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X24,k5_xboole_0(k4_xboole_0(k4_xboole_0(X23,X24),X25),k1_xboole_0)) = X24 ),
    inference(superposition,[],[f398,f916])).

fof(f398,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X4,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))) = X4 ),
    inference(backward_demodulation,[],[f312,f372])).

fof(f312,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X4,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))) = X4 ),
    inference(superposition,[],[f212,f35])).

fof(f1049,plain,(
    ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X14,k4_xboole_0(X15,X14))) ),
    inference(superposition,[],[f916,f284])).

fof(f284,plain,(
    ! [X4,X3] : k4_xboole_0(X4,X3) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X3) ),
    inference(forward_demodulation,[],[f283,f240])).

fof(f240,plain,(
    ! [X8,X9] : k4_xboole_0(X9,X8) = k4_xboole_0(k4_xboole_0(X9,X8),X8) ),
    inference(superposition,[],[f212,f212])).

fof(f283,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X4,X3),X3) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X3) ),
    inference(forward_demodulation,[],[f249,f21])).

fof(f249,plain,(
    ! [X4,X3] : k4_xboole_0(k4_xboole_0(X4,X3),X3) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X3),X3),X3) ),
    inference(superposition,[],[f34,f212])).

fof(f6320,plain,(
    ! [X74,X75] : k4_xboole_0(k5_xboole_0(X74,X75),k4_xboole_0(X74,X75)) = k5_xboole_0(k4_xboole_0(X75,X74),k4_xboole_0(k4_xboole_0(X74,X75),k5_xboole_0(X74,X75))) ),
    inference(superposition,[],[f5229,f2673])).

fof(f2673,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X7) = k5_xboole_0(k4_xboole_0(X7,X8),k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f941,f60])).

fof(f5229,plain,(
    ! [X14,X15] : k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X14,X15),k4_xboole_0(X14,X15)) ),
    inference(superposition,[],[f2672,f727])).

fof(f727,plain,(
    ! [X23,X21,X22] : k5_xboole_0(k5_xboole_0(X21,X22),X23) = k5_xboole_0(X23,k5_xboole_0(X22,X21)) ),
    inference(forward_demodulation,[],[f708,f19])).

fof(f708,plain,(
    ! [X23,X21,X22] : k5_xboole_0(X23,k5_xboole_0(X22,X21)) = k5_xboole_0(k5_xboole_0(X21,X22),k5_xboole_0(X23,k1_xboole_0)) ),
    inference(superposition,[],[f66,f587])).

fof(f2672,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5)) ),
    inference(superposition,[],[f941,f572])).

fof(f572,plain,(
    ! [X14,X12,X13] : k5_xboole_0(X14,k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X13,X14),X12) ),
    inference(superposition,[],[f66,f21])).

fof(f49417,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X115,X114) = k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))) ),
    inference(forward_demodulation,[],[f49416,f41125])).

fof(f41125,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X114,X115) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),X115),k1_xboole_0) ),
    inference(forward_demodulation,[],[f41124,f294])).

fof(f41124,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X114,X115) = k5_xboole_0(k5_xboole_0(X114,k5_xboole_0(X114,k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),X115))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f41123,f19144])).

fof(f19144,plain,(
    ! [X39,X41,X40] : k4_xboole_0(X39,k4_xboole_0(k4_xboole_0(X39,X40),X41)) = k5_xboole_0(X39,k4_xboole_0(k4_xboole_0(X39,X40),X41)) ),
    inference(forward_demodulation,[],[f19056,f19])).

fof(f19056,plain,(
    ! [X39,X41,X40] : k4_xboole_0(X39,k4_xboole_0(k4_xboole_0(X39,X40),X41)) = k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(k4_xboole_0(X39,X40),X41),k1_xboole_0)) ),
    inference(superposition,[],[f385,f18859])).

fof(f18859,plain,(
    ! [X64,X62,X63] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X62,X63),X64),X62) ),
    inference(forward_demodulation,[],[f18715,f19])).

fof(f18715,plain,(
    ! [X64,X62,X63] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X62,X63),X64),k1_xboole_0),X62) ),
    inference(superposition,[],[f18258,f916])).

fof(f18258,plain,(
    ! [X57,X56,X55] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X55,X56))),X55) ),
    inference(forward_demodulation,[],[f17970,f262])).

fof(f262,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f112,f241])).

fof(f112,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f86,f111])).

fof(f17970,plain,(
    ! [X57,X56,X55] : k4_xboole_0(k5_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X55,X56))),X55) = k4_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X55,X56)) ),
    inference(superposition,[],[f390,f4292])).

fof(f4292,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X21,X22) = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,X21)) ),
    inference(superposition,[],[f212,f1262])).

fof(f390,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(backward_demodulation,[],[f302,f372])).

fof(f302,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f35,f32])).

fof(f41123,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X114,X115) = k5_xboole_0(k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),X115))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f41122,f402])).

fof(f402,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f383,f372])).

fof(f383,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(backward_demodulation,[],[f35,f372])).

fof(f41122,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X114,X115) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(X115,X116)))),X115),k1_xboole_0) ),
    inference(forward_demodulation,[],[f40924,f4203])).

fof(f4203,plain,(
    ! [X14,X15,X16] : k5_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))) = k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),X16) ),
    inference(forward_demodulation,[],[f4093,f372])).

fof(f4093,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X16) = k5_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))) ),
    inference(superposition,[],[f402,f1020])).

fof(f1020,plain,(
    ! [X2,X1] : k4_xboole_0(X2,k4_xboole_0(X2,X1)) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f1016,f1019])).

fof(f1019,plain,(
    ! [X12,X11] : k4_xboole_0(X12,X11) = k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f1018,f385])).

fof(f1018,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f998,f19])).

fof(f998,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X12)),k1_xboole_0)) ),
    inference(superposition,[],[f385,f970])).

fof(f970,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(forward_demodulation,[],[f951,f372])).

fof(f951,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f916,f32])).

fof(f1016,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f993,f111])).

fof(f993,plain,(
    ! [X2,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[],[f32,f970])).

fof(f40924,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X114,X115) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),k4_xboole_0(X114,X115))),k1_xboole_0) ),
    inference(superposition,[],[f903,f40462])).

fof(f40462,plain,(
    ! [X45,X46,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,k4_xboole_0(X45,X46))) ),
    inference(forward_demodulation,[],[f40461,f294])).

fof(f40461,plain,(
    ! [X45,X46,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(X44,k5_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46))))) ),
    inference(forward_demodulation,[],[f40460,f402])).

fof(f40460,plain,(
    ! [X45,X46,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(X44,k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X44,X45)),X46))) ),
    inference(forward_demodulation,[],[f40232,f11478])).

fof(f11478,plain,(
    ! [X105,X106,X104] : k5_xboole_0(X106,k5_xboole_0(X104,k4_xboole_0(X104,k5_xboole_0(X105,X106)))) = k5_xboole_0(X105,k4_xboole_0(k5_xboole_0(X105,X106),X104)) ),
    inference(superposition,[],[f650,f941])).

fof(f650,plain,(
    ! [X12,X13,X11] : k5_xboole_0(X13,X12) = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,X13))) ),
    inference(forward_demodulation,[],[f583,f28])).

fof(f583,plain,(
    ! [X12,X13,X11] : k5_xboole_0(X13,X12) = k5_xboole_0(X11,k5_xboole_0(k5_xboole_0(X12,X11),X13)) ),
    inference(superposition,[],[f66,f370])).

fof(f40232,plain,(
    ! [X45,X46,X44] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(X46,k4_xboole_0(X46,k5_xboole_0(X44,k4_xboole_0(X44,X45)))))) ),
    inference(superposition,[],[f1356,f372])).

fof(f1356,plain,(
    ! [X39,X37,X38] : k1_xboole_0 = k4_xboole_0(X39,k5_xboole_0(X39,k5_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X39))))) ),
    inference(superposition,[],[f1064,f402])).

fof(f1064,plain,(
    ! [X6,X7] : k1_xboole_0 = k4_xboole_0(X6,k5_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    inference(forward_demodulation,[],[f1045,f262])).

fof(f1045,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k5_xboole_0(X6,k4_xboole_0(X7,X6))) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k5_xboole_0(X6,k4_xboole_0(X7,X6))) ),
    inference(superposition,[],[f34,f284])).

fof(f903,plain,(
    ! [X24,X23] : k5_xboole_0(k5_xboole_0(X24,k4_xboole_0(X24,X23)),k4_xboole_0(X23,X24)) = X23 ),
    inference(superposition,[],[f370,f385])).

fof(f49416,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))),X114),k1_xboole_0) ),
    inference(forward_demodulation,[],[f49221,f268])).

fof(f49221,plain,(
    ! [X116,X114,X115] : k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))),X114),k5_xboole_0(X114,X114)) ),
    inference(superposition,[],[f904,f48788])).

fof(f48788,plain,(
    ! [X10,X8,X9] : k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X10,X8)))) = X9 ),
    inference(superposition,[],[f48463,f4292])).

fof(f48463,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X22,X24)),X24)) = X22 ),
    inference(forward_demodulation,[],[f48202,f111])).

fof(f48202,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X22,k1_xboole_0) = k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X22,X24)),X24)) ),
    inference(superposition,[],[f395,f35673])).

fof(f35673,plain,(
    ! [X12,X10,X11] : k1_xboole_0 = k5_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X10,X12)),X12))) ),
    inference(superposition,[],[f18261,f402])).

fof(f18261,plain,(
    ! [X61,X62,X63] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X62,k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X62,X63)))),X63) ),
    inference(forward_demodulation,[],[f17972,f262])).

fof(f17972,plain,(
    ! [X61,X62,X63] : k4_xboole_0(k5_xboole_0(X62,k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X62,X63)))),X63) = k4_xboole_0(k4_xboole_0(X61,k4_xboole_0(X62,X63)),k4_xboole_0(X61,k4_xboole_0(X62,X63))) ),
    inference(superposition,[],[f390,f240])).

fof(f395,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k4_xboole_0(X14,k5_xboole_0(X14,k4_xboole_0(X14,X15))) ),
    inference(backward_demodulation,[],[f327,f372])).

fof(f327,plain,(
    ! [X14,X15] : k4_xboole_0(X14,X15) = k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f300,f111])).

fof(f300,plain,(
    ! [X14,X15] : k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(k4_xboole_0(X14,k1_xboole_0),X15) ),
    inference(superposition,[],[f35,f262])).

fof(f904,plain,(
    ! [X26,X25] : k5_xboole_0(k4_xboole_0(X25,X26),k5_xboole_0(X26,k4_xboole_0(X26,X25))) = X25 ),
    inference(superposition,[],[f425,f385])).

fof(f425,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f370,f294])).

fof(f5210,plain,(
    ! [X45,X46] : k4_xboole_0(k5_xboole_0(X45,X46),X46) = k5_xboole_0(k4_xboole_0(X46,k5_xboole_0(X45,X46)),X45) ),
    inference(superposition,[],[f2672,f425])).

fof(f62550,plain,(
    ! [X159,X160] : k5_xboole_0(X159,X160) = k4_xboole_0(k5_xboole_0(X159,k4_xboole_0(X160,X159)),k4_xboole_0(X159,k5_xboole_0(X159,X160))) ),
    inference(superposition,[],[f2073,f61789])).

fof(f2073,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f2071,f111])).

fof(f2071,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f187,f2069])).

fof(f187,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f34])).

fof(f417,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl2_3
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f418,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f401,f37,f415])).

fof(f37,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f401,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(backward_demodulation,[],[f39,f372])).

fof(f39,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f57,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f51,f53])).

fof(f53,plain,
    ( spl2_2
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f51,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f42,f31])).

fof(f56,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f50,f53])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f31,f42])).

fof(f40,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f37])).

fof(f30,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f17,f23,f24])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:46:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (30187)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (30197)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (30197)Refutation not found, incomplete strategy% (30197)------------------------------
% 0.21/0.47  % (30197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (30197)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (30197)Memory used [KB]: 10490
% 0.21/0.47  % (30197)Time elapsed: 0.045 s
% 0.21/0.47  % (30197)------------------------------
% 0.21/0.47  % (30197)------------------------------
% 0.21/0.47  % (30191)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (30190)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (30201)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (30198)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (30203)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (30188)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (30193)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (30196)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (30194)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (30192)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (30186)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (30202)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (30195)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (30199)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (30200)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (30189)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 5.24/1.03  % (30190)Time limit reached!
% 5.24/1.03  % (30190)------------------------------
% 5.24/1.03  % (30190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.24/1.03  % (30190)Termination reason: Time limit
% 5.24/1.03  
% 5.24/1.03  % (30190)Memory used [KB]: 15095
% 5.24/1.03  % (30190)Time elapsed: 0.611 s
% 5.24/1.03  % (30190)------------------------------
% 5.24/1.03  % (30190)------------------------------
% 12.39/1.93  % (30191)Time limit reached!
% 12.39/1.93  % (30191)------------------------------
% 12.39/1.93  % (30191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.39/1.93  % (30191)Termination reason: Time limit
% 12.39/1.93  % (30191)Termination phase: Saturation
% 12.39/1.93  
% 12.39/1.93  % (30191)Memory used [KB]: 39786
% 12.39/1.93  % (30191)Time elapsed: 1.500 s
% 12.39/1.93  % (30191)------------------------------
% 12.39/1.93  % (30191)------------------------------
% 12.39/1.96  % (30192)Time limit reached!
% 12.39/1.96  % (30192)------------------------------
% 12.39/1.96  % (30192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.39/1.96  % (30192)Termination reason: Time limit
% 12.39/1.96  % (30192)Termination phase: Saturation
% 12.39/1.96  
% 12.39/1.96  % (30192)Memory used [KB]: 37099
% 12.39/1.96  % (30192)Time elapsed: 1.500 s
% 12.39/1.96  % (30192)------------------------------
% 12.39/1.96  % (30192)------------------------------
% 14.81/2.26  % (30188)Time limit reached!
% 14.81/2.26  % (30188)------------------------------
% 14.81/2.26  % (30188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.81/2.26  % (30188)Termination reason: Time limit
% 14.81/2.26  
% 14.81/2.26  % (30188)Memory used [KB]: 44135
% 14.81/2.26  % (30188)Time elapsed: 1.834 s
% 14.81/2.26  % (30188)------------------------------
% 14.81/2.26  % (30188)------------------------------
% 17.83/2.64  % (30198)Time limit reached!
% 17.83/2.64  % (30198)------------------------------
% 17.83/2.64  % (30198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.83/2.65  % (30198)Termination reason: Time limit
% 17.83/2.65  
% 17.83/2.65  % (30198)Memory used [KB]: 44263
% 17.83/2.65  % (30198)Time elapsed: 2.217 s
% 17.83/2.65  % (30198)------------------------------
% 17.83/2.65  % (30198)------------------------------
% 45.67/6.18  % (30196)Refutation found. Thanks to Tanya!
% 45.67/6.18  % SZS status Theorem for theBenchmark
% 45.67/6.18  % SZS output start Proof for theBenchmark
% 45.67/6.18  fof(f62943,plain,(
% 45.67/6.18    $false),
% 45.67/6.18    inference(avatar_sat_refutation,[],[f40,f56,f57,f418,f62834])).
% 45.67/6.18  fof(f62834,plain,(
% 45.67/6.18    spl2_3),
% 45.67/6.18    inference(avatar_contradiction_clause,[],[f62833])).
% 45.67/6.18  fof(f62833,plain,(
% 45.67/6.18    $false | spl2_3),
% 45.67/6.18    inference(subsumption_resolution,[],[f417,f62832])).
% 45.67/6.18  fof(f62832,plain,(
% 45.67/6.18    ( ! [X159,X160] : (k5_xboole_0(X159,X160) = k4_xboole_0(k5_xboole_0(X159,k4_xboole_0(X160,X159)),k5_xboole_0(X159,k4_xboole_0(X159,X160)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f62550,f62727])).
% 45.67/6.18  fof(f62727,plain,(
% 45.67/6.18    ( ! [X52,X53] : (k5_xboole_0(X52,k4_xboole_0(X52,X53)) = k4_xboole_0(X52,k5_xboole_0(X52,X53))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f62726,f1453])).
% 45.67/6.18  fof(f1453,plain,(
% 45.67/6.18    ( ! [X30,X31,X32] : (k5_xboole_0(X30,k5_xboole_0(X32,k5_xboole_0(X31,k4_xboole_0(X31,X30)))) = k5_xboole_0(X32,k4_xboole_0(X30,X31))) )),
% 45.67/6.18    inference(superposition,[],[f511,f385])).
% 45.67/6.18  fof(f385,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 45.67/6.18    inference(backward_demodulation,[],[f88,f372])).
% 45.67/6.18  fof(f372,plain,(
% 45.67/6.18    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X8)) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 45.67/6.18    inference(superposition,[],[f294,f29])).
% 45.67/6.18  fof(f29,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 45.67/6.18    inference(definition_unfolding,[],[f26,f24])).
% 45.67/6.18  fof(f24,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 45.67/6.18    inference(cnf_transformation,[],[f7])).
% 45.67/6.18  fof(f7,axiom,(
% 45.67/6.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 45.67/6.18  fof(f26,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 45.67/6.18    inference(cnf_transformation,[],[f3])).
% 45.67/6.18  fof(f3,axiom,(
% 45.67/6.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 45.67/6.18  fof(f294,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 45.67/6.18    inference(forward_demodulation,[],[f292,f42])).
% 45.67/6.18  fof(f42,plain,(
% 45.67/6.18    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 45.67/6.18    inference(superposition,[],[f21,f19])).
% 45.67/6.18  fof(f19,plain,(
% 45.67/6.18    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 45.67/6.18    inference(cnf_transformation,[],[f9])).
% 45.67/6.18  fof(f9,axiom,(
% 45.67/6.18    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 45.67/6.18  fof(f21,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 45.67/6.18    inference(cnf_transformation,[],[f2])).
% 45.67/6.18  fof(f2,axiom,(
% 45.67/6.18    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 45.67/6.18  fof(f292,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 45.67/6.18    inference(superposition,[],[f28,f268])).
% 45.67/6.18  fof(f268,plain,(
% 45.67/6.18    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f226,f241])).
% 45.67/6.18  fof(f241,plain,(
% 45.67/6.18    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)) )),
% 45.67/6.18    inference(superposition,[],[f212,f111])).
% 45.67/6.18  fof(f111,plain,(
% 45.67/6.18    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 45.67/6.18    inference(forward_demodulation,[],[f107,f31])).
% 45.67/6.18  fof(f31,plain,(
% 45.67/6.18    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 45.67/6.18    inference(definition_unfolding,[],[f18,f23])).
% 45.67/6.18  fof(f23,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 45.67/6.18    inference(cnf_transformation,[],[f11])).
% 45.67/6.18  fof(f11,axiom,(
% 45.67/6.18    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 45.67/6.18  fof(f18,plain,(
% 45.67/6.18    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 45.67/6.18    inference(cnf_transformation,[],[f4])).
% 45.67/6.18  fof(f4,axiom,(
% 45.67/6.18    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 45.67/6.18  fof(f107,plain,(
% 45.67/6.18    ( ! [X2] : (k5_xboole_0(X2,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,k1_xboole_0)) )),
% 45.67/6.18    inference(superposition,[],[f29,f86])).
% 45.67/6.18  fof(f86,plain,(
% 45.67/6.18    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 45.67/6.18    inference(superposition,[],[f32,f76])).
% 45.67/6.18  fof(f76,plain,(
% 45.67/6.18    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 45.67/6.18    inference(superposition,[],[f29,f42])).
% 45.67/6.18  fof(f32,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 45.67/6.18    inference(definition_unfolding,[],[f20,f24,f24])).
% 45.67/6.18  fof(f20,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 45.67/6.18    inference(cnf_transformation,[],[f1])).
% 45.67/6.18  fof(f1,axiom,(
% 45.67/6.18    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 45.67/6.18  fof(f212,plain,(
% 45.67/6.18    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) )),
% 45.67/6.18    inference(superposition,[],[f41,f29])).
% 45.67/6.18  fof(f41,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 45.67/6.18    inference(backward_demodulation,[],[f33,f35])).
% 45.67/6.18  fof(f35,plain,(
% 45.67/6.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 45.67/6.18    inference(definition_unfolding,[],[f27,f24,f24])).
% 45.67/6.18  fof(f27,plain,(
% 45.67/6.18    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 45.67/6.18    inference(cnf_transformation,[],[f8])).
% 45.67/6.18  fof(f8,axiom,(
% 45.67/6.18    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 45.67/6.18  fof(f33,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 45.67/6.18    inference(definition_unfolding,[],[f22,f23,f24])).
% 45.67/6.18  fof(f22,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 45.67/6.18    inference(cnf_transformation,[],[f5])).
% 45.67/6.18  fof(f5,axiom,(
% 45.67/6.18    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 45.67/6.18  fof(f226,plain,(
% 45.67/6.18    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,X5)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f108,f212])).
% 45.67/6.18  fof(f108,plain,(
% 45.67/6.18    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k5_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(k1_xboole_0,X5)))) )),
% 45.67/6.18    inference(superposition,[],[f29,f86])).
% 45.67/6.18  fof(f28,plain,(
% 45.67/6.18    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 45.67/6.18    inference(cnf_transformation,[],[f10])).
% 45.67/6.18  fof(f10,axiom,(
% 45.67/6.18    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 45.67/6.18  fof(f88,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 45.67/6.18    inference(superposition,[],[f29,f32])).
% 45.67/6.18  fof(f511,plain,(
% 45.67/6.18    ( ! [X4,X5,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X5)) = k5_xboole_0(X3,k5_xboole_0(X4,X5))) )),
% 45.67/6.18    inference(superposition,[],[f60,f28])).
% 45.67/6.18  fof(f60,plain,(
% 45.67/6.18    ( ! [X4,X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,X4)) = k5_xboole_0(k5_xboole_0(X3,X2),X4)) )),
% 45.67/6.18    inference(superposition,[],[f28,f21])).
% 45.67/6.18  fof(f62726,plain,(
% 45.67/6.18    ( ! [X52,X53] : (k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(X52,k5_xboole_0(X53,k4_xboole_0(X53,X52))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f62508,f28])).
% 45.67/6.18  fof(f62508,plain,(
% 45.67/6.18    ( ! [X52,X53] : (k4_xboole_0(X52,k5_xboole_0(X52,X53)) = k5_xboole_0(X52,k5_xboole_0(k5_xboole_0(X52,X53),k4_xboole_0(X53,X52)))) )),
% 45.67/6.18    inference(superposition,[],[f385,f61789])).
% 45.67/6.18  fof(f61789,plain,(
% 45.67/6.18    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k5_xboole_0(X2,X1),X2)) )),
% 45.67/6.18    inference(superposition,[],[f61571,f21])).
% 45.67/6.18  fof(f61571,plain,(
% 45.67/6.18    ( ! [X45,X46] : (k4_xboole_0(X45,X46) = k4_xboole_0(k5_xboole_0(X45,X46),X46)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f61549,f941])).
% 45.67/6.18  fof(f941,plain,(
% 45.67/6.18    ( ! [X30,X29] : (k4_xboole_0(X29,X30) = k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f906,f42])).
% 45.67/6.18  fof(f906,plain,(
% 45.67/6.18    ( ! [X30,X29] : (k5_xboole_0(k5_xboole_0(X30,k4_xboole_0(X30,X29)),X29) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X29,X30))) )),
% 45.67/6.18    inference(superposition,[],[f587,f385])).
% 45.67/6.18  fof(f587,plain,(
% 45.67/6.18    ( ! [X24,X25] : (k5_xboole_0(X25,X24) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X24,X25))) )),
% 45.67/6.18    inference(superposition,[],[f66,f42])).
% 45.67/6.18  fof(f66,plain,(
% 45.67/6.18    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 45.67/6.18    inference(superposition,[],[f28,f21])).
% 45.67/6.18  fof(f61549,plain,(
% 45.67/6.18    ( ! [X45,X46] : (k4_xboole_0(k5_xboole_0(X45,X46),X46) = k5_xboole_0(k5_xboole_0(X46,k4_xboole_0(X46,X45)),X45)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f5210,f61547])).
% 45.67/6.18  fof(f61547,plain,(
% 45.67/6.18    ( ! [X33,X32] : (k5_xboole_0(X33,k4_xboole_0(X33,X32)) = k4_xboole_0(X33,k5_xboole_0(X32,X33))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f61157,f372])).
% 45.67/6.18  fof(f61157,plain,(
% 45.67/6.18    ( ! [X33,X32] : (k4_xboole_0(X33,k4_xboole_0(X33,X32)) = k4_xboole_0(X33,k5_xboole_0(X32,X33))) )),
% 45.67/6.18    inference(superposition,[],[f49417,f55439])).
% 45.67/6.18  fof(f55439,plain,(
% 45.67/6.18    ( ! [X74,X75] : (k4_xboole_0(X75,X74) = k4_xboole_0(k5_xboole_0(X74,X75),k4_xboole_0(X74,X75))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f55435,f19])).
% 45.67/6.18  fof(f55435,plain,(
% 45.67/6.18    ( ! [X74,X75] : (k4_xboole_0(k5_xboole_0(X74,X75),k4_xboole_0(X74,X75)) = k5_xboole_0(k4_xboole_0(X75,X74),k1_xboole_0)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f6320,f55218])).
% 45.67/6.18  fof(f55218,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X0),k5_xboole_0(X1,X0))) )),
% 45.67/6.18    inference(superposition,[],[f4309,f4956])).
% 45.67/6.18  fof(f4956,plain,(
% 45.67/6.18    ( ! [X41,X40] : (k5_xboole_0(X41,X40) = k5_xboole_0(k4_xboole_0(X40,X41),k4_xboole_0(X41,X40))) )),
% 45.67/6.18    inference(superposition,[],[f426,f4824])).
% 45.67/6.18  fof(f4824,plain,(
% 45.67/6.18    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = X3) )),
% 45.67/6.18    inference(forward_demodulation,[],[f4823,f111])).
% 45.67/6.18  fof(f4823,plain,(
% 45.67/6.18    ( ! [X2,X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f4822,f2127])).
% 45.67/6.18  fof(f2127,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f2126,f66])).
% 45.67/6.18  fof(f2126,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k5_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X9,k4_xboole_0(X9,X8))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f2091,f372])).
% 45.67/6.18  fof(f2091,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))))) )),
% 45.67/6.18    inference(superposition,[],[f2069,f32])).
% 45.67/6.18  fof(f2069,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f2068,f268])).
% 45.67/6.18  fof(f2068,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9))) )),
% 45.67/6.18    inference(backward_demodulation,[],[f926,f2067])).
% 45.67/6.18  fof(f2067,plain,(
% 45.67/6.18    ( ! [X19,X20,X18] : (k5_xboole_0(k4_xboole_0(X19,X18),X20) = k5_xboole_0(X18,k5_xboole_0(X19,k5_xboole_0(k4_xboole_0(X18,X19),X20)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f2016,f28])).
% 45.67/6.18  fof(f2016,plain,(
% 45.67/6.18    ( ! [X19,X20,X18] : (k5_xboole_0(k4_xboole_0(X19,X18),X20) = k5_xboole_0(X18,k5_xboole_0(k5_xboole_0(X19,k4_xboole_0(X18,X19)),X20))) )),
% 45.67/6.18    inference(superposition,[],[f28,f933])).
% 45.67/6.18  fof(f933,plain,(
% 45.67/6.18    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f892,f21])).
% 45.67/6.18  fof(f892,plain,(
% 45.67/6.18    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X4,k5_xboole_0(k4_xboole_0(X4,X3),X3))) )),
% 45.67/6.18    inference(superposition,[],[f385,f66])).
% 45.67/6.18  fof(f926,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(X9,k5_xboole_0(X8,k5_xboole_0(k4_xboole_0(X9,X8),k4_xboole_0(X8,X9))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f925,f66])).
% 45.67/6.18  fof(f925,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X8,X9),k5_xboole_0(X8,k4_xboole_0(X9,X8))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f886,f21])).
% 45.67/6.18  fof(f886,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k4_xboole_0(X9,k5_xboole_0(X8,k4_xboole_0(X9,X8))) = k5_xboole_0(X9,k5_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X8,X9)))) )),
% 45.67/6.18    inference(superposition,[],[f385,f34])).
% 45.67/6.18  fof(f34,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 45.67/6.18    inference(definition_unfolding,[],[f25,f23])).
% 45.67/6.18  fof(f25,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 45.67/6.18    inference(cnf_transformation,[],[f6])).
% 45.67/6.18  fof(f6,axiom,(
% 45.67/6.18    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 45.67/6.18  fof(f4822,plain,(
% 45.67/6.18    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))) = k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2)))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f4579,f111])).
% 45.67/6.18  fof(f4579,plain,(
% 45.67/6.18    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))))) = k4_xboole_0(k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X3,X2))),k1_xboole_0)) )),
% 45.67/6.18    inference(superposition,[],[f32,f917])).
% 45.67/6.18  fof(f917,plain,(
% 45.67/6.18    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))),X4)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f404,f916])).
% 45.67/6.18  fof(f916,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f915,f268])).
% 45.67/6.18  fof(f915,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f914,f385])).
% 45.67/6.18  fof(f914,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f881,f372])).
% 45.67/6.18  fof(f881,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 45.67/6.18    inference(superposition,[],[f385,f32])).
% 45.67/6.18  fof(f404,plain,(
% 45.67/6.18    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k5_xboole_0(X5,k5_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X4,X5))),X4)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f387,f66])).
% 45.67/6.18  fof(f387,plain,(
% 45.67/6.18    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X5),k5_xboole_0(X5,k4_xboole_0(X5,X4))),X4)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f177,f372])).
% 45.67/6.18  fof(f177,plain,(
% 45.67/6.18    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X5,k4_xboole_0(X5,X4))),X4)) )),
% 45.67/6.18    inference(superposition,[],[f34,f32])).
% 45.67/6.18  fof(f426,plain,(
% 45.67/6.18    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 45.67/6.18    inference(superposition,[],[f370,f370])).
% 45.67/6.18  fof(f370,plain,(
% 45.67/6.18    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 45.67/6.18    inference(superposition,[],[f294,f21])).
% 45.67/6.18  fof(f4309,plain,(
% 45.67/6.18    ( ! [X74,X75,X73] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X73,X74),k5_xboole_0(k4_xboole_0(X74,X75),k4_xboole_0(X73,X74)))) )),
% 45.67/6.18    inference(superposition,[],[f1049,f1262])).
% 45.67/6.18  fof(f1262,plain,(
% 45.67/6.18    ( ! [X17,X15,X16] : (k4_xboole_0(X16,X15) = k4_xboole_0(k4_xboole_0(X16,X15),k4_xboole_0(X15,X17))) )),
% 45.67/6.18    inference(superposition,[],[f1242,f212])).
% 45.67/6.18  fof(f1242,plain,(
% 45.67/6.18    ( ! [X24,X23,X25] : (k4_xboole_0(X24,k4_xboole_0(k4_xboole_0(X23,X24),X25)) = X24) )),
% 45.67/6.18    inference(forward_demodulation,[],[f1198,f19])).
% 45.67/6.18  fof(f1198,plain,(
% 45.67/6.18    ( ! [X24,X23,X25] : (k4_xboole_0(X24,k5_xboole_0(k4_xboole_0(k4_xboole_0(X23,X24),X25),k1_xboole_0)) = X24) )),
% 45.67/6.18    inference(superposition,[],[f398,f916])).
% 45.67/6.18  fof(f398,plain,(
% 45.67/6.18    ( ! [X4,X2,X3] : (k4_xboole_0(X4,k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))) = X4) )),
% 45.67/6.18    inference(backward_demodulation,[],[f312,f372])).
% 45.67/6.18  fof(f312,plain,(
% 45.67/6.18    ( ! [X4,X2,X3] : (k4_xboole_0(X4,k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,X4)))) = X4) )),
% 45.67/6.18    inference(superposition,[],[f212,f35])).
% 45.67/6.18  fof(f1049,plain,(
% 45.67/6.18    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X15,X14),k5_xboole_0(X14,k4_xboole_0(X15,X14)))) )),
% 45.67/6.18    inference(superposition,[],[f916,f284])).
% 45.67/6.18  fof(f284,plain,(
% 45.67/6.18    ( ! [X4,X3] : (k4_xboole_0(X4,X3) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X3)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f283,f240])).
% 45.67/6.18  fof(f240,plain,(
% 45.67/6.18    ( ! [X8,X9] : (k4_xboole_0(X9,X8) = k4_xboole_0(k4_xboole_0(X9,X8),X8)) )),
% 45.67/6.18    inference(superposition,[],[f212,f212])).
% 45.67/6.18  fof(f283,plain,(
% 45.67/6.18    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X4,X3),X3) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),X3)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f249,f21])).
% 45.67/6.18  fof(f249,plain,(
% 45.67/6.18    ( ! [X4,X3] : (k4_xboole_0(k4_xboole_0(X4,X3),X3) = k4_xboole_0(k5_xboole_0(k4_xboole_0(X4,X3),X3),X3)) )),
% 45.67/6.18    inference(superposition,[],[f34,f212])).
% 45.67/6.18  fof(f6320,plain,(
% 45.67/6.18    ( ! [X74,X75] : (k4_xboole_0(k5_xboole_0(X74,X75),k4_xboole_0(X74,X75)) = k5_xboole_0(k4_xboole_0(X75,X74),k4_xboole_0(k4_xboole_0(X74,X75),k5_xboole_0(X74,X75)))) )),
% 45.67/6.18    inference(superposition,[],[f5229,f2673])).
% 45.67/6.18  fof(f2673,plain,(
% 45.67/6.18    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k5_xboole_0(k4_xboole_0(X7,X8),k5_xboole_0(X7,X8))) )),
% 45.67/6.18    inference(superposition,[],[f941,f60])).
% 45.67/6.18  fof(f5229,plain,(
% 45.67/6.18    ( ! [X14,X15] : (k4_xboole_0(X15,X14) = k5_xboole_0(k5_xboole_0(X14,X15),k4_xboole_0(X14,X15))) )),
% 45.67/6.18    inference(superposition,[],[f2672,f727])).
% 45.67/6.18  fof(f727,plain,(
% 45.67/6.18    ( ! [X23,X21,X22] : (k5_xboole_0(k5_xboole_0(X21,X22),X23) = k5_xboole_0(X23,k5_xboole_0(X22,X21))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f708,f19])).
% 45.67/6.18  fof(f708,plain,(
% 45.67/6.18    ( ! [X23,X21,X22] : (k5_xboole_0(X23,k5_xboole_0(X22,X21)) = k5_xboole_0(k5_xboole_0(X21,X22),k5_xboole_0(X23,k1_xboole_0))) )),
% 45.67/6.18    inference(superposition,[],[f66,f587])).
% 45.67/6.18  fof(f2672,plain,(
% 45.67/6.18    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k4_xboole_0(X5,X6),k5_xboole_0(X6,X5))) )),
% 45.67/6.18    inference(superposition,[],[f941,f572])).
% 45.67/6.18  fof(f572,plain,(
% 45.67/6.18    ( ! [X14,X12,X13] : (k5_xboole_0(X14,k5_xboole_0(X12,X13)) = k5_xboole_0(k5_xboole_0(X13,X14),X12)) )),
% 45.67/6.18    inference(superposition,[],[f66,f21])).
% 45.67/6.18  fof(f49417,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X115,X114) = k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f49416,f41125])).
% 45.67/6.18  fof(f41125,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X114,X115) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),X115),k1_xboole_0)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f41124,f294])).
% 45.67/6.18  fof(f41124,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X114,X115) = k5_xboole_0(k5_xboole_0(X114,k5_xboole_0(X114,k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),X115))),k1_xboole_0)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f41123,f19144])).
% 45.67/6.18  fof(f19144,plain,(
% 45.67/6.18    ( ! [X39,X41,X40] : (k4_xboole_0(X39,k4_xboole_0(k4_xboole_0(X39,X40),X41)) = k5_xboole_0(X39,k4_xboole_0(k4_xboole_0(X39,X40),X41))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f19056,f19])).
% 45.67/6.18  fof(f19056,plain,(
% 45.67/6.18    ( ! [X39,X41,X40] : (k4_xboole_0(X39,k4_xboole_0(k4_xboole_0(X39,X40),X41)) = k5_xboole_0(X39,k5_xboole_0(k4_xboole_0(k4_xboole_0(X39,X40),X41),k1_xboole_0))) )),
% 45.67/6.18    inference(superposition,[],[f385,f18859])).
% 45.67/6.18  fof(f18859,plain,(
% 45.67/6.18    ( ! [X64,X62,X63] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X62,X63),X64),X62)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f18715,f19])).
% 45.67/6.18  fof(f18715,plain,(
% 45.67/6.18    ( ! [X64,X62,X63] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k4_xboole_0(k4_xboole_0(X62,X63),X64),k1_xboole_0),X62)) )),
% 45.67/6.18    inference(superposition,[],[f18258,f916])).
% 45.67/6.18  fof(f18258,plain,(
% 45.67/6.18    ( ! [X57,X56,X55] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X55,X56))),X55)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f17970,f262])).
% 45.67/6.18  fof(f262,plain,(
% 45.67/6.18    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f112,f241])).
% 45.67/6.18  fof(f112,plain,(
% 45.67/6.18    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f86,f111])).
% 45.67/6.18  fof(f17970,plain,(
% 45.67/6.18    ( ! [X57,X56,X55] : (k4_xboole_0(k5_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X55,X56))),X55) = k4_xboole_0(k4_xboole_0(X55,X56),k4_xboole_0(X55,X56))) )),
% 45.67/6.18    inference(superposition,[],[f390,f4292])).
% 45.67/6.18  fof(f4292,plain,(
% 45.67/6.18    ( ! [X21,X22,X20] : (k4_xboole_0(X21,X22) = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X20,X21))) )),
% 45.67/6.18    inference(superposition,[],[f212,f1262])).
% 45.67/6.18  fof(f390,plain,(
% 45.67/6.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f302,f372])).
% 45.67/6.18  fof(f302,plain,(
% 45.67/6.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 45.67/6.18    inference(superposition,[],[f35,f32])).
% 45.67/6.18  fof(f41123,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X114,X115) = k5_xboole_0(k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),X115))),k1_xboole_0)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f41122,f402])).
% 45.67/6.18  fof(f402,plain,(
% 45.67/6.18    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f383,f372])).
% 45.67/6.18  fof(f383,plain,(
% 45.67/6.18    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 45.67/6.18    inference(backward_demodulation,[],[f35,f372])).
% 45.67/6.18  fof(f41122,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X114,X115) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(X114,k4_xboole_0(X115,X116)))),X115),k1_xboole_0)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f40924,f4203])).
% 45.67/6.18  fof(f4203,plain,(
% 45.67/6.18    ( ! [X14,X15,X16] : (k5_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))) = k4_xboole_0(k5_xboole_0(X15,k4_xboole_0(X15,X14)),X16)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f4093,f372])).
% 45.67/6.18  fof(f4093,plain,(
% 45.67/6.18    ( ! [X14,X15,X16] : (k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X16) = k5_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))) )),
% 45.67/6.18    inference(superposition,[],[f402,f1020])).
% 45.67/6.18  fof(f1020,plain,(
% 45.67/6.18    ( ! [X2,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,X1)) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 45.67/6.18    inference(backward_demodulation,[],[f1016,f1019])).
% 45.67/6.18  fof(f1019,plain,(
% 45.67/6.18    ( ! [X12,X11] : (k4_xboole_0(X12,X11) = k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f1018,f385])).
% 45.67/6.18  fof(f1018,plain,(
% 45.67/6.18    ( ! [X12,X11] : (k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f998,f19])).
% 45.67/6.18  fof(f998,plain,(
% 45.67/6.18    ( ! [X12,X11] : (k4_xboole_0(X12,k5_xboole_0(X11,k4_xboole_0(X11,X12))) = k5_xboole_0(X12,k5_xboole_0(k5_xboole_0(X11,k4_xboole_0(X11,X12)),k1_xboole_0))) )),
% 45.67/6.18    inference(superposition,[],[f385,f970])).
% 45.67/6.18  fof(f970,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f951,f372])).
% 45.67/6.18  fof(f951,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 45.67/6.18    inference(superposition,[],[f916,f32])).
% 45.67/6.18  fof(f1016,plain,(
% 45.67/6.18    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f993,f111])).
% 45.67/6.18  fof(f993,plain,(
% 45.67/6.18    ( ! [X2,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X2)),k1_xboole_0)) )),
% 45.67/6.18    inference(superposition,[],[f32,f970])).
% 45.67/6.18  fof(f40924,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X114,X115) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),k4_xboole_0(k4_xboole_0(X114,k4_xboole_0(X115,X116)),k4_xboole_0(X114,X115))),k1_xboole_0)) )),
% 45.67/6.18    inference(superposition,[],[f903,f40462])).
% 45.67/6.18  fof(f40462,plain,(
% 45.67/6.18    ( ! [X45,X46,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,k4_xboole_0(X45,X46)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f40461,f294])).
% 45.67/6.18  fof(f40461,plain,(
% 45.67/6.18    ( ! [X45,X46,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(X44,k5_xboole_0(X44,k4_xboole_0(X44,k4_xboole_0(X45,X46)))))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f40460,f402])).
% 45.67/6.18  fof(f40460,plain,(
% 45.67/6.18    ( ! [X45,X46,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(X44,k4_xboole_0(k5_xboole_0(X44,k4_xboole_0(X44,X45)),X46)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f40232,f11478])).
% 45.67/6.18  fof(f11478,plain,(
% 45.67/6.18    ( ! [X105,X106,X104] : (k5_xboole_0(X106,k5_xboole_0(X104,k4_xboole_0(X104,k5_xboole_0(X105,X106)))) = k5_xboole_0(X105,k4_xboole_0(k5_xboole_0(X105,X106),X104))) )),
% 45.67/6.18    inference(superposition,[],[f650,f941])).
% 45.67/6.18  fof(f650,plain,(
% 45.67/6.18    ( ! [X12,X13,X11] : (k5_xboole_0(X13,X12) = k5_xboole_0(X11,k5_xboole_0(X12,k5_xboole_0(X11,X13)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f583,f28])).
% 45.67/6.18  fof(f583,plain,(
% 45.67/6.18    ( ! [X12,X13,X11] : (k5_xboole_0(X13,X12) = k5_xboole_0(X11,k5_xboole_0(k5_xboole_0(X12,X11),X13))) )),
% 45.67/6.18    inference(superposition,[],[f66,f370])).
% 45.67/6.18  fof(f40232,plain,(
% 45.67/6.18    ( ! [X45,X46,X44] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(k4_xboole_0(X44,X45),k5_xboole_0(X46,k4_xboole_0(X46,k5_xboole_0(X44,k4_xboole_0(X44,X45))))))) )),
% 45.67/6.18    inference(superposition,[],[f1356,f372])).
% 45.67/6.18  fof(f1356,plain,(
% 45.67/6.18    ( ! [X39,X37,X38] : (k1_xboole_0 = k4_xboole_0(X39,k5_xboole_0(X39,k5_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X39)))))) )),
% 45.67/6.18    inference(superposition,[],[f1064,f402])).
% 45.67/6.18  fof(f1064,plain,(
% 45.67/6.18    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(X6,k5_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f1045,f262])).
% 45.67/6.18  fof(f1045,plain,(
% 45.67/6.18    ( ! [X6,X7] : (k4_xboole_0(X6,k5_xboole_0(X6,k4_xboole_0(X7,X6))) = k4_xboole_0(k5_xboole_0(X6,k4_xboole_0(X7,X6)),k5_xboole_0(X6,k4_xboole_0(X7,X6)))) )),
% 45.67/6.18    inference(superposition,[],[f34,f284])).
% 45.67/6.18  fof(f903,plain,(
% 45.67/6.18    ( ! [X24,X23] : (k5_xboole_0(k5_xboole_0(X24,k4_xboole_0(X24,X23)),k4_xboole_0(X23,X24)) = X23) )),
% 45.67/6.18    inference(superposition,[],[f370,f385])).
% 45.67/6.18  fof(f49416,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))),X114),k1_xboole_0)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f49221,f268])).
% 45.67/6.18  fof(f49221,plain,(
% 45.67/6.18    ( ! [X116,X114,X115] : (k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X115,k4_xboole_0(X114,k4_xboole_0(X116,X115))),X114),k5_xboole_0(X114,X114))) )),
% 45.67/6.18    inference(superposition,[],[f904,f48788])).
% 45.67/6.18  fof(f48788,plain,(
% 45.67/6.18    ( ! [X10,X8,X9] : (k4_xboole_0(X9,k4_xboole_0(X8,k4_xboole_0(X9,k4_xboole_0(X10,X8)))) = X9) )),
% 45.67/6.18    inference(superposition,[],[f48463,f4292])).
% 45.67/6.18  fof(f48463,plain,(
% 45.67/6.18    ( ! [X24,X23,X22] : (k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X22,X24)),X24)) = X22) )),
% 45.67/6.18    inference(forward_demodulation,[],[f48202,f111])).
% 45.67/6.18  fof(f48202,plain,(
% 45.67/6.18    ( ! [X24,X23,X22] : (k4_xboole_0(X22,k1_xboole_0) = k4_xboole_0(X22,k4_xboole_0(k4_xboole_0(X23,k4_xboole_0(X22,X24)),X24))) )),
% 45.67/6.18    inference(superposition,[],[f395,f35673])).
% 45.67/6.18  fof(f35673,plain,(
% 45.67/6.18    ( ! [X12,X10,X11] : (k1_xboole_0 = k5_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X10,X12)),X12)))) )),
% 45.67/6.18    inference(superposition,[],[f18261,f402])).
% 45.67/6.18  fof(f18261,plain,(
% 45.67/6.18    ( ! [X61,X62,X63] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X62,k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X62,X63)))),X63)) )),
% 45.67/6.18    inference(forward_demodulation,[],[f17972,f262])).
% 45.67/6.18  fof(f17972,plain,(
% 45.67/6.18    ( ! [X61,X62,X63] : (k4_xboole_0(k5_xboole_0(X62,k4_xboole_0(X62,k4_xboole_0(X61,k4_xboole_0(X62,X63)))),X63) = k4_xboole_0(k4_xboole_0(X61,k4_xboole_0(X62,X63)),k4_xboole_0(X61,k4_xboole_0(X62,X63)))) )),
% 45.67/6.18    inference(superposition,[],[f390,f240])).
% 45.67/6.18  fof(f395,plain,(
% 45.67/6.18    ( ! [X14,X15] : (k4_xboole_0(X14,X15) = k4_xboole_0(X14,k5_xboole_0(X14,k4_xboole_0(X14,X15)))) )),
% 45.67/6.18    inference(backward_demodulation,[],[f327,f372])).
% 45.67/6.18  fof(f327,plain,(
% 45.67/6.18    ( ! [X14,X15] : (k4_xboole_0(X14,X15) = k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X14,X15)))) )),
% 45.67/6.18    inference(forward_demodulation,[],[f300,f111])).
% 45.67/6.18  fof(f300,plain,(
% 45.67/6.18    ( ! [X14,X15] : (k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X14,X15))) = k4_xboole_0(k4_xboole_0(X14,k1_xboole_0),X15)) )),
% 45.67/6.18    inference(superposition,[],[f35,f262])).
% 45.67/6.18  fof(f904,plain,(
% 45.67/6.18    ( ! [X26,X25] : (k5_xboole_0(k4_xboole_0(X25,X26),k5_xboole_0(X26,k4_xboole_0(X26,X25))) = X25) )),
% 45.67/6.18    inference(superposition,[],[f425,f385])).
% 45.67/6.18  fof(f425,plain,(
% 45.67/6.18    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 45.67/6.18    inference(superposition,[],[f370,f294])).
% 45.67/6.18  fof(f5210,plain,(
% 45.67/6.18    ( ! [X45,X46] : (k4_xboole_0(k5_xboole_0(X45,X46),X46) = k5_xboole_0(k4_xboole_0(X46,k5_xboole_0(X45,X46)),X45)) )),
% 45.67/6.18    inference(superposition,[],[f2672,f425])).
% 45.67/6.18  fof(f62550,plain,(
% 45.67/6.18    ( ! [X159,X160] : (k5_xboole_0(X159,X160) = k4_xboole_0(k5_xboole_0(X159,k4_xboole_0(X160,X159)),k4_xboole_0(X159,k5_xboole_0(X159,X160)))) )),
% 45.67/6.18    inference(superposition,[],[f2073,f61789])).
% 45.67/6.18  fof(f2073,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1) )),
% 45.67/6.18    inference(forward_demodulation,[],[f2071,f111])).
% 45.67/6.18  fof(f2071,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) )),
% 45.67/6.18    inference(backward_demodulation,[],[f187,f2069])).
% 45.67/6.18  fof(f187,plain,(
% 45.67/6.18    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1))) )),
% 45.67/6.18    inference(superposition,[],[f32,f34])).
% 45.67/6.18  fof(f417,plain,(
% 45.67/6.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_3),
% 45.67/6.18    inference(avatar_component_clause,[],[f415])).
% 45.67/6.18  fof(f415,plain,(
% 45.67/6.18    spl2_3 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 45.67/6.18    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 45.67/6.18  fof(f418,plain,(
% 45.67/6.18    ~spl2_3 | spl2_1),
% 45.67/6.18    inference(avatar_split_clause,[],[f401,f37,f415])).
% 45.67/6.18  fof(f37,plain,(
% 45.67/6.18    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 45.67/6.18    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 45.67/6.18  fof(f401,plain,(
% 45.67/6.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 45.67/6.18    inference(backward_demodulation,[],[f39,f372])).
% 45.67/6.18  fof(f39,plain,(
% 45.67/6.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 45.67/6.18    inference(avatar_component_clause,[],[f37])).
% 45.67/6.18  fof(f57,plain,(
% 45.67/6.18    spl2_2),
% 45.67/6.18    inference(avatar_split_clause,[],[f51,f53])).
% 45.67/6.18  fof(f53,plain,(
% 45.67/6.18    spl2_2 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 45.67/6.18    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 45.67/6.18  fof(f51,plain,(
% 45.67/6.18    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 45.67/6.18    inference(superposition,[],[f42,f31])).
% 45.67/6.18  fof(f56,plain,(
% 45.67/6.18    spl2_2),
% 45.67/6.18    inference(avatar_split_clause,[],[f50,f53])).
% 45.67/6.18  fof(f50,plain,(
% 45.67/6.18    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 45.67/6.18    inference(superposition,[],[f31,f42])).
% 45.67/6.18  fof(f40,plain,(
% 45.67/6.18    ~spl2_1),
% 45.67/6.18    inference(avatar_split_clause,[],[f30,f37])).
% 45.67/6.18  fof(f30,plain,(
% 45.67/6.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 45.67/6.18    inference(definition_unfolding,[],[f17,f23,f24])).
% 45.67/6.18  fof(f17,plain,(
% 45.67/6.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 45.67/6.18    inference(cnf_transformation,[],[f16])).
% 45.67/6.18  fof(f16,plain,(
% 45.67/6.18    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 45.67/6.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 45.67/6.18  fof(f15,plain,(
% 45.67/6.18    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 45.67/6.18    introduced(choice_axiom,[])).
% 45.67/6.18  fof(f14,plain,(
% 45.67/6.18    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 45.67/6.18    inference(ennf_transformation,[],[f13])).
% 45.67/6.18  fof(f13,negated_conjecture,(
% 45.67/6.18    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 45.67/6.18    inference(negated_conjecture,[],[f12])).
% 45.67/6.18  fof(f12,conjecture,(
% 45.67/6.18    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 45.67/6.18    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 45.67/6.18  % SZS output end Proof for theBenchmark
% 45.67/6.18  % (30196)------------------------------
% 45.67/6.18  % (30196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 45.67/6.18  % (30196)Termination reason: Refutation
% 45.67/6.18  
% 45.67/6.18  % (30196)Memory used [KB]: 139443
% 45.67/6.18  % (30196)Time elapsed: 5.691 s
% 45.67/6.18  % (30196)------------------------------
% 45.67/6.18  % (30196)------------------------------
% 46.53/6.20  % (30185)Success in time 5.836 s
%------------------------------------------------------------------------------
