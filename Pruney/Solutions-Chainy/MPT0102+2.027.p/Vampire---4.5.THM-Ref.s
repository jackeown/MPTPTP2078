%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:59 EST 2020

% Result     : Theorem 4.51s
% Output     : Refutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :  158 (2605 expanded)
%              Number of leaves         :   25 ( 857 expanded)
%              Depth                    :   31
%              Number of atoms          :  206 (3036 expanded)
%              Number of equality atoms :  134 (2327 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9729,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f65,f71,f844,f845,f3601,f3608,f3661,f9202,f9208,f9261,f9626])).

fof(f9626,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f9625])).

fof(f9625,plain,
    ( $false
    | spl2_7 ),
    inference(subsumption_resolution,[],[f3660,f9624])).

fof(f9624,plain,(
    ! [X52,X53] : k3_xboole_0(X52,X53) = k4_xboole_0(k2_xboole_0(X52,X53),k2_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(X53,X52))) ),
    inference(forward_demodulation,[],[f9517,f7350])).

fof(f7350,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)),k3_xboole_0(X8,X9)) ),
    inference(backward_demodulation,[],[f4985,f7346])).

fof(f7346,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k2_xboole_0(X12,X14),k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X14,X12)) ),
    inference(backward_demodulation,[],[f5442,f7258])).

fof(f7258,plain,(
    ! [X52,X50,X51] : k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,k3_xboole_0(X50,X51))) = k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,X50)) ),
    inference(superposition,[],[f1393,f2968])).

fof(f2968,plain,(
    ! [X30,X31] : k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) = X30 ),
    inference(forward_demodulation,[],[f2923,f301])).

fof(f301,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,X14),X13) = X13 ),
    inference(superposition,[],[f179,f173])).

fof(f173,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f164,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f164,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f30,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f179,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f31,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f2923,plain,(
    ! [X30,X31] : k2_xboole_0(k4_xboole_0(X30,X31),X30) = k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) ),
    inference(superposition,[],[f753,f2685])).

fof(f2685,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2626,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f28,f25])).

fof(f2626,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f38,f150])).

fof(f150,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(X6,X6) ),
    inference(backward_demodulation,[],[f83,f147])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f146,f35])).

fof(f146,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f145,f25])).

fof(f145,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f138,f30])).

fof(f138,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f98,f83])).

fof(f98,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f89,f28])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f87,f56])).

fof(f87,plain,(
    ! [X6,X7] : r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f83,plain,(
    ! [X6] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6) ),
    inference(superposition,[],[f29,f48])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f753,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(forward_demodulation,[],[f714,f25])).

fof(f714,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X11,X12),k1_xboole_0) ),
    inference(superposition,[],[f571,f30])).

fof(f571,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f545,f286])).

fof(f286,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f285,f171])).

fof(f171,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f163,f30])).

fof(f163,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f30,f29])).

fof(f285,plain,(
    ! [X8,X7] : k2_xboole_0(X7,k2_xboole_0(X8,X7)) = k2_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f272,f28])).

fof(f272,plain,(
    ! [X8,X7] : k2_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f171,f171])).

fof(f545,plain,(
    ! [X4,X3] : k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f30,f290])).

fof(f290,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f276,f204])).

fof(f204,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f188,f28])).

fof(f188,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f187,f150])).

fof(f187,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f29,f31])).

fof(f276,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5)) ),
    inference(superposition,[],[f29,f171])).

fof(f1393,plain,(
    ! [X14,X15,X13] : k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15))) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f5442,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k2_xboole_0(X12,X14),k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X14,k3_xboole_0(X12,X13))) ),
    inference(superposition,[],[f39,f3216])).

fof(f3216,plain,(
    ! [X12,X11] : k4_xboole_0(X11,X12) = k4_xboole_0(X11,k3_xboole_0(X11,X12)) ),
    inference(backward_demodulation,[],[f2893,f3194])).

fof(f3194,plain,(
    ! [X24,X23] : k4_xboole_0(X23,X24) = k3_xboole_0(X23,k4_xboole_0(X23,X24)) ),
    inference(superposition,[],[f2980,f173])).

fof(f2980,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X17) = X17 ),
    inference(backward_demodulation,[],[f2944,f2979])).

fof(f2979,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X4,X3)) = X3 ),
    inference(forward_demodulation,[],[f2978,f301])).

fof(f2978,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(superposition,[],[f38,f2935])).

fof(f2935,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f2888,f174])).

fof(f174,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f165,f48])).

fof(f165,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,k1_xboole_0) ),
    inference(superposition,[],[f30,f48])).

fof(f2888,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f2685,f150])).

fof(f2944,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X17,k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f2896,f1147])).

fof(f1147,plain,(
    ! [X12,X11] : k4_xboole_0(X12,k4_xboole_0(X11,X12)) = k4_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f81,f1025])).

fof(f1025,plain,(
    ! [X12,X11] : k2_xboole_0(X12,X11) = k2_xboole_0(k4_xboole_0(X12,X11),X11) ),
    inference(forward_demodulation,[],[f992,f759])).

fof(f759,plain,(
    ! [X8,X9] : k2_xboole_0(X9,X8) = k4_xboole_0(k2_xboole_0(X8,X9),k1_xboole_0) ),
    inference(forward_demodulation,[],[f731,f174])).

fof(f731,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X9,X8),k1_xboole_0) ),
    inference(superposition,[],[f29,f571])).

fof(f992,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k4_xboole_0(k2_xboole_0(X11,X12),k1_xboole_0) ),
    inference(superposition,[],[f759,f30])).

fof(f81,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3) ),
    inference(superposition,[],[f29,f28])).

fof(f2896,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17)) ),
    inference(superposition,[],[f2685,f29])).

fof(f2893,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k3_xboole_0(X11,X12)) = k3_xboole_0(X11,k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f2685,f2685])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f4985,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)),k3_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f29,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f9517,plain,(
    ! [X52,X53] : k3_xboole_0(X52,X53) = k4_xboole_0(k2_xboole_0(X52,X53),k4_xboole_0(k2_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(X53,X52)),k3_xboole_0(X52,X53))) ),
    inference(superposition,[],[f2982,f42])).

fof(f2982,plain,(
    ! [X12,X11] : k4_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X11,X12)) = X12 ),
    inference(backward_demodulation,[],[f1147,f2979])).

fof(f3660,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f3658])).

fof(f3658,plain,
    ( spl2_7
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f9261,plain,
    ( ~ spl2_10
    | spl2_9 ),
    inference(avatar_split_clause,[],[f9256,f9205,f9258])).

fof(f9258,plain,
    ( spl2_10
  <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f9205,plain,
    ( spl2_9
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f9256,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK1,sK0)
    | spl2_9 ),
    inference(superposition,[],[f9207,f48])).

fof(f9207,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK0))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f9205])).

fof(f9208,plain,
    ( ~ spl2_9
    | spl2_6 ),
    inference(avatar_split_clause,[],[f9203,f3605,f9205])).

fof(f3605,plain,
    ( spl2_6
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f9203,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK0))
    | spl2_6 ),
    inference(forward_demodulation,[],[f9194,f2685])).

fof(f9194,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | spl2_6 ),
    inference(backward_demodulation,[],[f3607,f9190])).

fof(f9190,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X28,X30) = k4_xboole_0(k2_xboole_0(X29,X28),k2_xboole_0(k4_xboole_0(X29,X28),X30)) ),
    inference(forward_demodulation,[],[f9060,f3383])).

fof(f3383,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,X9) = k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X8,X7),X9)) ),
    inference(superposition,[],[f36,f2979])).

fof(f9060,plain,(
    ! [X30,X28,X29] : k4_xboole_0(X28,k2_xboole_0(k4_xboole_0(X29,X28),X30)) = k4_xboole_0(k2_xboole_0(X29,X28),k2_xboole_0(k4_xboole_0(X29,X28),X30)) ),
    inference(superposition,[],[f1418,f1033])).

fof(f1033,plain,(
    ! [X26,X27] : k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(X26,X27)) ),
    inference(forward_demodulation,[],[f1000,f759])).

fof(f1000,plain,(
    ! [X26,X27] : k2_xboole_0(X27,k4_xboole_0(X26,X27)) = k4_xboole_0(k2_xboole_0(X27,X26),k1_xboole_0) ),
    inference(superposition,[],[f759,f753])).

fof(f1418,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f1370,f36])).

fof(f1370,plain,(
    ! [X14,X15,X13] : k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),X15) ),
    inference(superposition,[],[f36,f29])).

fof(f3607,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f3605])).

fof(f9202,plain,
    ( ~ spl2_8
    | spl2_5 ),
    inference(avatar_split_clause,[],[f9197,f3598,f9199])).

fof(f9199,plain,
    ( spl2_8
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK1,sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f3598,plain,
    ( spl2_5
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f9197,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k3_xboole_0(sK1,sK0),k1_xboole_0)
    | spl2_5 ),
    inference(forward_demodulation,[],[f9193,f2685])).

fof(f9193,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k1_xboole_0)
    | spl2_5 ),
    inference(backward_demodulation,[],[f3600,f9190])).

fof(f3600,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f3598])).

fof(f3661,plain,
    ( ~ spl2_7
    | spl2_6 ),
    inference(avatar_split_clause,[],[f3656,f3605,f3658])).

fof(f3656,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl2_6 ),
    inference(superposition,[],[f3607,f48])).

fof(f3608,plain,
    ( ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f3603,f44,f3605])).

fof(f44,plain,
    ( spl2_1
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3603,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f3602,f1643])).

fof(f1643,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f1416,f28])).

fof(f1416,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X7,X9))) ),
    inference(forward_demodulation,[],[f1415,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1415,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9)) ),
    inference(forward_demodulation,[],[f1368,f147])).

fof(f1368,plain,(
    ! [X8,X7,X9] : k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9)) = k4_xboole_0(k1_xboole_0,X9) ),
    inference(superposition,[],[f36,f204])).

fof(f3602,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(forward_demodulation,[],[f3594,f36])).

fof(f3594,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(backward_demodulation,[],[f46,f3592])).

fof(f3592,plain,(
    ! [X47,X48,X46,X49] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X46,X47),X49),k2_xboole_0(X46,X48)) = k4_xboole_0(X49,k2_xboole_0(X46,X48)) ),
    inference(forward_demodulation,[],[f3497,f48])).

fof(f3497,plain,(
    ! [X47,X48,X46,X49] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X46,X47),X49),k2_xboole_0(X46,X48)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X49,k2_xboole_0(X46,X48))) ),
    inference(superposition,[],[f39,f1422])).

fof(f1422,plain,(
    ! [X24,X23,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X22,X23),k2_xboole_0(X22,X24)) ),
    inference(forward_demodulation,[],[f1373,f147])).

fof(f1373,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k4_xboole_0(X22,X23),k2_xboole_0(X22,X24)) = k4_xboole_0(k1_xboole_0,X24) ),
    inference(superposition,[],[f36,f56])).

fof(f46,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f3601,plain,
    ( ~ spl2_5
    | spl2_4 ),
    inference(avatar_split_clause,[],[f3596,f841,f3598])).

fof(f841,plain,
    ( spl2_4
  <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f3596,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0)
    | spl2_4 ),
    inference(forward_demodulation,[],[f3595,f1643])).

fof(f3595,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))))
    | spl2_4 ),
    inference(forward_demodulation,[],[f3593,f36])).

fof(f3593,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(backward_demodulation,[],[f843,f3592])).

fof(f843,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f841])).

fof(f845,plain,
    ( ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f839,f44,f841])).

fof(f839,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(superposition,[],[f46,f28])).

fof(f844,plain,
    ( ~ spl2_4
    | spl2_1 ),
    inference(avatar_split_clause,[],[f838,f44,f841])).

fof(f838,plain,
    ( k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(superposition,[],[f46,f28])).

fof(f71,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f66,f62,f68])).

fof(f68,plain,
    ( spl2_3
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f62,plain,
    ( spl2_2
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f66,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(resolution,[],[f64,f35])).

fof(f64,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f60,f62])).

fof(f60,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f58,f56])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f27,f56])).

fof(f47,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f40,f44])).

fof(f40,plain,(
    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f23,f32,f32])).

fof(f23,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:16:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (16336)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (16334)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (16338)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (16343)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (16342)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (16343)Refutation not found, incomplete strategy% (16343)------------------------------
% 0.22/0.47  % (16343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16335)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (16343)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (16343)Memory used [KB]: 10618
% 0.22/0.48  % (16343)Time elapsed: 0.050 s
% 0.22/0.48  % (16343)------------------------------
% 0.22/0.48  % (16343)------------------------------
% 0.22/0.48  % (16339)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (16333)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (16346)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (16332)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (16337)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (16344)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (16348)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (16345)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (16341)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (16347)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (16340)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (16349)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 4.51/0.97  % (16342)Refutation found. Thanks to Tanya!
% 4.51/0.97  % SZS status Theorem for theBenchmark
% 4.94/0.98  % SZS output start Proof for theBenchmark
% 4.94/0.99  fof(f9729,plain,(
% 4.94/0.99    $false),
% 4.94/0.99    inference(avatar_sat_refutation,[],[f47,f65,f71,f844,f845,f3601,f3608,f3661,f9202,f9208,f9261,f9626])).
% 4.94/0.99  fof(f9626,plain,(
% 4.94/0.99    spl2_7),
% 4.94/0.99    inference(avatar_contradiction_clause,[],[f9625])).
% 4.94/0.99  fof(f9625,plain,(
% 4.94/0.99    $false | spl2_7),
% 4.94/0.99    inference(subsumption_resolution,[],[f3660,f9624])).
% 4.94/0.99  fof(f9624,plain,(
% 4.94/0.99    ( ! [X52,X53] : (k3_xboole_0(X52,X53) = k4_xboole_0(k2_xboole_0(X52,X53),k2_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(X53,X52)))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f9517,f7350])).
% 4.94/0.99  fof(f7350,plain,(
% 4.94/0.99    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)),k3_xboole_0(X8,X9))) )),
% 4.94/0.99    inference(backward_demodulation,[],[f4985,f7346])).
% 4.94/0.99  fof(f7346,plain,(
% 4.94/0.99    ( ! [X14,X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X14),k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X14,X12))) )),
% 4.94/0.99    inference(backward_demodulation,[],[f5442,f7258])).
% 4.94/0.99  fof(f7258,plain,(
% 4.94/0.99    ( ! [X52,X50,X51] : (k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,k3_xboole_0(X50,X51))) = k2_xboole_0(k4_xboole_0(X50,X51),k4_xboole_0(X52,X50))) )),
% 4.94/0.99    inference(superposition,[],[f1393,f2968])).
% 4.94/0.99  fof(f2968,plain,(
% 4.94/0.99    ( ! [X30,X31] : (k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31)) = X30) )),
% 4.94/0.99    inference(forward_demodulation,[],[f2923,f301])).
% 4.94/0.99  fof(f301,plain,(
% 4.94/0.99    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,X14),X13) = X13) )),
% 4.94/0.99    inference(superposition,[],[f179,f173])).
% 4.94/0.99  fof(f173,plain,(
% 4.94/0.99    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 4.94/0.99    inference(forward_demodulation,[],[f164,f25])).
% 4.94/0.99  fof(f25,plain,(
% 4.94/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.94/0.99    inference(cnf_transformation,[],[f5])).
% 4.94/0.99  fof(f5,axiom,(
% 4.94/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 4.94/0.99  fof(f164,plain,(
% 4.94/0.99    ( ! [X4,X3] : (k2_xboole_0(X3,k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 4.94/0.99    inference(superposition,[],[f30,f56])).
% 4.94/0.99  fof(f56,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 4.94/0.99    inference(resolution,[],[f35,f27])).
% 4.94/0.99  fof(f27,plain,(
% 4.94/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.94/0.99    inference(cnf_transformation,[],[f6])).
% 4.94/0.99  fof(f6,axiom,(
% 4.94/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.94/0.99  fof(f35,plain,(
% 4.94/0.99    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 4.94/0.99    inference(cnf_transformation,[],[f22])).
% 4.94/0.99  fof(f22,plain,(
% 4.94/0.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.94/0.99    inference(nnf_transformation,[],[f4])).
% 4.94/0.99  fof(f4,axiom,(
% 4.94/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.94/0.99  fof(f30,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f7])).
% 4.94/0.99  fof(f7,axiom,(
% 4.94/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.94/0.99  fof(f179,plain,(
% 4.94/0.99    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 4.94/0.99    inference(superposition,[],[f31,f28])).
% 4.94/0.99  fof(f28,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.94/0.99    inference(cnf_transformation,[],[f1])).
% 4.94/0.99  fof(f1,axiom,(
% 4.94/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.94/0.99  fof(f31,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f13])).
% 4.94/0.99  fof(f13,axiom,(
% 4.94/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 4.94/0.99  fof(f2923,plain,(
% 4.94/0.99    ( ! [X30,X31] : (k2_xboole_0(k4_xboole_0(X30,X31),X30) = k2_xboole_0(k3_xboole_0(X30,X31),k4_xboole_0(X30,X31))) )),
% 4.94/0.99    inference(superposition,[],[f753,f2685])).
% 4.94/0.99  fof(f2685,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f2626,f48])).
% 4.94/0.99  fof(f48,plain,(
% 4.94/0.99    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.94/0.99    inference(superposition,[],[f28,f25])).
% 4.94/0.99  fof(f2626,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) )),
% 4.94/0.99    inference(superposition,[],[f38,f150])).
% 4.94/0.99  fof(f150,plain,(
% 4.94/0.99    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(X6,X6)) )),
% 4.94/0.99    inference(backward_demodulation,[],[f83,f147])).
% 4.94/0.99  fof(f147,plain,(
% 4.94/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 4.94/0.99    inference(resolution,[],[f146,f35])).
% 4.94/0.99  fof(f146,plain,(
% 4.94/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.94/0.99    inference(forward_demodulation,[],[f145,f25])).
% 4.94/0.99  fof(f145,plain,(
% 4.94/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f138,f30])).
% 4.94/0.99  fof(f138,plain,(
% 4.94/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)))) )),
% 4.94/0.99    inference(superposition,[],[f98,f83])).
% 4.94/0.99  fof(f98,plain,(
% 4.94/0.99    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f89,f28])).
% 4.94/0.99  fof(f89,plain,(
% 4.94/0.99    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 4.94/0.99    inference(superposition,[],[f87,f56])).
% 4.94/0.99  fof(f87,plain,(
% 4.94/0.99    ( ! [X6,X7] : (r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X6,X7))) )),
% 4.94/0.99    inference(superposition,[],[f27,f29])).
% 4.94/0.99  fof(f29,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 4.94/0.99    inference(cnf_transformation,[],[f8])).
% 4.94/0.99  fof(f8,axiom,(
% 4.94/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 4.94/0.99  fof(f83,plain,(
% 4.94/0.99    ( ! [X6] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,X6)) )),
% 4.94/0.99    inference(superposition,[],[f29,f48])).
% 4.94/0.99  fof(f38,plain,(
% 4.94/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f12])).
% 4.94/0.99  fof(f12,axiom,(
% 4.94/0.99    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 4.94/0.99  fof(f753,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 4.94/0.99    inference(forward_demodulation,[],[f714,f25])).
% 4.94/0.99  fof(f714,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k2_xboole_0(X11,X12),k1_xboole_0)) )),
% 4.94/0.99    inference(superposition,[],[f571,f30])).
% 4.94/0.99  fof(f571,plain,(
% 4.94/0.99    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0)) )),
% 4.94/0.99    inference(forward_demodulation,[],[f545,f286])).
% 4.94/0.99  fof(f286,plain,(
% 4.94/0.99    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f285,f171])).
% 4.94/0.99  fof(f171,plain,(
% 4.94/0.99    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k2_xboole_0(X1,X2))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f163,f30])).
% 4.94/0.99  fof(f163,plain,(
% 4.94/0.99    ( ! [X2,X1] : (k2_xboole_0(X2,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k4_xboole_0(X1,X2))) )),
% 4.94/0.99    inference(superposition,[],[f30,f29])).
% 4.94/0.99  fof(f285,plain,(
% 4.94/0.99    ( ! [X8,X7] : (k2_xboole_0(X7,k2_xboole_0(X8,X7)) = k2_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f272,f28])).
% 4.94/0.99  fof(f272,plain,(
% 4.94/0.99    ( ! [X8,X7] : (k2_xboole_0(k2_xboole_0(X8,X7),X7) = k2_xboole_0(k2_xboole_0(X8,X7),k2_xboole_0(X7,X8))) )),
% 4.94/0.99    inference(superposition,[],[f171,f171])).
% 4.94/0.99  fof(f545,plain,(
% 4.94/0.99    ( ! [X4,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),k1_xboole_0) = k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4))) )),
% 4.94/0.99    inference(superposition,[],[f30,f290])).
% 4.94/0.99  fof(f290,plain,(
% 4.94/0.99    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f276,f204])).
% 4.94/0.99  fof(f204,plain,(
% 4.94/0.99    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 4.94/0.99    inference(superposition,[],[f188,f28])).
% 4.94/0.99  fof(f188,plain,(
% 4.94/0.99    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X4,k2_xboole_0(X4,X5))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f187,f150])).
% 4.94/0.99  fof(f187,plain,(
% 4.94/0.99    ( ! [X4,X5] : (k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X4,X5))) )),
% 4.94/0.99    inference(superposition,[],[f29,f31])).
% 4.94/0.99  fof(f276,plain,(
% 4.94/0.99    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X6,X5)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X6,X5))) )),
% 4.94/0.99    inference(superposition,[],[f29,f171])).
% 4.94/0.99  fof(f1393,plain,(
% 4.94/0.99    ( ! [X14,X15,X13] : (k2_xboole_0(X15,k4_xboole_0(X13,X14)) = k2_xboole_0(X15,k4_xboole_0(X13,k2_xboole_0(X14,X15)))) )),
% 4.94/0.99    inference(superposition,[],[f30,f36])).
% 4.94/0.99  fof(f36,plain,(
% 4.94/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f9])).
% 4.94/0.99  fof(f9,axiom,(
% 4.94/0.99    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.94/0.99  fof(f5442,plain,(
% 4.94/0.99    ( ! [X14,X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X14),k3_xboole_0(X12,X13)) = k2_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(X14,k3_xboole_0(X12,X13)))) )),
% 4.94/0.99    inference(superposition,[],[f39,f3216])).
% 4.94/0.99  fof(f3216,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k4_xboole_0(X11,k3_xboole_0(X11,X12))) )),
% 4.94/0.99    inference(backward_demodulation,[],[f2893,f3194])).
% 4.94/0.99  fof(f3194,plain,(
% 4.94/0.99    ( ! [X24,X23] : (k4_xboole_0(X23,X24) = k3_xboole_0(X23,k4_xboole_0(X23,X24))) )),
% 4.94/0.99    inference(superposition,[],[f2980,f173])).
% 4.94/0.99  fof(f2980,plain,(
% 4.94/0.99    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X17) = X17) )),
% 4.94/0.99    inference(backward_demodulation,[],[f2944,f2979])).
% 4.94/0.99  fof(f2979,plain,(
% 4.94/0.99    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X4,X3)) = X3) )),
% 4.94/0.99    inference(forward_demodulation,[],[f2978,f301])).
% 4.94/0.99  fof(f2978,plain,(
% 4.94/0.99    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k4_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 4.94/0.99    inference(superposition,[],[f38,f2935])).
% 4.94/0.99  fof(f2935,plain,(
% 4.94/0.99    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.94/0.99    inference(forward_demodulation,[],[f2888,f174])).
% 4.94/0.99  fof(f174,plain,(
% 4.94/0.99    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 4.94/0.99    inference(forward_demodulation,[],[f165,f48])).
% 4.94/0.99  fof(f165,plain,(
% 4.94/0.99    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X6,k1_xboole_0)) )),
% 4.94/0.99    inference(superposition,[],[f30,f48])).
% 4.94/0.99  fof(f2888,plain,(
% 4.94/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 4.94/0.99    inference(superposition,[],[f2685,f150])).
% 4.94/0.99  fof(f2944,plain,(
% 4.94/0.99    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(X17,k4_xboole_0(X16,X17))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f2896,f1147])).
% 4.94/0.99  fof(f1147,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k4_xboole_0(X12,k4_xboole_0(X11,X12)) = k4_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X11,X12))) )),
% 4.94/0.99    inference(superposition,[],[f81,f1025])).
% 4.94/0.99  fof(f1025,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k2_xboole_0(X12,X11) = k2_xboole_0(k4_xboole_0(X12,X11),X11)) )),
% 4.94/0.99    inference(forward_demodulation,[],[f992,f759])).
% 4.94/0.99  fof(f759,plain,(
% 4.94/0.99    ( ! [X8,X9] : (k2_xboole_0(X9,X8) = k4_xboole_0(k2_xboole_0(X8,X9),k1_xboole_0)) )),
% 4.94/0.99    inference(forward_demodulation,[],[f731,f174])).
% 4.94/0.99  fof(f731,plain,(
% 4.94/0.99    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k1_xboole_0) = k4_xboole_0(k2_xboole_0(X9,X8),k1_xboole_0)) )),
% 4.94/0.99    inference(superposition,[],[f29,f571])).
% 4.94/0.99  fof(f992,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k4_xboole_0(k2_xboole_0(X11,X12),k1_xboole_0)) )),
% 4.94/0.99    inference(superposition,[],[f759,f30])).
% 4.94/0.99  fof(f81,plain,(
% 4.94/0.99    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)) )),
% 4.94/0.99    inference(superposition,[],[f29,f28])).
% 4.94/0.99  fof(f2896,plain,(
% 4.94/0.99    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X17) = k4_xboole_0(k2_xboole_0(X16,X17),k4_xboole_0(X16,X17))) )),
% 4.94/0.99    inference(superposition,[],[f2685,f29])).
% 4.94/0.99  fof(f2893,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k4_xboole_0(X11,k3_xboole_0(X11,X12)) = k3_xboole_0(X11,k4_xboole_0(X11,X12))) )),
% 4.94/0.99    inference(superposition,[],[f2685,f2685])).
% 4.94/0.99  fof(f39,plain,(
% 4.94/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f10])).
% 4.94/0.99  fof(f10,axiom,(
% 4.94/0.99    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 4.94/0.99  fof(f4985,plain,(
% 4.94/0.99    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,X8)),k3_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(X8,X9),k3_xboole_0(X8,X9))) )),
% 4.94/0.99    inference(superposition,[],[f29,f42])).
% 4.94/0.99  fof(f42,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k3_xboole_0(X0,X1))) )),
% 4.94/0.99    inference(definition_unfolding,[],[f33,f32])).
% 4.94/0.99  fof(f32,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f2])).
% 4.94/0.99  fof(f2,axiom,(
% 4.94/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 4.94/0.99  fof(f33,plain,(
% 4.94/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f15])).
% 4.94/0.99  fof(f15,axiom,(
% 4.94/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 4.94/0.99  fof(f9517,plain,(
% 4.94/0.99    ( ! [X52,X53] : (k3_xboole_0(X52,X53) = k4_xboole_0(k2_xboole_0(X52,X53),k4_xboole_0(k2_xboole_0(k4_xboole_0(X52,X53),k4_xboole_0(X53,X52)),k3_xboole_0(X52,X53)))) )),
% 4.94/0.99    inference(superposition,[],[f2982,f42])).
% 4.94/0.99  fof(f2982,plain,(
% 4.94/0.99    ( ! [X12,X11] : (k4_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(X11,X12)) = X12) )),
% 4.94/0.99    inference(backward_demodulation,[],[f1147,f2979])).
% 4.94/0.99  fof(f3660,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_7),
% 4.94/0.99    inference(avatar_component_clause,[],[f3658])).
% 4.94/0.99  fof(f3658,plain,(
% 4.94/0.99    spl2_7 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 4.94/0.99  fof(f9261,plain,(
% 4.94/0.99    ~spl2_10 | spl2_9),
% 4.94/0.99    inference(avatar_split_clause,[],[f9256,f9205,f9258])).
% 4.94/0.99  fof(f9258,plain,(
% 4.94/0.99    spl2_10 <=> k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,sK0)),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 4.94/0.99  fof(f9205,plain,(
% 4.94/0.99    spl2_9 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK0))),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 4.94/0.99  fof(f9256,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK1,sK0) | spl2_9),
% 4.94/0.99    inference(superposition,[],[f9207,f48])).
% 4.94/0.99  fof(f9207,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK0)) | spl2_9),
% 4.94/0.99    inference(avatar_component_clause,[],[f9205])).
% 4.94/0.99  fof(f9208,plain,(
% 4.94/0.99    ~spl2_9 | spl2_6),
% 4.94/0.99    inference(avatar_split_clause,[],[f9203,f3605,f9205])).
% 4.94/0.99  fof(f3605,plain,(
% 4.94/0.99    spl2_6 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 4.94/0.99  fof(f9203,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,sK0)) | spl2_6),
% 4.94/0.99    inference(forward_demodulation,[],[f9194,f2685])).
% 4.94/0.99  fof(f9194,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | spl2_6),
% 4.94/0.99    inference(backward_demodulation,[],[f3607,f9190])).
% 4.94/0.99  fof(f9190,plain,(
% 4.94/0.99    ( ! [X30,X28,X29] : (k4_xboole_0(X28,X30) = k4_xboole_0(k2_xboole_0(X29,X28),k2_xboole_0(k4_xboole_0(X29,X28),X30))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f9060,f3383])).
% 4.94/0.99  fof(f3383,plain,(
% 4.94/0.99    ( ! [X8,X7,X9] : (k4_xboole_0(X7,X9) = k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X8,X7),X9))) )),
% 4.94/0.99    inference(superposition,[],[f36,f2979])).
% 4.94/0.99  fof(f9060,plain,(
% 4.94/0.99    ( ! [X30,X28,X29] : (k4_xboole_0(X28,k2_xboole_0(k4_xboole_0(X29,X28),X30)) = k4_xboole_0(k2_xboole_0(X29,X28),k2_xboole_0(k4_xboole_0(X29,X28),X30))) )),
% 4.94/0.99    inference(superposition,[],[f1418,f1033])).
% 4.94/0.99  fof(f1033,plain,(
% 4.94/0.99    ( ! [X26,X27] : (k2_xboole_0(X26,X27) = k2_xboole_0(X27,k4_xboole_0(X26,X27))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f1000,f759])).
% 4.94/0.99  fof(f1000,plain,(
% 4.94/0.99    ( ! [X26,X27] : (k2_xboole_0(X27,k4_xboole_0(X26,X27)) = k4_xboole_0(k2_xboole_0(X27,X26),k1_xboole_0)) )),
% 4.94/0.99    inference(superposition,[],[f759,f753])).
% 4.94/0.99  fof(f1418,plain,(
% 4.94/0.99    ( ! [X14,X15,X13] : (k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(X13,k2_xboole_0(X14,X15))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f1370,f36])).
% 4.94/0.99  fof(f1370,plain,(
% 4.94/0.99    ( ! [X14,X15,X13] : (k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(X14,X15)) = k4_xboole_0(k4_xboole_0(X13,X14),X15)) )),
% 4.94/0.99    inference(superposition,[],[f36,f29])).
% 4.94/0.99  fof(f3607,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_6),
% 4.94/0.99    inference(avatar_component_clause,[],[f3605])).
% 4.94/0.99  fof(f9202,plain,(
% 4.94/0.99    ~spl2_8 | spl2_5),
% 4.94/0.99    inference(avatar_split_clause,[],[f9197,f3598,f9199])).
% 4.94/0.99  fof(f9199,plain,(
% 4.94/0.99    spl2_8 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK1,sK0),k1_xboole_0)),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 4.94/0.99  fof(f3598,plain,(
% 4.94/0.99    spl2_5 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0)),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 4.94/0.99  fof(f9197,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k3_xboole_0(sK1,sK0),k1_xboole_0) | spl2_5),
% 4.94/0.99    inference(forward_demodulation,[],[f9193,f2685])).
% 4.94/0.99  fof(f9193,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k1_xboole_0) | spl2_5),
% 4.94/0.99    inference(backward_demodulation,[],[f3600,f9190])).
% 4.94/0.99  fof(f3600,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) | spl2_5),
% 4.94/0.99    inference(avatar_component_clause,[],[f3598])).
% 4.94/0.99  fof(f3661,plain,(
% 4.94/0.99    ~spl2_7 | spl2_6),
% 4.94/0.99    inference(avatar_split_clause,[],[f3656,f3605,f3658])).
% 4.94/0.99  fof(f3656,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl2_6),
% 4.94/0.99    inference(superposition,[],[f3607,f48])).
% 4.94/0.99  fof(f3608,plain,(
% 4.94/0.99    ~spl2_6 | spl2_1),
% 4.94/0.99    inference(avatar_split_clause,[],[f3603,f44,f3605])).
% 4.94/0.99  fof(f44,plain,(
% 4.94/0.99    spl2_1 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 4.94/0.99  fof(f3603,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 4.94/0.99    inference(forward_demodulation,[],[f3602,f1643])).
% 4.94/0.99  fof(f1643,plain,(
% 4.94/0.99    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 4.94/0.99    inference(superposition,[],[f1416,f28])).
% 4.94/0.99  fof(f1416,plain,(
% 4.94/0.99    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k2_xboole_0(X7,X9)))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f1415,f37])).
% 4.94/0.99  fof(f37,plain,(
% 4.94/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.94/0.99    inference(cnf_transformation,[],[f11])).
% 4.94/0.99  fof(f11,axiom,(
% 4.94/0.99    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.94/0.99  fof(f1415,plain,(
% 4.94/0.99    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f1368,f147])).
% 4.94/0.99  fof(f1368,plain,(
% 4.94/0.99    ( ! [X8,X7,X9] : (k4_xboole_0(X7,k2_xboole_0(k2_xboole_0(X8,X7),X9)) = k4_xboole_0(k1_xboole_0,X9)) )),
% 4.94/0.99    inference(superposition,[],[f36,f204])).
% 4.94/0.99  fof(f3602,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 4.94/0.99    inference(forward_demodulation,[],[f3594,f36])).
% 4.94/0.99  fof(f3594,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 4.94/0.99    inference(backward_demodulation,[],[f46,f3592])).
% 4.94/0.99  fof(f3592,plain,(
% 4.94/0.99    ( ! [X47,X48,X46,X49] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X46,X47),X49),k2_xboole_0(X46,X48)) = k4_xboole_0(X49,k2_xboole_0(X46,X48))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f3497,f48])).
% 4.94/0.99  fof(f3497,plain,(
% 4.94/0.99    ( ! [X47,X48,X46,X49] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X46,X47),X49),k2_xboole_0(X46,X48)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X49,k2_xboole_0(X46,X48)))) )),
% 4.94/0.99    inference(superposition,[],[f39,f1422])).
% 4.94/0.99  fof(f1422,plain,(
% 4.94/0.99    ( ! [X24,X23,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X22,X23),k2_xboole_0(X22,X24))) )),
% 4.94/0.99    inference(forward_demodulation,[],[f1373,f147])).
% 4.94/0.99  fof(f1373,plain,(
% 4.94/0.99    ( ! [X24,X23,X22] : (k4_xboole_0(k4_xboole_0(X22,X23),k2_xboole_0(X22,X24)) = k4_xboole_0(k1_xboole_0,X24)) )),
% 4.94/0.99    inference(superposition,[],[f36,f56])).
% 4.94/0.99  fof(f46,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl2_1),
% 4.94/0.99    inference(avatar_component_clause,[],[f44])).
% 4.94/0.99  fof(f3601,plain,(
% 4.94/0.99    ~spl2_5 | spl2_4),
% 4.94/0.99    inference(avatar_split_clause,[],[f3596,f841,f3598])).
% 4.94/0.99  fof(f841,plain,(
% 4.94/0.99    spl2_4 <=> k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)))),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 4.94/0.99  fof(f3596,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k1_xboole_0) | spl2_4),
% 4.94/0.99    inference(forward_demodulation,[],[f3595,f1643])).
% 4.94/0.99  fof(f3595,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)))) | spl2_4),
% 4.94/0.99    inference(forward_demodulation,[],[f3593,f36])).
% 4.94/0.99  fof(f3593,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,sK1))) | spl2_4),
% 4.94/0.99    inference(backward_demodulation,[],[f843,f3592])).
% 4.94/0.99  fof(f843,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_4),
% 4.94/0.99    inference(avatar_component_clause,[],[f841])).
% 4.94/0.99  fof(f845,plain,(
% 4.94/0.99    ~spl2_4 | spl2_1),
% 4.94/0.99    inference(avatar_split_clause,[],[f839,f44,f841])).
% 4.94/0.99  fof(f839,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_1),
% 4.94/0.99    inference(superposition,[],[f46,f28])).
% 4.94/0.99  fof(f844,plain,(
% 4.94/0.99    ~spl2_4 | spl2_1),
% 4.94/0.99    inference(avatar_split_clause,[],[f838,f44,f841])).
% 4.94/0.99  fof(f838,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) | spl2_1),
% 4.94/0.99    inference(superposition,[],[f46,f28])).
% 4.94/0.99  fof(f71,plain,(
% 4.94/0.99    spl2_3 | ~spl2_2),
% 4.94/0.99    inference(avatar_split_clause,[],[f66,f62,f68])).
% 4.94/0.99  fof(f68,plain,(
% 4.94/0.99    spl2_3 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 4.94/0.99  fof(f62,plain,(
% 4.94/0.99    spl2_2 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 4.94/0.99    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 4.94/0.99  fof(f66,plain,(
% 4.94/0.99    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 4.94/0.99    inference(resolution,[],[f64,f35])).
% 4.94/0.99  fof(f64,plain,(
% 4.94/0.99    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 4.94/0.99    inference(avatar_component_clause,[],[f62])).
% 4.94/0.99  fof(f65,plain,(
% 4.94/0.99    spl2_2),
% 4.94/0.99    inference(avatar_split_clause,[],[f60,f62])).
% 4.94/0.99  fof(f60,plain,(
% 4.94/0.99    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 4.94/0.99    inference(superposition,[],[f58,f56])).
% 4.94/0.99  fof(f58,plain,(
% 4.94/0.99    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1))) )),
% 4.94/0.99    inference(superposition,[],[f27,f56])).
% 4.94/0.99  fof(f47,plain,(
% 4.94/0.99    ~spl2_1),
% 4.94/0.99    inference(avatar_split_clause,[],[f40,f44])).
% 4.94/0.99  fof(f40,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 4.94/0.99    inference(definition_unfolding,[],[f23,f32,f32])).
% 4.94/0.99  fof(f23,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 4.94/0.99    inference(cnf_transformation,[],[f21])).
% 4.94/0.99  fof(f21,plain,(
% 4.94/0.99    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 4.94/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 4.94/0.99  fof(f20,plain,(
% 4.94/0.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 4.94/0.99    introduced(choice_axiom,[])).
% 4.94/0.99  fof(f19,plain,(
% 4.94/0.99    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.94/0.99    inference(ennf_transformation,[],[f17])).
% 4.94/0.99  fof(f17,negated_conjecture,(
% 4.94/0.99    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.94/0.99    inference(negated_conjecture,[],[f16])).
% 4.94/0.99  fof(f16,conjecture,(
% 4.94/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.94/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.94/0.99  % SZS output end Proof for theBenchmark
% 4.94/0.99  % (16342)------------------------------
% 4.94/0.99  % (16342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/0.99  % (16342)Termination reason: Refutation
% 4.94/0.99  
% 4.94/0.99  % (16342)Memory used [KB]: 12920
% 4.94/0.99  % (16342)Time elapsed: 0.537 s
% 4.94/0.99  % (16342)------------------------------
% 4.94/0.99  % (16342)------------------------------
% 4.94/0.99  % (16331)Success in time 0.629 s
%------------------------------------------------------------------------------
