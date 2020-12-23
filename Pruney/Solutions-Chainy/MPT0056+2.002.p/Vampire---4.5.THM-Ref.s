%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:09 EST 2020

% Result     : Theorem 43.48s
% Output     : Refutation 43.48s
% Verified   : 
% Statistics : Number of formulae       :  121 (1749 expanded)
%              Number of leaves         :    8 ( 583 expanded)
%              Depth                    :   31
%              Number of atoms          :  126 (1755 expanded)
%              Number of equality atoms :  118 (1746 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116922,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f116899])).

fof(f116899,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f116898])).

fof(f116898,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f116510,f33680])).

fof(f33680,plain,(
    ! [X59,X57,X58] : k3_xboole_0(X59,k4_xboole_0(X57,X58)) = k3_xboole_0(X57,k4_xboole_0(X59,X58)) ),
    inference(superposition,[],[f32807,f12])).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32807,plain,(
    ! [X54,X56,X55] : k3_xboole_0(X56,k4_xboole_0(X54,X55)) = k3_xboole_0(k4_xboole_0(X56,X55),X54) ),
    inference(superposition,[],[f31639,f12])).

fof(f31639,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k3_xboole_0(k4_xboole_0(X7,X6),X5) ),
    inference(superposition,[],[f768,f500])).

fof(f500,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X2,X0),X1) ),
    inference(forward_demodulation,[],[f468,f125])).

fof(f125,plain,(
    ! [X10,X11,X9] : k3_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k2_xboole_0(X10,X11))) ),
    inference(superposition,[],[f13,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f13,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f468,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f125,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f768,plain,(
    ! [X14,X12,X13] : k3_xboole_0(k4_xboole_0(X12,X13),X14) = k3_xboole_0(k4_xboole_0(X14,X13),k4_xboole_0(X12,X13)) ),
    inference(superposition,[],[f500,f12])).

fof(f116510,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_1 ),
    inference(superposition,[],[f20,f116171])).

fof(f116171,plain,(
    ! [X47,X48,X46] : k4_xboole_0(k3_xboole_0(X46,X47),X48) = k3_xboole_0(X47,k4_xboole_0(X46,X48)) ),
    inference(forward_demodulation,[],[f116108,f101520])).

fof(f101520,plain,(
    ! [X422,X421,X423] : k3_xboole_0(X423,k4_xboole_0(X421,X422)) = k3_xboole_0(k4_xboole_0(X421,X422),k3_xboole_0(X421,X423)) ),
    inference(superposition,[],[f92520,f88])).

fof(f88,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4) ),
    inference(superposition,[],[f72,f23])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f22,f14])).

fof(f14,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f13,f13])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(k3_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f71,f12])).

fof(f71,plain,(
    ! [X14,X13] : k3_xboole_0(X14,X13) = k3_xboole_0(k3_xboole_0(X14,X13),X13) ),
    inference(forward_demodulation,[],[f70,f56])).

fof(f56,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f55,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f26,f13])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f13,f14])).

fof(f55,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f48,f12])).

fof(f48,plain,(
    ! [X6,X7] : k3_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f39,f27])).

fof(f39,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k3_xboole_0(X5,X6) ),
    inference(forward_demodulation,[],[f37,f13])).

fof(f37,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k4_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f13,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f14,f12])).

fof(f70,plain,(
    ! [X14,X13] : k3_xboole_0(k3_xboole_0(X14,X13),X13) = k3_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X14,X13)) ),
    inference(superposition,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f12])).

fof(f92520,plain,(
    ! [X17,X18,X16] : k3_xboole_0(X18,k3_xboole_0(X17,X16)) = k3_xboole_0(X16,k3_xboole_0(X18,X17)) ),
    inference(superposition,[],[f88190,f70094])).

fof(f70094,plain,(
    ! [X43,X44,X42] : k3_xboole_0(k3_xboole_0(X43,X42),X44) = k3_xboole_0(X44,k3_xboole_0(X42,X43)) ),
    inference(superposition,[],[f68726,f12])).

fof(f68726,plain,(
    ! [X182,X183,X181] : k3_xboole_0(k3_xboole_0(X181,X182),X183) = k3_xboole_0(k3_xboole_0(X182,X181),X183) ),
    inference(forward_demodulation,[],[f68725,f39])).

fof(f68725,plain,(
    ! [X182,X183,X181] : k3_xboole_0(k3_xboole_0(X181,X182),X183) = k3_xboole_0(k3_xboole_0(X182,k3_xboole_0(X181,X182)),X183) ),
    inference(forward_demodulation,[],[f68724,f12])).

fof(f68724,plain,(
    ! [X182,X183,X181] : k3_xboole_0(k3_xboole_0(X181,X182),X183) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X181,X182),X182),X183) ),
    inference(forward_demodulation,[],[f68723,f68697])).

fof(f68697,plain,(
    ! [X152,X151,X153] : k3_xboole_0(k3_xboole_0(X151,X152),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k3_xboole_0(X152,k4_xboole_0(X151,X152)))) ),
    inference(forward_demodulation,[],[f68696,f27])).

fof(f68696,plain,(
    ! [X152,X151,X153] : k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k3_xboole_0(X152,k4_xboole_0(X151,X152)))) = k3_xboole_0(k3_xboole_0(X151,k3_xboole_0(X151,X152)),X153) ),
    inference(forward_demodulation,[],[f68695,f12])).

fof(f68695,plain,(
    ! [X152,X151,X153] : k3_xboole_0(k3_xboole_0(k3_xboole_0(X151,X152),X151),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k3_xboole_0(X152,k4_xboole_0(X151,X152)))) ),
    inference(forward_demodulation,[],[f68694,f6562])).

fof(f6562,plain,(
    ! [X4,X5] : k3_xboole_0(X5,k4_xboole_0(X4,X5)) = k4_xboole_0(X5,k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f5508,f5501])).

fof(f5501,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f5500,f15])).

fof(f5500,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k3_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f5439,f12])).

fof(f5439,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[],[f133,f811])).

fof(f811,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k2_xboole_0(X5,X5)) ),
    inference(forward_demodulation,[],[f810,f54])).

fof(f54,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f53,f23])).

fof(f53,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f47,f12])).

fof(f47,plain,(
    ! [X4,X5] : k3_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f39,f23])).

fof(f810,plain,(
    ! [X4,X5] : k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k2_xboole_0(X5,X5)) ),
    inference(forward_demodulation,[],[f772,f16])).

fof(f772,plain,(
    ! [X4,X5] : k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(k4_xboole_0(X4,X5),X5) ),
    inference(superposition,[],[f23,f500])).

fof(f133,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) ),
    inference(forward_demodulation,[],[f119,f16])).

fof(f119,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5))) ),
    inference(superposition,[],[f16,f13])).

fof(f5508,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X18,X17)) = k4_xboole_0(X18,k2_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f5507,f15])).

fof(f5507,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,X18))) = k4_xboole_0(X18,k2_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f5506,f1980])).

fof(f1980,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f1979,f1318])).

fof(f1318,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f1317,f38])).

fof(f38,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k2_xboole_0(X5,X4)) ),
    inference(forward_demodulation,[],[f34,f16])).

fof(f34,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f24,f23])).

fof(f1317,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f1316,f1239])).

fof(f1239,plain,(
    ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),X2) = k3_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f1201,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f27])).

fof(f1201,plain,(
    ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f13,f834])).

fof(f834,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f807,f13])).

fof(f807,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(k4_xboole_0(X7,X8),X8) ),
    inference(forward_demodulation,[],[f766,f54])).

fof(f766,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X7,X8),X8) = k3_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f500,f23])).

fof(f1316,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f1282,f12])).

fof(f1282,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f13,f835])).

fof(f835,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f807,f14])).

fof(f1979,plain,(
    ! [X4,X3] : k3_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X4,X3)) = k4_xboole_0(k3_xboole_0(X3,X4),X3) ),
    inference(forward_demodulation,[],[f1920,f44])).

fof(f1920,plain,(
    ! [X4,X3] : k3_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X4,X3)) = k4_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f13,f1167])).

fof(f1167,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k4_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f834,f12])).

fof(f5506,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,X18))) = k3_xboole_0(k3_xboole_0(X18,X17),k4_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f5445,f12])).

fof(f5445,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,X18))) = k3_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X18,X17)) ),
    inference(superposition,[],[f133,f904])).

fof(f904,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k2_xboole_0(X5,k3_xboole_0(X5,X4))) ),
    inference(forward_demodulation,[],[f876,f24])).

fof(f876,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X5,X4)) = k4_xboole_0(X4,k2_xboole_0(X5,k3_xboole_0(X5,X4))) ),
    inference(superposition,[],[f811,f130])).

fof(f130,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X7,X6),X8)) = k4_xboole_0(X6,k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f117,f16])).

fof(f117,plain,(
    ! [X6,X8,X7] : k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X7,X6),X8)) = k4_xboole_0(k4_xboole_0(X6,X7),X8) ),
    inference(superposition,[],[f16,f24])).

fof(f68694,plain,(
    ! [X152,X151,X153] : k3_xboole_0(k3_xboole_0(k3_xboole_0(X151,X152),X151),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k4_xboole_0(X152,k2_xboole_0(X151,X152)))) ),
    inference(forward_demodulation,[],[f68429,f1990])).

fof(f1990,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f1318,f12])).

fof(f68429,plain,(
    ! [X152,X151,X153] : k3_xboole_0(k3_xboole_0(k3_xboole_0(X151,X152),X151),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k4_xboole_0(k3_xboole_0(X151,X152),X152))) ),
    inference(superposition,[],[f31745,f5358])).

fof(f5358,plain,(
    ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k3_xboole_0(X2,X3),X3) ),
    inference(superposition,[],[f68,f44])).

fof(f68,plain,(
    ! [X10,X9] : k4_xboole_0(k3_xboole_0(X10,X9),X9) = k4_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X10,X9)) ),
    inference(superposition,[],[f24,f40])).

fof(f31745,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f31744,f744])).

fof(f744,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f500,f13])).

fof(f31744,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k3_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f31484,f12])).

fof(f31484,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k3_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f768,f13])).

fof(f68723,plain,(
    ! [X182,X183,X181] : k3_xboole_0(k3_xboole_0(k3_xboole_0(X181,X182),X182),X183) = k3_xboole_0(k3_xboole_0(X181,X182),k4_xboole_0(X183,k3_xboole_0(X182,k4_xboole_0(X181,X182)))) ),
    inference(forward_demodulation,[],[f68439,f6562])).

fof(f68439,plain,(
    ! [X182,X183,X181] : k3_xboole_0(k3_xboole_0(k3_xboole_0(X181,X182),X182),X183) = k3_xboole_0(k3_xboole_0(X181,X182),k4_xboole_0(X183,k4_xboole_0(X182,k2_xboole_0(X181,X182)))) ),
    inference(superposition,[],[f31745,f1990])).

fof(f88190,plain,(
    ! [X6,X4,X5] : k3_xboole_0(X5,k3_xboole_0(X4,X6)) = k3_xboole_0(k3_xboole_0(X5,X6),X4) ),
    inference(forward_demodulation,[],[f88189,f67723])).

fof(f67723,plain,(
    ! [X39,X37,X38] : k3_xboole_0(X38,k3_xboole_0(X37,X39)) = k3_xboole_0(k3_xboole_0(X38,k3_xboole_0(X37,X39)),X37) ),
    inference(forward_demodulation,[],[f67641,f56])).

fof(f67641,plain,(
    ! [X39,X37,X38] : k3_xboole_0(k3_xboole_0(X38,k3_xboole_0(X37,X39)),X37) = k3_xboole_0(k3_xboole_0(X38,k3_xboole_0(X37,X39)),k3_xboole_0(X38,k3_xboole_0(X37,X39))) ),
    inference(superposition,[],[f39,f30158])).

fof(f30158,plain,(
    ! [X26,X27,X25] : k3_xboole_0(X27,k3_xboole_0(X25,X26)) = k3_xboole_0(X25,k3_xboole_0(X27,k3_xboole_0(X25,X26))) ),
    inference(superposition,[],[f656,f12])).

fof(f656,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),X4) = k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X2,X3),X4)) ),
    inference(superposition,[],[f325,f13])).

fof(f325,plain,(
    ! [X12,X10,X11] : k4_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k4_xboole_0(k3_xboole_0(X10,X11),X12)) ),
    inference(superposition,[],[f23,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(superposition,[],[f16,f13])).

fof(f88189,plain,(
    ! [X6,X4,X5] : k3_xboole_0(k3_xboole_0(X5,X6),X4) = k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X4,X6)),X4) ),
    inference(forward_demodulation,[],[f88043,f32712])).

fof(f32712,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f31639,f13])).

fof(f88043,plain,(
    ! [X6,X4,X5] : k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X4,X6)),X4) = k3_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X6)),X5) ),
    inference(superposition,[],[f32712,f75747])).

fof(f75747,plain,(
    ! [X54,X55,X53] : k4_xboole_0(X54,k4_xboole_0(X53,X55)) = k4_xboole_0(X54,k4_xboole_0(X53,k3_xboole_0(X54,X55))) ),
    inference(forward_demodulation,[],[f75746,f14])).

fof(f75746,plain,(
    ! [X54,X55,X53] : k4_xboole_0(X54,k4_xboole_0(X53,k3_xboole_0(X54,X55))) = k4_xboole_0(X54,k3_xboole_0(X54,k4_xboole_0(X53,X55))) ),
    inference(forward_demodulation,[],[f75524,f32807])).

fof(f75524,plain,(
    ! [X54,X55,X53] : k4_xboole_0(X54,k4_xboole_0(X53,k3_xboole_0(X54,X55))) = k4_xboole_0(X54,k3_xboole_0(k4_xboole_0(X54,X55),X53)) ),
    inference(superposition,[],[f24,f31747])).

fof(f31747,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k4_xboole_0(X6,X7),X8) = k3_xboole_0(k4_xboole_0(X8,k3_xboole_0(X6,X7)),X6) ),
    inference(forward_demodulation,[],[f31486,f745])).

fof(f745,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X5,k3_xboole_0(X3,X4))) ),
    inference(superposition,[],[f500,f14])).

fof(f31486,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k4_xboole_0(X8,k3_xboole_0(X6,X7)),X6) = k3_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X8,k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f768,f14])).

fof(f116108,plain,(
    ! [X47,X48,X46] : k4_xboole_0(k3_xboole_0(X46,X47),X48) = k3_xboole_0(k4_xboole_0(X46,X48),k3_xboole_0(X46,X47)) ),
    inference(superposition,[],[f329,f31639])).

fof(f329,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k3_xboole_0(X22,X23),X24) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X22,X23),X24),X22) ),
    inference(superposition,[],[f88,f115])).

fof(f20,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f18,plain,
    ( spl3_1
  <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f21,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f11,f18])).

fof(f11,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:50:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.43  % (6649)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (6640)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.45  % (6639)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (6653)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (6642)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (6644)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (6647)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (6650)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (6650)Refutation not found, incomplete strategy% (6650)------------------------------
% 0.20/0.48  % (6650)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6650)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (6650)Memory used [KB]: 10490
% 0.20/0.48  % (6650)Time elapsed: 0.071 s
% 0.20/0.48  % (6650)------------------------------
% 0.20/0.48  % (6650)------------------------------
% 0.20/0.48  % (6648)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (6645)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (6643)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (6656)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (6652)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (6651)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (6646)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (6654)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (6641)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (6655)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.36/1.02  % (6643)Time limit reached!
% 5.36/1.02  % (6643)------------------------------
% 5.36/1.02  % (6643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.36/1.02  % (6643)Termination reason: Time limit
% 5.36/1.02  
% 5.36/1.02  % (6643)Memory used [KB]: 22387
% 5.36/1.02  % (6643)Time elapsed: 0.612 s
% 5.36/1.02  % (6643)------------------------------
% 5.36/1.02  % (6643)------------------------------
% 12.38/1.91  % (6644)Time limit reached!
% 12.38/1.91  % (6644)------------------------------
% 12.38/1.91  % (6644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.38/1.91  % (6644)Termination reason: Time limit
% 12.38/1.91  % (6644)Termination phase: Saturation
% 12.38/1.91  
% 12.38/1.91  % (6644)Memory used [KB]: 50404
% 12.38/1.91  % (6644)Time elapsed: 1.500 s
% 12.38/1.91  % (6644)------------------------------
% 12.38/1.91  % (6644)------------------------------
% 12.38/1.96  % (6645)Time limit reached!
% 12.38/1.96  % (6645)------------------------------
% 12.38/1.96  % (6645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.38/1.96  % (6645)Termination reason: Time limit
% 12.38/1.96  
% 12.38/1.96  % (6645)Memory used [KB]: 43368
% 12.38/1.96  % (6645)Time elapsed: 1.533 s
% 12.38/1.96  % (6645)------------------------------
% 12.38/1.96  % (6645)------------------------------
% 14.82/2.22  % (6641)Time limit reached!
% 14.82/2.22  % (6641)------------------------------
% 14.82/2.22  % (6641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.82/2.24  % (6641)Termination reason: Time limit
% 14.82/2.24  
% 14.82/2.24  % (6641)Memory used [KB]: 43496
% 14.82/2.24  % (6641)Time elapsed: 1.809 s
% 14.82/2.24  % (6641)------------------------------
% 14.82/2.24  % (6641)------------------------------
% 17.83/2.63  % (6651)Time limit reached!
% 17.83/2.63  % (6651)------------------------------
% 17.83/2.63  % (6651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.83/2.63  % (6651)Termination reason: Time limit
% 17.83/2.63  % (6651)Termination phase: Saturation
% 17.83/2.63  
% 17.83/2.63  % (6651)Memory used [KB]: 45798
% 17.83/2.63  % (6651)Time elapsed: 2.200 s
% 17.83/2.63  % (6651)------------------------------
% 17.83/2.63  % (6651)------------------------------
% 43.48/5.86  % (6639)Refutation found. Thanks to Tanya!
% 43.48/5.86  % SZS status Theorem for theBenchmark
% 43.48/5.86  % SZS output start Proof for theBenchmark
% 43.48/5.86  fof(f116922,plain,(
% 43.48/5.86    $false),
% 43.48/5.86    inference(avatar_sat_refutation,[],[f21,f116899])).
% 43.48/5.86  fof(f116899,plain,(
% 43.48/5.86    spl3_1),
% 43.48/5.86    inference(avatar_contradiction_clause,[],[f116898])).
% 43.48/5.86  fof(f116898,plain,(
% 43.48/5.86    $false | spl3_1),
% 43.48/5.86    inference(subsumption_resolution,[],[f116510,f33680])).
% 43.48/5.86  fof(f33680,plain,(
% 43.48/5.86    ( ! [X59,X57,X58] : (k3_xboole_0(X59,k4_xboole_0(X57,X58)) = k3_xboole_0(X57,k4_xboole_0(X59,X58))) )),
% 43.48/5.86    inference(superposition,[],[f32807,f12])).
% 43.48/5.86  fof(f12,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 43.48/5.86    inference(cnf_transformation,[],[f1])).
% 43.48/5.86  fof(f1,axiom,(
% 43.48/5.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 43.48/5.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 43.48/5.86  fof(f32807,plain,(
% 43.48/5.86    ( ! [X54,X56,X55] : (k3_xboole_0(X56,k4_xboole_0(X54,X55)) = k3_xboole_0(k4_xboole_0(X56,X55),X54)) )),
% 43.48/5.86    inference(superposition,[],[f31639,f12])).
% 43.48/5.86  fof(f31639,plain,(
% 43.48/5.86    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k3_xboole_0(k4_xboole_0(X7,X6),X5)) )),
% 43.48/5.86    inference(superposition,[],[f768,f500])).
% 43.48/5.86  fof(f500,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k3_xboole_0(k4_xboole_0(X2,X0),X1)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f468,f125])).
% 43.48/5.86  fof(f125,plain,(
% 43.48/5.86    ( ! [X10,X11,X9] : (k3_xboole_0(k4_xboole_0(X9,X10),X11) = k4_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,k2_xboole_0(X10,X11)))) )),
% 43.48/5.86    inference(superposition,[],[f13,f16])).
% 43.48/5.86  fof(f16,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 43.48/5.86    inference(cnf_transformation,[],[f3])).
% 43.48/5.86  fof(f3,axiom,(
% 43.48/5.86    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 43.48/5.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 43.48/5.86  fof(f13,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(cnf_transformation,[],[f5])).
% 43.48/5.86  fof(f5,axiom,(
% 43.48/5.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 43.48/5.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 43.48/5.86  fof(f468,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X1,X0)) = k4_xboole_0(k4_xboole_0(X2,X0),k4_xboole_0(X2,k2_xboole_0(X0,X1)))) )),
% 43.48/5.86    inference(superposition,[],[f125,f15])).
% 43.48/5.86  fof(f15,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 43.48/5.86    inference(cnf_transformation,[],[f2])).
% 43.48/5.86  fof(f2,axiom,(
% 43.48/5.86    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 43.48/5.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 43.48/5.86  fof(f768,plain,(
% 43.48/5.86    ( ! [X14,X12,X13] : (k3_xboole_0(k4_xboole_0(X12,X13),X14) = k3_xboole_0(k4_xboole_0(X14,X13),k4_xboole_0(X12,X13))) )),
% 43.48/5.86    inference(superposition,[],[f500,f12])).
% 43.48/5.86  fof(f116510,plain,(
% 43.48/5.86    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_1),
% 43.48/5.86    inference(superposition,[],[f20,f116171])).
% 43.48/5.86  fof(f116171,plain,(
% 43.48/5.86    ( ! [X47,X48,X46] : (k4_xboole_0(k3_xboole_0(X46,X47),X48) = k3_xboole_0(X47,k4_xboole_0(X46,X48))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f116108,f101520])).
% 43.48/5.86  fof(f101520,plain,(
% 43.48/5.86    ( ! [X422,X421,X423] : (k3_xboole_0(X423,k4_xboole_0(X421,X422)) = k3_xboole_0(k4_xboole_0(X421,X422),k3_xboole_0(X421,X423))) )),
% 43.48/5.86    inference(superposition,[],[f92520,f88])).
% 43.48/5.86  fof(f88,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),X4)) )),
% 43.48/5.86    inference(superposition,[],[f72,f23])).
% 43.48/5.86  fof(f23,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f22,f14])).
% 43.48/5.86  fof(f14,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(cnf_transformation,[],[f4])).
% 43.48/5.86  fof(f4,axiom,(
% 43.48/5.86    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.48/5.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 43.48/5.86  fof(f22,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(superposition,[],[f13,f13])).
% 43.48/5.86  fof(f72,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(k3_xboole_0(X1,X0),X1)) )),
% 43.48/5.86    inference(superposition,[],[f71,f12])).
% 43.48/5.86  fof(f71,plain,(
% 43.48/5.86    ( ! [X14,X13] : (k3_xboole_0(X14,X13) = k3_xboole_0(k3_xboole_0(X14,X13),X13)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f70,f56])).
% 43.48/5.86  fof(f56,plain,(
% 43.48/5.86    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f55,f27])).
% 43.48/5.86  fof(f27,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f26,f13])).
% 43.48/5.86  fof(f26,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(superposition,[],[f13,f14])).
% 43.48/5.86  fof(f55,plain,(
% 43.48/5.86    ( ! [X6,X7] : (k3_xboole_0(X6,k3_xboole_0(X6,X7)) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f48,f12])).
% 43.48/5.86  fof(f48,plain,(
% 43.48/5.86    ( ! [X6,X7] : (k3_xboole_0(k3_xboole_0(X6,X7),X6) = k3_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7))) )),
% 43.48/5.86    inference(superposition,[],[f39,f27])).
% 43.48/5.86  fof(f39,plain,(
% 43.48/5.86    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k3_xboole_0(X5,X6)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f37,f13])).
% 43.48/5.86  fof(f37,plain,(
% 43.48/5.86    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X6,X5)) = k4_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 43.48/5.86    inference(superposition,[],[f13,f24])).
% 43.48/5.86  fof(f24,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 43.48/5.86    inference(superposition,[],[f14,f12])).
% 43.48/5.86  fof(f70,plain,(
% 43.48/5.86    ( ! [X14,X13] : (k3_xboole_0(k3_xboole_0(X14,X13),X13) = k3_xboole_0(k3_xboole_0(X14,X13),k3_xboole_0(X14,X13))) )),
% 43.48/5.86    inference(superposition,[],[f39,f40])).
% 43.48/5.86  fof(f40,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 43.48/5.86    inference(superposition,[],[f27,f12])).
% 43.48/5.86  fof(f92520,plain,(
% 43.48/5.86    ( ! [X17,X18,X16] : (k3_xboole_0(X18,k3_xboole_0(X17,X16)) = k3_xboole_0(X16,k3_xboole_0(X18,X17))) )),
% 43.48/5.86    inference(superposition,[],[f88190,f70094])).
% 43.48/5.86  fof(f70094,plain,(
% 43.48/5.86    ( ! [X43,X44,X42] : (k3_xboole_0(k3_xboole_0(X43,X42),X44) = k3_xboole_0(X44,k3_xboole_0(X42,X43))) )),
% 43.48/5.86    inference(superposition,[],[f68726,f12])).
% 43.48/5.86  fof(f68726,plain,(
% 43.48/5.86    ( ! [X182,X183,X181] : (k3_xboole_0(k3_xboole_0(X181,X182),X183) = k3_xboole_0(k3_xboole_0(X182,X181),X183)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68725,f39])).
% 43.48/5.86  fof(f68725,plain,(
% 43.48/5.86    ( ! [X182,X183,X181] : (k3_xboole_0(k3_xboole_0(X181,X182),X183) = k3_xboole_0(k3_xboole_0(X182,k3_xboole_0(X181,X182)),X183)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68724,f12])).
% 43.48/5.86  fof(f68724,plain,(
% 43.48/5.86    ( ! [X182,X183,X181] : (k3_xboole_0(k3_xboole_0(X181,X182),X183) = k3_xboole_0(k3_xboole_0(k3_xboole_0(X181,X182),X182),X183)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68723,f68697])).
% 43.48/5.86  fof(f68697,plain,(
% 43.48/5.86    ( ! [X152,X151,X153] : (k3_xboole_0(k3_xboole_0(X151,X152),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k3_xboole_0(X152,k4_xboole_0(X151,X152))))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68696,f27])).
% 43.48/5.86  fof(f68696,plain,(
% 43.48/5.86    ( ! [X152,X151,X153] : (k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k3_xboole_0(X152,k4_xboole_0(X151,X152)))) = k3_xboole_0(k3_xboole_0(X151,k3_xboole_0(X151,X152)),X153)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68695,f12])).
% 43.48/5.86  fof(f68695,plain,(
% 43.48/5.86    ( ! [X152,X151,X153] : (k3_xboole_0(k3_xboole_0(k3_xboole_0(X151,X152),X151),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k3_xboole_0(X152,k4_xboole_0(X151,X152))))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68694,f6562])).
% 43.48/5.86  fof(f6562,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k3_xboole_0(X5,k4_xboole_0(X4,X5)) = k4_xboole_0(X5,k2_xboole_0(X4,X5))) )),
% 43.48/5.86    inference(superposition,[],[f5508,f5501])).
% 43.48/5.86  fof(f5501,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k3_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f5500,f15])).
% 43.48/5.86  fof(f5500,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k3_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f5439,f12])).
% 43.48/5.86  fof(f5439,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 43.48/5.86    inference(superposition,[],[f133,f811])).
% 43.48/5.86  fof(f811,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k2_xboole_0(X5,X5))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f810,f54])).
% 43.48/5.86  fof(f54,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f53,f23])).
% 43.48/5.86  fof(f53,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k3_xboole_0(X4,k4_xboole_0(X4,X5)) = k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f47,f12])).
% 43.48/5.86  fof(f47,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X5),X4) = k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 43.48/5.86    inference(superposition,[],[f39,f23])).
% 43.48/5.86  fof(f810,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k2_xboole_0(X5,X5))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f772,f16])).
% 43.48/5.86  fof(f772,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k3_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(k4_xboole_0(X4,X5),X5)) )),
% 43.48/5.86    inference(superposition,[],[f23,f500])).
% 43.48/5.86  fof(f133,plain,(
% 43.48/5.86    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,k2_xboole_0(X4,X5))))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f119,f16])).
% 43.48/5.86  fof(f119,plain,(
% 43.48/5.86    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,X4),X5)))) )),
% 43.48/5.86    inference(superposition,[],[f16,f13])).
% 43.48/5.86  fof(f5508,plain,(
% 43.48/5.86    ( ! [X17,X18] : (k4_xboole_0(X17,k2_xboole_0(X18,X17)) = k4_xboole_0(X18,k2_xboole_0(X17,X18))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f5507,f15])).
% 43.48/5.86  fof(f5507,plain,(
% 43.48/5.86    ( ! [X17,X18] : (k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,X18))) = k4_xboole_0(X18,k2_xboole_0(X17,X18))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f5506,f1980])).
% 43.48/5.86  fof(f1980,plain,(
% 43.48/5.86    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,X3)) = k3_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X4,X3))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f1979,f1318])).
% 43.48/5.86  fof(f1318,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X2)) = k4_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f1317,f38])).
% 43.48/5.86  fof(f38,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k2_xboole_0(X5,X4))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f34,f16])).
% 43.48/5.86  fof(f34,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X4,X5),X4) = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5))) )),
% 43.48/5.86    inference(superposition,[],[f24,f23])).
% 43.48/5.86  fof(f1317,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f1316,f1239])).
% 43.48/5.86  fof(f1239,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),X2) = k3_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f1201,f44])).
% 43.48/5.86  fof(f44,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X0) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(superposition,[],[f24,f27])).
% 43.48/5.86  fof(f1201,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 43.48/5.86    inference(superposition,[],[f13,f834])).
% 43.48/5.86  fof(f834,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(superposition,[],[f807,f13])).
% 43.48/5.86  fof(f807,plain,(
% 43.48/5.86    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f766,f54])).
% 43.48/5.86  fof(f766,plain,(
% 43.48/5.86    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X7,X8),X8) = k3_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,X8))) )),
% 43.48/5.86    inference(superposition,[],[f500,f23])).
% 43.48/5.86  fof(f1316,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k3_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f1282,f12])).
% 43.48/5.86  fof(f1282,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k3_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 43.48/5.86    inference(superposition,[],[f13,f835])).
% 43.48/5.86  fof(f835,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 43.48/5.86    inference(superposition,[],[f807,f14])).
% 43.48/5.86  fof(f1979,plain,(
% 43.48/5.86    ( ! [X4,X3] : (k3_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X4,X3)) = k4_xboole_0(k3_xboole_0(X3,X4),X3)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f1920,f44])).
% 43.48/5.86  fof(f1920,plain,(
% 43.48/5.86    ( ! [X4,X3] : (k3_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X4,X3)) = k4_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,X4))) )),
% 43.48/5.86    inference(superposition,[],[f13,f1167])).
% 43.48/5.86  fof(f1167,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k4_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1))) )),
% 43.48/5.86    inference(superposition,[],[f834,f12])).
% 43.48/5.86  fof(f5506,plain,(
% 43.48/5.86    ( ! [X17,X18] : (k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,X18))) = k3_xboole_0(k3_xboole_0(X18,X17),k4_xboole_0(X17,X18))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f5445,f12])).
% 43.48/5.86  fof(f5445,plain,(
% 43.48/5.86    ( ! [X17,X18] : (k4_xboole_0(X17,k2_xboole_0(X18,k4_xboole_0(X17,X18))) = k3_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X18,X17))) )),
% 43.48/5.86    inference(superposition,[],[f133,f904])).
% 43.48/5.86  fof(f904,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k2_xboole_0(X5,k3_xboole_0(X5,X4)))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f876,f24])).
% 43.48/5.86  fof(f876,plain,(
% 43.48/5.86    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X5,X4)) = k4_xboole_0(X4,k2_xboole_0(X5,k3_xboole_0(X5,X4)))) )),
% 43.48/5.86    inference(superposition,[],[f811,f130])).
% 43.48/5.86  fof(f130,plain,(
% 43.48/5.86    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X7,X6),X8)) = k4_xboole_0(X6,k2_xboole_0(X7,X8))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f117,f16])).
% 43.48/5.86  fof(f117,plain,(
% 43.48/5.86    ( ! [X6,X8,X7] : (k4_xboole_0(X6,k2_xboole_0(k3_xboole_0(X7,X6),X8)) = k4_xboole_0(k4_xboole_0(X6,X7),X8)) )),
% 43.48/5.86    inference(superposition,[],[f16,f24])).
% 43.48/5.86  fof(f68694,plain,(
% 43.48/5.86    ( ! [X152,X151,X153] : (k3_xboole_0(k3_xboole_0(k3_xboole_0(X151,X152),X151),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k4_xboole_0(X152,k2_xboole_0(X151,X152))))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68429,f1990])).
% 43.48/5.86  fof(f1990,plain,(
% 43.48/5.86    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 43.48/5.86    inference(superposition,[],[f1318,f12])).
% 43.48/5.86  fof(f68429,plain,(
% 43.48/5.86    ( ! [X152,X151,X153] : (k3_xboole_0(k3_xboole_0(k3_xboole_0(X151,X152),X151),X153) = k3_xboole_0(k3_xboole_0(X151,X152),k4_xboole_0(X153,k4_xboole_0(k3_xboole_0(X151,X152),X152)))) )),
% 43.48/5.86    inference(superposition,[],[f31745,f5358])).
% 43.48/5.86  fof(f5358,plain,(
% 43.48/5.86    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k3_xboole_0(X2,X3),X3)) )),
% 43.48/5.86    inference(superposition,[],[f68,f44])).
% 43.48/5.86  fof(f68,plain,(
% 43.48/5.86    ( ! [X10,X9] : (k4_xboole_0(k3_xboole_0(X10,X9),X9) = k4_xboole_0(k3_xboole_0(X10,X9),k3_xboole_0(X10,X9))) )),
% 43.48/5.86    inference(superposition,[],[f24,f40])).
% 43.48/5.86  fof(f31745,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f31744,f744])).
% 43.48/5.86  fof(f744,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1)))) )),
% 43.48/5.86    inference(superposition,[],[f500,f13])).
% 43.48/5.86  fof(f31744,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k3_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,X1)))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f31484,f12])).
% 43.48/5.86  fof(f31484,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k3_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X0)) )),
% 43.48/5.86    inference(superposition,[],[f768,f13])).
% 43.48/5.86  fof(f68723,plain,(
% 43.48/5.86    ( ! [X182,X183,X181] : (k3_xboole_0(k3_xboole_0(k3_xboole_0(X181,X182),X182),X183) = k3_xboole_0(k3_xboole_0(X181,X182),k4_xboole_0(X183,k3_xboole_0(X182,k4_xboole_0(X181,X182))))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f68439,f6562])).
% 43.48/5.86  fof(f68439,plain,(
% 43.48/5.86    ( ! [X182,X183,X181] : (k3_xboole_0(k3_xboole_0(k3_xboole_0(X181,X182),X182),X183) = k3_xboole_0(k3_xboole_0(X181,X182),k4_xboole_0(X183,k4_xboole_0(X182,k2_xboole_0(X181,X182))))) )),
% 43.48/5.86    inference(superposition,[],[f31745,f1990])).
% 43.48/5.86  fof(f88190,plain,(
% 43.48/5.86    ( ! [X6,X4,X5] : (k3_xboole_0(X5,k3_xboole_0(X4,X6)) = k3_xboole_0(k3_xboole_0(X5,X6),X4)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f88189,f67723])).
% 43.48/5.86  fof(f67723,plain,(
% 43.48/5.86    ( ! [X39,X37,X38] : (k3_xboole_0(X38,k3_xboole_0(X37,X39)) = k3_xboole_0(k3_xboole_0(X38,k3_xboole_0(X37,X39)),X37)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f67641,f56])).
% 43.48/5.86  fof(f67641,plain,(
% 43.48/5.86    ( ! [X39,X37,X38] : (k3_xboole_0(k3_xboole_0(X38,k3_xboole_0(X37,X39)),X37) = k3_xboole_0(k3_xboole_0(X38,k3_xboole_0(X37,X39)),k3_xboole_0(X38,k3_xboole_0(X37,X39)))) )),
% 43.48/5.86    inference(superposition,[],[f39,f30158])).
% 43.48/5.86  fof(f30158,plain,(
% 43.48/5.86    ( ! [X26,X27,X25] : (k3_xboole_0(X27,k3_xboole_0(X25,X26)) = k3_xboole_0(X25,k3_xboole_0(X27,k3_xboole_0(X25,X26)))) )),
% 43.48/5.86    inference(superposition,[],[f656,f12])).
% 43.48/5.86  fof(f656,plain,(
% 43.48/5.86    ( ! [X4,X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),X4) = k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(X2,X3),X4))) )),
% 43.48/5.86    inference(superposition,[],[f325,f13])).
% 43.48/5.86  fof(f325,plain,(
% 43.48/5.86    ( ! [X12,X10,X11] : (k4_xboole_0(k3_xboole_0(X10,X11),X12) = k3_xboole_0(X10,k4_xboole_0(k3_xboole_0(X10,X11),X12))) )),
% 43.48/5.86    inference(superposition,[],[f23,f115])).
% 43.48/5.86  fof(f115,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 43.48/5.86    inference(superposition,[],[f16,f13])).
% 43.48/5.86  fof(f88189,plain,(
% 43.48/5.86    ( ! [X6,X4,X5] : (k3_xboole_0(k3_xboole_0(X5,X6),X4) = k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X4,X6)),X4)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f88043,f32712])).
% 43.48/5.86  fof(f32712,plain,(
% 43.48/5.86    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k4_xboole_0(X2,k4_xboole_0(X0,X1)),X0)) )),
% 43.48/5.86    inference(superposition,[],[f31639,f13])).
% 43.48/5.86  fof(f88043,plain,(
% 43.48/5.86    ( ! [X6,X4,X5] : (k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X4,X6)),X4) = k3_xboole_0(k4_xboole_0(X4,k4_xboole_0(X5,X6)),X5)) )),
% 43.48/5.86    inference(superposition,[],[f32712,f75747])).
% 43.48/5.86  fof(f75747,plain,(
% 43.48/5.86    ( ! [X54,X55,X53] : (k4_xboole_0(X54,k4_xboole_0(X53,X55)) = k4_xboole_0(X54,k4_xboole_0(X53,k3_xboole_0(X54,X55)))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f75746,f14])).
% 43.48/5.86  fof(f75746,plain,(
% 43.48/5.86    ( ! [X54,X55,X53] : (k4_xboole_0(X54,k4_xboole_0(X53,k3_xboole_0(X54,X55))) = k4_xboole_0(X54,k3_xboole_0(X54,k4_xboole_0(X53,X55)))) )),
% 43.48/5.86    inference(forward_demodulation,[],[f75524,f32807])).
% 43.48/5.86  fof(f75524,plain,(
% 43.48/5.86    ( ! [X54,X55,X53] : (k4_xboole_0(X54,k4_xboole_0(X53,k3_xboole_0(X54,X55))) = k4_xboole_0(X54,k3_xboole_0(k4_xboole_0(X54,X55),X53))) )),
% 43.48/5.86    inference(superposition,[],[f24,f31747])).
% 43.48/5.86  fof(f31747,plain,(
% 43.48/5.86    ( ! [X6,X8,X7] : (k3_xboole_0(k4_xboole_0(X6,X7),X8) = k3_xboole_0(k4_xboole_0(X8,k3_xboole_0(X6,X7)),X6)) )),
% 43.48/5.86    inference(forward_demodulation,[],[f31486,f745])).
% 43.48/5.86  fof(f745,plain,(
% 43.48/5.86    ( ! [X4,X5,X3] : (k3_xboole_0(k4_xboole_0(X3,X4),X5) = k3_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X5,k3_xboole_0(X3,X4)))) )),
% 43.48/5.86    inference(superposition,[],[f500,f14])).
% 43.48/5.86  fof(f31486,plain,(
% 43.48/5.86    ( ! [X6,X8,X7] : (k3_xboole_0(k4_xboole_0(X8,k3_xboole_0(X6,X7)),X6) = k3_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X8,k3_xboole_0(X6,X7)))) )),
% 43.48/5.86    inference(superposition,[],[f768,f14])).
% 43.48/5.86  fof(f116108,plain,(
% 43.48/5.86    ( ! [X47,X48,X46] : (k4_xboole_0(k3_xboole_0(X46,X47),X48) = k3_xboole_0(k4_xboole_0(X46,X48),k3_xboole_0(X46,X47))) )),
% 43.48/5.86    inference(superposition,[],[f329,f31639])).
% 43.48/5.86  fof(f329,plain,(
% 43.48/5.86    ( ! [X24,X23,X22] : (k4_xboole_0(k3_xboole_0(X22,X23),X24) = k3_xboole_0(k4_xboole_0(k3_xboole_0(X22,X23),X24),X22)) )),
% 43.48/5.86    inference(superposition,[],[f88,f115])).
% 43.48/5.86  fof(f20,plain,(
% 43.48/5.86    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) | spl3_1),
% 43.48/5.86    inference(avatar_component_clause,[],[f18])).
% 43.48/5.86  fof(f18,plain,(
% 43.48/5.86    spl3_1 <=> k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 43.48/5.86    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 43.48/5.86  fof(f21,plain,(
% 43.48/5.86    ~spl3_1),
% 43.48/5.86    inference(avatar_split_clause,[],[f11,f18])).
% 43.48/5.86  fof(f11,plain,(
% 43.48/5.86    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 43.48/5.86    inference(cnf_transformation,[],[f10])).
% 43.48/5.86  fof(f10,plain,(
% 43.48/5.86    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 43.48/5.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 43.48/5.86  fof(f9,plain,(
% 43.48/5.86    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 43.48/5.86    introduced(choice_axiom,[])).
% 43.48/5.86  fof(f8,plain,(
% 43.48/5.86    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.48/5.86    inference(ennf_transformation,[],[f7])).
% 43.48/5.86  fof(f7,negated_conjecture,(
% 43.48/5.86    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.48/5.86    inference(negated_conjecture,[],[f6])).
% 43.48/5.86  fof(f6,conjecture,(
% 43.48/5.86    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 43.48/5.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 43.48/5.86  % SZS output end Proof for theBenchmark
% 43.48/5.86  % (6639)------------------------------
% 43.48/5.86  % (6639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 43.48/5.86  % (6639)Termination reason: Refutation
% 43.48/5.86  
% 43.48/5.86  % (6639)Memory used [KB]: 95307
% 43.48/5.86  % (6639)Time elapsed: 5.441 s
% 43.48/5.86  % (6639)------------------------------
% 43.48/5.86  % (6639)------------------------------
% 44.16/5.89  % (6638)Success in time 5.535 s
%------------------------------------------------------------------------------
