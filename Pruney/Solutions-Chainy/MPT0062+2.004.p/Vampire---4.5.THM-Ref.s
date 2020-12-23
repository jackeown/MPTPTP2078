%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:15 EST 2020

% Result     : Theorem 22.30s
% Output     : Refutation 22.30s
% Verified   : 
% Statistics : Number of formulae       :  213 (25329 expanded)
%              Number of leaves         :   10 (8536 expanded)
%              Depth                    :   55
%              Number of atoms          :  217 (25334 expanded)
%              Number of equality atoms :  210 (25326 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f45439,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f45318])).

fof(f45318,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f45316])).

fof(f45316,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f27,f45314])).

fof(f45314,plain,(
    ! [X54,X52,X53] : k4_xboole_0(k2_xboole_0(X54,X52),k4_xboole_0(X53,k4_xboole_0(X53,X52))) = k2_xboole_0(k4_xboole_0(X54,X52),k4_xboole_0(X52,X53)) ),
    inference(backward_demodulation,[],[f34149,f45313])).

fof(f45313,plain,(
    ! [X61,X59,X60] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X59,X59),X60),k4_xboole_0(X61,k4_xboole_0(X60,k4_xboole_0(X60,X59)))) = k2_xboole_0(k4_xboole_0(X61,X59),k4_xboole_0(X59,X60)) ),
    inference(forward_demodulation,[],[f44864,f19052])).

fof(f19052,plain,(
    ! [X23,X21,X22] : k2_xboole_0(X23,k4_xboole_0(X21,X22)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X21,X21),X22),X23) ),
    inference(superposition,[],[f18767,f55])).

fof(f55,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4) ),
    inference(superposition,[],[f20,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f18767,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k2_xboole_0(X5,X5),X4) ),
    inference(superposition,[],[f18494,f171])).

fof(f171,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k2_xboole_0(X8,X7)) = k2_xboole_0(k2_xboole_0(X7,X8),X6) ),
    inference(superposition,[],[f147,f15])).

fof(f147,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X3,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f90,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f90,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X1,X0),X2)) ),
    inference(superposition,[],[f17,f75])).

fof(f75,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X5),X4) = k4_xboole_0(k2_xboole_0(X5,X3),X4) ),
    inference(superposition,[],[f55,f20])).

fof(f18494,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f18168,f90])).

fof(f18168,plain,(
    ! [X26,X25] : k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X25,X25),X26)) ),
    inference(forward_demodulation,[],[f18167,f10958])).

fof(f10958,plain,(
    ! [X10,X9] : k4_xboole_0(k2_xboole_0(X9,X9),X10) = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X10,X9))) ),
    inference(backward_demodulation,[],[f5405,f10945])).

fof(f10945,plain,(
    ! [X109,X110] : k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(X109,k4_xboole_0(X109,X110)) ),
    inference(backward_demodulation,[],[f8209,f10822])).

fof(f10822,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k2_xboole_0(X20,X19))) ),
    inference(backward_demodulation,[],[f6349,f10774])).

fof(f10774,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k2_xboole_0(X16,X17)) = k4_xboole_0(X17,k2_xboole_0(X17,k4_xboole_0(X17,X16))) ),
    inference(forward_demodulation,[],[f10564,f5351])).

fof(f5351,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X1,X1))) ),
    inference(backward_demodulation,[],[f4360,f5302])).

fof(f5302,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X20,X20)) = k4_xboole_0(X19,k4_xboole_0(X20,X20)) ),
    inference(backward_demodulation,[],[f2050,f5301])).

fof(f5301,plain,(
    ! [X66,X65] : k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(X65,k4_xboole_0(X66,X66)) ),
    inference(forward_demodulation,[],[f5300,f1518])).

fof(f1518,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) ),
    inference(superposition,[],[f1509,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1509,plain,(
    ! [X26,X27] : k2_xboole_0(X27,X26) = k2_xboole_0(k4_xboole_0(X26,X27),X27) ),
    inference(forward_demodulation,[],[f1459,f1508])).

fof(f1508,plain,(
    ! [X24,X25] : k2_xboole_0(X25,X24) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X24,X25)),X25)) ),
    inference(forward_demodulation,[],[f1507,f17])).

fof(f1507,plain,(
    ! [X24,X25] : k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X24,X25)),X25)) = k2_xboole_0(X25,k4_xboole_0(X24,X25)) ),
    inference(forward_demodulation,[],[f1506,f15])).

fof(f1506,plain,(
    ! [X24,X25] : k2_xboole_0(k4_xboole_0(X24,X25),X25) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X24,X25)),X25)) ),
    inference(forward_demodulation,[],[f1458,f75])).

fof(f1458,plain,(
    ! [X24,X25] : k2_xboole_0(k4_xboole_0(X24,X25),X25) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X24,X25),X24),X25)) ),
    inference(superposition,[],[f1105,f55])).

fof(f1105,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f1104,f17])).

fof(f1104,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,k4_xboole_0(X6,X7))) ),
    inference(forward_demodulation,[],[f1073,f15])).

fof(f1073,plain,(
    ! [X6,X7] : k2_xboole_0(k4_xboole_0(X7,X6),X6) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,k4_xboole_0(X6,X7))) ),
    inference(superposition,[],[f764,f131])).

fof(f131,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f122,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    inference(superposition,[],[f30,f15])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f17,f18])).

fof(f122,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f59,f17])).

fof(f764,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f763,f17])).

fof(f763,plain,(
    ! [X8,X7] : k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k2_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f709,f15])).

fof(f709,plain,(
    ! [X8,X7] : k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X7,X8),X7)) ),
    inference(superposition,[],[f131,f640])).

fof(f640,plain,(
    ! [X14,X13] : k4_xboole_0(X13,k4_xboole_0(X14,X14)) = k2_xboole_0(k4_xboole_0(X13,X14),X13) ),
    inference(superposition,[],[f23,f17])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f19,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1459,plain,(
    ! [X26,X27] : k2_xboole_0(k4_xboole_0(X26,X27),X27) = k2_xboole_0(k4_xboole_0(X27,k4_xboole_0(X26,X27)),k4_xboole_0(k2_xboole_0(X26,k4_xboole_0(X26,X27)),X27)) ),
    inference(superposition,[],[f1105,f20])).

fof(f5300,plain,(
    ! [X66,X65] : k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(X66,X65)),X65) ),
    inference(forward_demodulation,[],[f5299,f17])).

fof(f5299,plain,(
    ! [X66,X65] : k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(X66,k4_xboole_0(X65,X66))),X65) ),
    inference(forward_demodulation,[],[f5298,f131])).

fof(f5298,plain,(
    ! [X66,X65] : k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(X66,k4_xboole_0(X65,k4_xboole_0(X66,X66)))),X65) ),
    inference(forward_demodulation,[],[f5297,f15])).

fof(f5297,plain,(
    ! [X66,X65] : k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(k4_xboole_0(X65,k4_xboole_0(X66,X66)),X66)),X65) ),
    inference(forward_demodulation,[],[f5296,f5246])).

fof(f5246,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X2)))) ),
    inference(forward_demodulation,[],[f5245,f59])).

fof(f5245,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X2))))) ),
    inference(forward_demodulation,[],[f5154,f18])).

fof(f5154,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X2)))) ),
    inference(superposition,[],[f4360,f18])).

fof(f5296,plain,(
    ! [X66,X65] : k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X65,k2_xboole_0(k4_xboole_0(X66,X66),k4_xboole_0(X65,k4_xboole_0(X66,X66)))),X65) ),
    inference(forward_demodulation,[],[f5295,f18])).

fof(f5295,plain,(
    ! [X66,X65] : k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X65,k4_xboole_0(X66,X66)),k4_xboole_0(X65,k4_xboole_0(X66,X66))),X65) ),
    inference(forward_demodulation,[],[f5189,f133])).

fof(f133,plain,(
    ! [X14,X15,X13,X16] : k2_xboole_0(X13,k4_xboole_0(X16,k4_xboole_0(X14,k2_xboole_0(X13,X15)))) = k2_xboole_0(X13,k4_xboole_0(X16,k4_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f124,f59])).

fof(f124,plain,(
    ! [X14,X15,X13,X16] : k2_xboole_0(X13,k4_xboole_0(X16,k4_xboole_0(X14,k2_xboole_0(X13,X15)))) = k2_xboole_0(X13,k4_xboole_0(X16,k2_xboole_0(X13,k4_xboole_0(X14,X15)))) ),
    inference(superposition,[],[f59,f59])).

fof(f5189,plain,(
    ! [X66,X65] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X65,k4_xboole_0(X66,X66)),k4_xboole_0(X65,k4_xboole_0(X66,X66))),X65) = k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,k2_xboole_0(X65,X66)))) ),
    inference(superposition,[],[f390,f4360])).

fof(f390,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X12),X11) = k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f363,f15])).

fof(f363,plain,(
    ! [X4,X5] : k2_xboole_0(X5,k4_xboole_0(X4,X4)) = k2_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f131,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f14,f16,f16])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2050,plain,(
    ! [X19,X20] : k4_xboole_0(X19,k4_xboole_0(X20,X20)) = k2_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,X20))) ),
    inference(superposition,[],[f765,f700])).

fof(f700,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X8)) = k2_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f640,f15])).

fof(f765,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(X9,k2_xboole_0(X9,k4_xboole_0(X9,X10))) ),
    inference(forward_demodulation,[],[f710,f15])).

fof(f710,plain,(
    ! [X10,X9] : k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(X9,k2_xboole_0(k4_xboole_0(X9,X10),X9)) ),
    inference(superposition,[],[f440,f640])).

fof(f440,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4))) ),
    inference(forward_demodulation,[],[f439,f30])).

fof(f439,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(X4,X3))) ),
    inference(forward_demodulation,[],[f438,f17])).

fof(f438,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4)))) ),
    inference(forward_demodulation,[],[f437,f18])).

fof(f437,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4))) ),
    inference(forward_demodulation,[],[f396,f377])).

fof(f377,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(X10,k4_xboole_0(X13,k4_xboole_0(X11,k4_xboole_0(X12,X10)))) = k2_xboole_0(X10,k4_xboole_0(X13,k4_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f370,f59])).

fof(f370,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(X10,k4_xboole_0(X13,k4_xboole_0(X11,k4_xboole_0(X12,X10)))) = k2_xboole_0(X10,k4_xboole_0(X13,k2_xboole_0(X10,k4_xboole_0(X11,X12)))) ),
    inference(superposition,[],[f59,f131])).

fof(f396,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3)))) ),
    inference(superposition,[],[f363,f22])).

fof(f4360,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f2289,f4194])).

fof(f4194,plain,(
    ! [X6,X7] : k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k4_xboole_0(X7,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f2290,f22])).

fof(f2290,plain,(
    ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X5) = k4_xboole_0(X4,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f37,f1509])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f18,f22])).

fof(f2289,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f37,f640])).

fof(f10564,plain,(
    ! [X17,X16] : k4_xboole_0(X17,k2_xboole_0(X17,k4_xboole_0(X17,X16))) = k4_xboole_0(X16,k2_xboole_0(X16,k4_xboole_0(X17,X17))) ),
    inference(superposition,[],[f65,f5302])).

fof(f65,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) ),
    inference(backward_demodulation,[],[f43,f59])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f34,f18])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f22,f18])).

fof(f6349,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k2_xboole_0(X19,k4_xboole_0(X19,X20)))) ),
    inference(forward_demodulation,[],[f6348,f2741])).

fof(f2741,plain,(
    ! [X2,X3,X1] : k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X3,k2_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f2664,f765])).

fof(f2664,plain,(
    ! [X2,X3,X1] : k4_xboole_0(X3,k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f32,f1296])).

fof(f1296,plain,(
    ! [X4,X5] : k2_xboole_0(k2_xboole_0(X4,X4),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f756,f171])).

fof(f756,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f755,f17])).

fof(f755,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f705,f15])).

fof(f705,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X0),X0)) ),
    inference(superposition,[],[f23,f640])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f31,f18])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) ),
    inference(forward_demodulation,[],[f29,f18])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[],[f18,f18])).

fof(f6348,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,X19)))) ),
    inference(forward_demodulation,[],[f6347,f4017])).

fof(f4017,plain,(
    ! [X39,X37,X38] : k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X38,k2_xboole_0(X37,X37)))) = k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X38,X37))) ),
    inference(forward_demodulation,[],[f3938,f23])).

fof(f3938,plain,(
    ! [X39,X37,X38] : k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X38,k2_xboole_0(X37,X37)))) = k2_xboole_0(k4_xboole_0(X37,X39),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X37)))) ),
    inference(superposition,[],[f23,f2230])).

fof(f2230,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f2229,f756])).

fof(f2229,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f2132,f17])).

fof(f2132,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0))) ),
    inference(superposition,[],[f23,f1005])).

fof(f1005,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X16,X16))) ),
    inference(forward_demodulation,[],[f1004,f17])).

fof(f1004,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X16,k4_xboole_0(X16,X16)))) ),
    inference(forward_demodulation,[],[f952,f18])).

fof(f952,plain,(
    ! [X15,X16] : k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(k4_xboole_0(X16,X16),k4_xboole_0(X16,X16))) ),
    inference(superposition,[],[f700,f440])).

fof(f6347,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,k2_xboole_0(X19,X19))))) ),
    inference(forward_demodulation,[],[f6346,f22])).

fof(f6346,plain,(
    ! [X19,X20] : k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),X19))) ),
    inference(forward_demodulation,[],[f6196,f131])).

fof(f6196,plain,(
    ! [X19,X20] : k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),X19))) = k2_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,X19))) ),
    inference(superposition,[],[f45,f2230])).

fof(f45,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f38,f15])).

fof(f38,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f17,f22])).

fof(f8209,plain,(
    ! [X109,X110] : k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(k4_xboole_0(X109,k4_xboole_0(X110,X109)),k4_xboole_0(X109,k2_xboole_0(X110,X109))) ),
    inference(forward_demodulation,[],[f8208,f6621])).

fof(f6621,plain,(
    ! [X2,X3,X1] : k4_xboole_0(X3,k2_xboole_0(X1,X2)) = k4_xboole_0(X3,k2_xboole_0(X1,k2_xboole_0(X2,X2))) ),
    inference(superposition,[],[f32,f6105])).

fof(f6105,plain,(
    ! [X61,X60] : k2_xboole_0(X61,X60) = k2_xboole_0(k2_xboole_0(X61,X60),X60) ),
    inference(forward_demodulation,[],[f6083,f5956])).

fof(f5956,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f1406,f5950])).

fof(f5950,plain,(
    ! [X47,X48] : k2_xboole_0(X47,X48) = k2_xboole_0(k2_xboole_0(X48,X47),k2_xboole_0(X47,X48)) ),
    inference(forward_demodulation,[],[f5949,f5677])).

fof(f5677,plain,(
    ! [X21,X20] : k2_xboole_0(X21,X20) = k2_xboole_0(X21,k2_xboole_0(X20,X21)) ),
    inference(forward_demodulation,[],[f5676,f17])).

fof(f5676,plain,(
    ! [X21,X20] : k2_xboole_0(X21,k4_xboole_0(X20,X21)) = k2_xboole_0(X21,k2_xboole_0(X20,X21)) ),
    inference(forward_demodulation,[],[f5573,f17])).

fof(f5573,plain,(
    ! [X21,X20] : k2_xboole_0(X21,k4_xboole_0(X20,X21)) = k2_xboole_0(X21,k4_xboole_0(k2_xboole_0(X20,X21),X21)) ),
    inference(superposition,[],[f5320,f20])).

fof(f5320,plain,(
    ! [X17,X18] : k2_xboole_0(X18,X17) = k2_xboole_0(X18,k2_xboole_0(X17,k4_xboole_0(X18,X18))) ),
    inference(backward_demodulation,[],[f1079,f5302])).

fof(f1079,plain,(
    ! [X17,X18] : k2_xboole_0(X18,X17) = k2_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X18,X18))) ),
    inference(superposition,[],[f764,f700])).

fof(f5949,plain,(
    ! [X47,X48] : k2_xboole_0(X47,k2_xboole_0(X48,X47)) = k2_xboole_0(k2_xboole_0(X48,X47),k2_xboole_0(X47,X48)) ),
    inference(forward_demodulation,[],[f5886,f15])).

fof(f5886,plain,(
    ! [X47,X48] : k2_xboole_0(k2_xboole_0(X48,X47),X47) = k2_xboole_0(k2_xboole_0(X48,X47),k2_xboole_0(X47,X48)) ),
    inference(superposition,[],[f5677,f5677])).

fof(f1406,plain,(
    ! [X4,X3] : k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)),k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f1398,f171])).

fof(f1398,plain,(
    ! [X36] : k2_xboole_0(X36,X36) = k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) ),
    inference(forward_demodulation,[],[f1397,f17])).

fof(f1397,plain,(
    ! [X36] : k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) = k2_xboole_0(X36,k4_xboole_0(X36,X36)) ),
    inference(forward_demodulation,[],[f1396,f131])).

fof(f1396,plain,(
    ! [X36] : k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) = k2_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X36,X36))) ),
    inference(forward_demodulation,[],[f1395,f995])).

fof(f995,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f938,f17])).

fof(f938,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f700,f18])).

fof(f1395,plain,(
    ! [X36] : k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) = k4_xboole_0(X36,k4_xboole_0(X36,k2_xboole_0(X36,X36))) ),
    inference(forward_demodulation,[],[f1370,f18])).

fof(f1370,plain,(
    ! [X36] : k4_xboole_0(X36,k4_xboole_0(k4_xboole_0(X36,X36),X36)) = k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) ),
    inference(superposition,[],[f756,f1295])).

fof(f1295,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f756,f1158])).

fof(f1158,plain,(
    ! [X7] : k2_xboole_0(X7,X7) = k2_xboole_0(k4_xboole_0(X7,X7),k2_xboole_0(X7,X7)) ),
    inference(forward_demodulation,[],[f1157,f17])).

fof(f1157,plain,(
    ! [X7] : k2_xboole_0(X7,k4_xboole_0(X7,X7)) = k2_xboole_0(k4_xboole_0(X7,X7),k2_xboole_0(X7,X7)) ),
    inference(forward_demodulation,[],[f1144,f15])).

fof(f1144,plain,(
    ! [X7] : k2_xboole_0(k4_xboole_0(X7,X7),X7) = k2_xboole_0(k4_xboole_0(X7,X7),k2_xboole_0(X7,X7)) ),
    inference(superposition,[],[f764,f1079])).

fof(f6083,plain,(
    ! [X61,X60] : k2_xboole_0(k2_xboole_0(X61,X60),X60) = k2_xboole_0(k2_xboole_0(X61,X60),k2_xboole_0(X61,X60)) ),
    inference(superposition,[],[f5677,f5787])).

fof(f5787,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f5619,f15])).

fof(f5619,plain,(
    ! [X19,X18] : k2_xboole_0(X19,X18) = k2_xboole_0(X19,k2_xboole_0(X19,X18)) ),
    inference(forward_demodulation,[],[f5618,f17])).

fof(f5618,plain,(
    ! [X19,X18] : k2_xboole_0(X19,k4_xboole_0(X18,X19)) = k2_xboole_0(X19,k2_xboole_0(X19,X18)) ),
    inference(forward_demodulation,[],[f5572,f17])).

fof(f5572,plain,(
    ! [X19,X18] : k2_xboole_0(X19,k4_xboole_0(X18,X19)) = k2_xboole_0(X19,k4_xboole_0(k2_xboole_0(X19,X18),X19)) ),
    inference(superposition,[],[f5320,f55])).

fof(f8208,plain,(
    ! [X109,X110] : k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(k4_xboole_0(X109,k4_xboole_0(X110,X109)),k4_xboole_0(X109,k2_xboole_0(X110,k2_xboole_0(X109,X109)))) ),
    inference(forward_demodulation,[],[f8117,f18])).

fof(f8117,plain,(
    ! [X109,X110] : k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(k4_xboole_0(X109,k4_xboole_0(X110,X109)),k4_xboole_0(k4_xboole_0(X109,X110),k2_xboole_0(X109,X109))) ),
    inference(superposition,[],[f6131,f1296])).

fof(f6131,plain,(
    ! [X57,X58] : k2_xboole_0(X58,X57) = k2_xboole_0(k2_xboole_0(X58,X57),k4_xboole_0(X57,X58)) ),
    inference(superposition,[],[f5995,f1509])).

fof(f5995,plain,(
    ! [X50,X49] : k2_xboole_0(X49,X50) = k2_xboole_0(k2_xboole_0(X49,X50),X49) ),
    inference(forward_demodulation,[],[f5887,f5956])).

fof(f5887,plain,(
    ! [X50,X49] : k2_xboole_0(k2_xboole_0(X49,X50),X49) = k2_xboole_0(k2_xboole_0(X49,X50),k2_xboole_0(X49,X50)) ),
    inference(superposition,[],[f5677,f5619])).

fof(f5405,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X9,X10))) = k4_xboole_0(k2_xboole_0(X9,X9),X10) ),
    inference(backward_demodulation,[],[f638,f5403])).

fof(f5403,plain,(
    ! [X24,X23] : k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X23)) = k4_xboole_0(k2_xboole_0(X23,X23),X24) ),
    inference(forward_demodulation,[],[f5328,f1381])).

fof(f1381,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X0),X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f1380,f20])).

fof(f1380,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0))) ),
    inference(forward_demodulation,[],[f1379,f59])).

fof(f1379,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) ),
    inference(forward_demodulation,[],[f1378,f18])).

fof(f1378,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X0))) ),
    inference(forward_demodulation,[],[f1346,f131])).

fof(f1346,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f1295,f18])).

fof(f5328,plain,(
    ! [X24,X23] : k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X23)) = k4_xboole_0(X23,k2_xboole_0(X24,k4_xboole_0(X23,X23))) ),
    inference(backward_demodulation,[],[f2746,f5302])).

fof(f2746,plain,(
    ! [X24,X23] : k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X23,X23))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X23)) ),
    inference(backward_demodulation,[],[f1365,f2745])).

fof(f2745,plain,(
    ! [X21,X19,X20] : k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,X19))) = k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,X19)) ),
    inference(forward_demodulation,[],[f2743,f30])).

fof(f2743,plain,(
    ! [X21,X19,X20] : k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,X19))) = k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,k4_xboole_0(X19,X20)))) ),
    inference(backward_demodulation,[],[f1305,f2741])).

fof(f1305,plain,(
    ! [X21,X19,X20] : k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,X19))) = k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k4_xboole_0(X19,k4_xboole_0(X20,X19)))) ),
    inference(superposition,[],[f59,f756])).

fof(f1365,plain,(
    ! [X24,X23] : k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X23,X23))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,k2_xboole_0(X23,X23))) ),
    inference(superposition,[],[f23,f1295])).

fof(f638,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X9)) = k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X9,X10))) ),
    inference(superposition,[],[f23,f131])).

fof(f18167,plain,(
    ! [X26,X25] : k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(X25,k2_xboole_0(X26,k4_xboole_0(X26,X25)))) ),
    inference(forward_demodulation,[],[f18166,f5619])).

fof(f18166,plain,(
    ! [X26,X25] : k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(X25,k2_xboole_0(X26,k2_xboole_0(X26,k4_xboole_0(X26,X25))))) ),
    inference(forward_demodulation,[],[f18149,f842])).

fof(f842,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(X11,k2_xboole_0(X8,k2_xboole_0(X9,X10))) = k4_xboole_0(X11,k2_xboole_0(X10,k2_xboole_0(X9,X8))) ),
    inference(superposition,[],[f32,f171])).

fof(f18149,plain,(
    ! [X26,X25] : k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(X25,k2_xboole_0(k4_xboole_0(X26,X25),k2_xboole_0(X26,X26)))) ),
    inference(backward_demodulation,[],[f1942,f18023])).

fof(f18023,plain,(
    ! [X28,X26,X27] : k4_xboole_0(k2_xboole_0(X26,k4_xboole_0(X26,X27)),X28) = k4_xboole_0(X26,k2_xboole_0(k4_xboole_0(X27,X26),X28)) ),
    inference(superposition,[],[f18,f10945])).

fof(f1942,plain,(
    ! [X26,X25] : k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X25,X26)),k2_xboole_0(X26,X26))) ),
    inference(forward_demodulation,[],[f1941,f17])).

fof(f1941,plain,(
    ! [X26,X25] : k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X25,X26)),k2_xboole_0(X26,X26))) ),
    inference(forward_demodulation,[],[f1940,f75])).

fof(f1940,plain,(
    ! [X26,X25] : k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(k4_xboole_0(X25,X26),X25),k2_xboole_0(X26,X26))) ),
    inference(forward_demodulation,[],[f1888,f18])).

fof(f1888,plain,(
    ! [X26,X25] : k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X25,X26),X25),X26),X26)) ),
    inference(superposition,[],[f1110,f55])).

fof(f1110,plain,(
    ! [X24,X23] : k2_xboole_0(X24,X23) = k2_xboole_0(X24,k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X23,X24)),X24)) ),
    inference(forward_demodulation,[],[f1109,f17])).

fof(f1109,plain,(
    ! [X24,X23] : k2_xboole_0(X24,k4_xboole_0(X23,X24)) = k2_xboole_0(X24,k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X23,X24)),X24)) ),
    inference(forward_demodulation,[],[f1080,f75])).

fof(f1080,plain,(
    ! [X24,X23] : k2_xboole_0(X24,k4_xboole_0(X23,X24)) = k2_xboole_0(X24,k4_xboole_0(k2_xboole_0(k4_xboole_0(X23,X24),X23),X24)) ),
    inference(superposition,[],[f764,f55])).

fof(f44864,plain,(
    ! [X61,X59,X60] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X59,X59),X60),k4_xboole_0(X61,X59)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X59,X59),X60),k4_xboole_0(X61,k4_xboole_0(X60,k4_xboole_0(X60,X59)))) ),
    inference(superposition,[],[f131,f34383])).

fof(f34383,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X18,X18),X17)) ),
    inference(forward_demodulation,[],[f34382,f20])).

fof(f34382,plain,(
    ! [X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X18,k2_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,X17))) ),
    inference(forward_demodulation,[],[f34139,f4506])).

fof(f4506,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(k2_xboole_0(X15,X15),X16)) ),
    inference(forward_demodulation,[],[f4505,f1381])).

fof(f4505,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X15,X15)))) ),
    inference(forward_demodulation,[],[f4504,f65])).

fof(f4504,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,X16)))) ),
    inference(forward_demodulation,[],[f4253,f4374])).

fof(f4374,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k2_xboole_0(X3,X2))) ),
    inference(backward_demodulation,[],[f3373,f4360])).

fof(f3373,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2)))) ),
    inference(backward_demodulation,[],[f2939,f3352])).

fof(f3352,plain,(
    ! [X26,X25] : k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X25,X25))) ),
    inference(backward_demodulation,[],[f2563,f3299])).

fof(f3299,plain,(
    ! [X14,X13] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,X14))) ),
    inference(superposition,[],[f2047,f23])).

fof(f2047,plain,(
    ! [X14,X13] : k2_xboole_0(k4_xboole_0(X14,X14),X13) = k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,X14),X13)) ),
    inference(superposition,[],[f765,f390])).

fof(f2563,plain,(
    ! [X26,X25] : k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X25,X25))) ),
    inference(forward_demodulation,[],[f2562,f1295])).

fof(f2562,plain,(
    ! [X26,X25] : k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X25,k4_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f2561,f2295])).

fof(f2295,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X17)),k4_xboole_0(X17,k4_xboole_0(X17,X19))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19))) ),
    inference(superposition,[],[f37,f23])).

fof(f2561,plain,(
    ! [X26,X25] : k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X25,X25)))) ),
    inference(forward_demodulation,[],[f2387,f632])).

fof(f632,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(X6,X5)) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X5,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f23,f22])).

fof(f2387,plain,(
    ! [X26,X25] : k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X26,k2_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,k4_xboole_0(X25,X26))))) ),
    inference(superposition,[],[f1295,f37])).

fof(f2939,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X3,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X3,X3))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2)))) ),
    inference(forward_demodulation,[],[f2938,f18])).

fof(f2938,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X3)) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X3)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2)))) ),
    inference(forward_demodulation,[],[f2937,f23])).

fof(f2937,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2)))) ),
    inference(forward_demodulation,[],[f2899,f632])).

fof(f2899,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3))))) ),
    inference(superposition,[],[f2869,f37])).

fof(f2869,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f2868,f17])).

fof(f2868,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f2804,f15])).

fof(f2804,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f1457,f55])).

fof(f1457,plain,(
    ! [X19,X18] : k2_xboole_0(X18,X19) = k2_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,k4_xboole_0(X19,X19))) ),
    inference(superposition,[],[f1105,f700])).

fof(f4253,plain,(
    ! [X15,X16] : k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,X16)))) = k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X16,k2_xboole_0(X15,X16))) ),
    inference(superposition,[],[f22,f2290])).

fof(f34139,plain,(
    ! [X17,X18] : k4_xboole_0(X18,k2_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,X17))) = k4_xboole_0(X17,k4_xboole_0(k2_xboole_0(X17,X17),X18)) ),
    inference(superposition,[],[f65,f10753])).

fof(f10753,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X12),X13) = k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X13,X12))) ),
    inference(forward_demodulation,[],[f10562,f1381])).

fof(f10562,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k2_xboole_0(X13,k4_xboole_0(X12,X12))) = k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X13,X12))) ),
    inference(superposition,[],[f65,f22])).

fof(f34149,plain,(
    ! [X54,X52,X53] : k4_xboole_0(k2_xboole_0(X54,X52),k4_xboole_0(X53,k4_xboole_0(X53,X52))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X52,X52),X53),k4_xboole_0(X54,k4_xboole_0(X53,k4_xboole_0(X53,X52)))) ),
    inference(superposition,[],[f55,f10753])).

fof(f27,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f25])).

fof(f21,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f13,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.36  % Computer   : n024.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % WCLimit    : 600
% 0.13/0.36  % DateTime   : Tue Dec  1 19:40:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.38  ipcrm: permission denied for id (1243316225)
% 0.13/0.38  ipcrm: permission denied for id (1243348994)
% 0.13/0.38  ipcrm: permission denied for id (1243381763)
% 0.13/0.38  ipcrm: permission denied for id (1243414532)
% 0.13/0.38  ipcrm: permission denied for id (1243447301)
% 0.13/0.39  ipcrm: permission denied for id (1247150087)
% 0.13/0.39  ipcrm: permission denied for id (1243545608)
% 0.13/0.39  ipcrm: permission denied for id (1243578377)
% 0.13/0.39  ipcrm: permission denied for id (1247182858)
% 0.13/0.39  ipcrm: permission denied for id (1247215627)
% 0.13/0.39  ipcrm: permission denied for id (1247248396)
% 0.13/0.39  ipcrm: permission denied for id (1243742221)
% 0.13/0.39  ipcrm: permission denied for id (1247281166)
% 0.13/0.40  ipcrm: permission denied for id (1243807759)
% 0.13/0.40  ipcrm: permission denied for id (1247313936)
% 0.21/0.40  ipcrm: permission denied for id (1243873298)
% 0.21/0.40  ipcrm: permission denied for id (1243938836)
% 0.21/0.40  ipcrm: permission denied for id (1243971605)
% 0.21/0.40  ipcrm: permission denied for id (1244004374)
% 0.21/0.40  ipcrm: permission denied for id (1244037143)
% 0.21/0.41  ipcrm: permission denied for id (1244069912)
% 0.21/0.41  ipcrm: permission denied for id (1244102681)
% 0.21/0.41  ipcrm: permission denied for id (1244135450)
% 0.21/0.41  ipcrm: permission denied for id (1249345563)
% 0.21/0.41  ipcrm: permission denied for id (1249443869)
% 0.21/0.41  ipcrm: permission denied for id (1247543327)
% 0.21/0.42  ipcrm: permission denied for id (1249542177)
% 0.21/0.42  ipcrm: permission denied for id (1244332066)
% 0.21/0.42  ipcrm: permission denied for id (1244364835)
% 0.21/0.42  ipcrm: permission denied for id (1247641636)
% 0.21/0.42  ipcrm: permission denied for id (1244430373)
% 0.21/0.42  ipcrm: permission denied for id (1244463142)
% 0.21/0.43  ipcrm: permission denied for id (1247707176)
% 0.21/0.43  ipcrm: permission denied for id (1244528681)
% 0.21/0.43  ipcrm: permission denied for id (1244561450)
% 0.21/0.43  ipcrm: permission denied for id (1247739947)
% 0.21/0.43  ipcrm: permission denied for id (1249607724)
% 0.21/0.43  ipcrm: permission denied for id (1247805485)
% 0.21/0.43  ipcrm: permission denied for id (1244725295)
% 0.21/0.44  ipcrm: permission denied for id (1244758064)
% 0.21/0.44  ipcrm: permission denied for id (1244790833)
% 0.21/0.44  ipcrm: permission denied for id (1247871026)
% 0.21/0.44  ipcrm: permission denied for id (1244856371)
% 0.21/0.44  ipcrm: permission denied for id (1247969333)
% 0.21/0.44  ipcrm: permission denied for id (1248002102)
% 0.21/0.45  ipcrm: permission denied for id (1245020216)
% 0.21/0.45  ipcrm: permission denied for id (1245052985)
% 0.21/0.45  ipcrm: permission denied for id (1245085754)
% 0.21/0.45  ipcrm: permission denied for id (1248067643)
% 0.21/0.45  ipcrm: permission denied for id (1245151292)
% 0.21/0.45  ipcrm: permission denied for id (1245184061)
% 0.21/0.45  ipcrm: permission denied for id (1245216830)
% 0.21/0.46  ipcrm: permission denied for id (1248100415)
% 0.21/0.46  ipcrm: permission denied for id (1245282368)
% 0.21/0.46  ipcrm: permission denied for id (1249738817)
% 0.21/0.46  ipcrm: permission denied for id (1245347906)
% 0.21/0.46  ipcrm: permission denied for id (1245380675)
% 0.21/0.46  ipcrm: permission denied for id (1248165956)
% 0.21/0.46  ipcrm: permission denied for id (1249771589)
% 0.21/0.46  ipcrm: permission denied for id (1245478982)
% 0.21/0.47  ipcrm: permission denied for id (1248231495)
% 0.21/0.47  ipcrm: permission denied for id (1245544520)
% 0.21/0.47  ipcrm: permission denied for id (1245577289)
% 0.21/0.47  ipcrm: permission denied for id (1248297035)
% 0.21/0.47  ipcrm: permission denied for id (1245642828)
% 0.21/0.47  ipcrm: permission denied for id (1249837133)
% 0.21/0.47  ipcrm: permission denied for id (1245708366)
% 0.21/0.48  ipcrm: permission denied for id (1245741135)
% 0.21/0.48  ipcrm: permission denied for id (1245806673)
% 0.21/0.48  ipcrm: permission denied for id (1245839442)
% 0.21/0.48  ipcrm: permission denied for id (1248395347)
% 0.21/0.48  ipcrm: permission denied for id (1248428116)
% 0.21/0.48  ipcrm: permission denied for id (1245904981)
% 0.21/0.49  ipcrm: permission denied for id (1245937750)
% 0.21/0.49  ipcrm: permission denied for id (1249902679)
% 0.21/0.49  ipcrm: permission denied for id (1245970520)
% 0.21/0.49  ipcrm: permission denied for id (1246003289)
% 0.21/0.49  ipcrm: permission denied for id (1249935450)
% 0.21/0.49  ipcrm: permission denied for id (1248559195)
% 0.21/0.49  ipcrm: permission denied for id (1246101596)
% 0.21/0.50  ipcrm: permission denied for id (1248624734)
% 0.21/0.50  ipcrm: permission denied for id (1246167135)
% 0.21/0.50  ipcrm: permission denied for id (1248657504)
% 0.21/0.50  ipcrm: permission denied for id (1246232673)
% 0.21/0.50  ipcrm: permission denied for id (1246298211)
% 0.21/0.50  ipcrm: permission denied for id (1246330980)
% 0.21/0.50  ipcrm: permission denied for id (1248723045)
% 0.21/0.51  ipcrm: permission denied for id (1250033766)
% 0.21/0.51  ipcrm: permission denied for id (1248788583)
% 0.21/0.51  ipcrm: permission denied for id (1246429288)
% 0.21/0.51  ipcrm: permission denied for id (1248821353)
% 0.21/0.51  ipcrm: permission denied for id (1250066538)
% 0.21/0.51  ipcrm: permission denied for id (1246462059)
% 0.21/0.51  ipcrm: permission denied for id (1248886892)
% 0.21/0.52  ipcrm: permission denied for id (1246527597)
% 0.21/0.52  ipcrm: permission denied for id (1246560366)
% 0.21/0.52  ipcrm: permission denied for id (1250099311)
% 0.21/0.52  ipcrm: permission denied for id (1246593136)
% 0.21/0.52  ipcrm: permission denied for id (1246625905)
% 0.21/0.52  ipcrm: permission denied for id (1246658674)
% 0.21/0.53  ipcrm: permission denied for id (1246756981)
% 0.21/0.53  ipcrm: permission denied for id (1249050742)
% 0.21/0.53  ipcrm: permission denied for id (1250197623)
% 0.21/0.53  ipcrm: permission denied for id (1249116280)
% 0.21/0.53  ipcrm: permission denied for id (1246855289)
% 0.21/0.53  ipcrm: permission denied for id (1246920827)
% 0.21/0.53  ipcrm: permission denied for id (1249181820)
% 0.21/0.54  ipcrm: permission denied for id (1246986365)
% 0.21/0.54  ipcrm: permission denied for id (1247019134)
% 0.21/0.54  ipcrm: permission denied for id (1247051903)
% 0.98/0.63  % (7478)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.98/0.63  % (7481)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.98/0.64  % (7486)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.98/0.65  % (7482)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.98/0.65  % (7492)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.15/0.66  % (7491)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.15/0.66  % (7493)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.15/0.66  % (7483)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 1.15/0.66  % (7476)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 1.15/0.67  % (7480)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 1.15/0.67  % (7477)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.15/0.67  % (7479)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 1.15/0.67  % (7488)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.15/0.67  % (7488)Refutation not found, incomplete strategy% (7488)------------------------------
% 1.15/0.67  % (7488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.67  % (7488)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.67  
% 1.15/0.67  % (7488)Memory used [KB]: 10490
% 1.15/0.67  % (7488)Time elapsed: 0.070 s
% 1.15/0.67  % (7488)------------------------------
% 1.15/0.67  % (7488)------------------------------
% 1.15/0.68  % (7489)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.15/0.69  % (7484)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.15/0.69  % (7485)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.15/0.69  % (7490)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.15/0.69  % (7494)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.31/1.20  % (7480)Time limit reached!
% 5.31/1.20  % (7480)------------------------------
% 5.31/1.20  % (7480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.31/1.22  % (7480)Termination reason: Time limit
% 5.31/1.22  % (7480)Termination phase: Saturation
% 5.31/1.22  
% 5.31/1.22  % (7480)Memory used [KB]: 16886
% 5.31/1.22  % (7480)Time elapsed: 0.600 s
% 5.31/1.22  % (7480)------------------------------
% 5.31/1.22  % (7480)------------------------------
% 12.59/2.10  % (7481)Time limit reached!
% 12.59/2.10  % (7481)------------------------------
% 12.59/2.10  % (7481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.59/2.10  % (7481)Termination reason: Time limit
% 12.59/2.10  % (7481)Termination phase: Saturation
% 12.59/2.10  
% 12.59/2.10  % (7481)Memory used [KB]: 47717
% 12.59/2.10  % (7481)Time elapsed: 1.500 s
% 12.59/2.10  % (7481)------------------------------
% 12.59/2.10  % (7481)------------------------------
% 12.59/2.13  % (7482)Time limit reached!
% 12.59/2.13  % (7482)------------------------------
% 12.59/2.13  % (7482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.59/2.13  % (7482)Termination reason: Time limit
% 12.59/2.13  % (7482)Termination phase: Saturation
% 12.59/2.13  
% 12.59/2.13  % (7482)Memory used [KB]: 37867
% 12.59/2.13  % (7482)Time elapsed: 1.500 s
% 12.59/2.13  % (7482)------------------------------
% 12.59/2.13  % (7482)------------------------------
% 14.98/2.41  % (7478)Time limit reached!
% 14.98/2.41  % (7478)------------------------------
% 14.98/2.41  % (7478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.98/2.42  % (7478)Termination reason: Time limit
% 14.98/2.42  
% 14.98/2.42  % (7478)Memory used [KB]: 45542
% 14.98/2.42  % (7478)Time elapsed: 1.805 s
% 14.98/2.42  % (7478)------------------------------
% 14.98/2.42  % (7478)------------------------------
% 18.20/2.81  % (7489)Time limit reached!
% 18.20/2.81  % (7489)------------------------------
% 18.20/2.81  % (7489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.20/2.81  % (7489)Termination reason: Time limit
% 18.20/2.81  
% 18.20/2.81  % (7489)Memory used [KB]: 38634
% 18.20/2.81  % (7489)Time elapsed: 2.204 s
% 18.20/2.81  % (7489)------------------------------
% 18.20/2.81  % (7489)------------------------------
% 22.30/3.34  % (7486)Refutation found. Thanks to Tanya!
% 22.30/3.34  % SZS status Theorem for theBenchmark
% 22.30/3.34  % SZS output start Proof for theBenchmark
% 22.30/3.34  fof(f45439,plain,(
% 22.30/3.34    $false),
% 22.30/3.34    inference(avatar_sat_refutation,[],[f28,f45318])).
% 22.30/3.34  fof(f45318,plain,(
% 22.30/3.34    spl2_1),
% 22.30/3.34    inference(avatar_contradiction_clause,[],[f45316])).
% 22.30/3.34  fof(f45316,plain,(
% 22.30/3.34    $false | spl2_1),
% 22.30/3.34    inference(subsumption_resolution,[],[f27,f45314])).
% 22.30/3.34  fof(f45314,plain,(
% 22.30/3.34    ( ! [X54,X52,X53] : (k4_xboole_0(k2_xboole_0(X54,X52),k4_xboole_0(X53,k4_xboole_0(X53,X52))) = k2_xboole_0(k4_xboole_0(X54,X52),k4_xboole_0(X52,X53))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f34149,f45313])).
% 22.30/3.34  fof(f45313,plain,(
% 22.30/3.34    ( ! [X61,X59,X60] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X59,X59),X60),k4_xboole_0(X61,k4_xboole_0(X60,k4_xboole_0(X60,X59)))) = k2_xboole_0(k4_xboole_0(X61,X59),k4_xboole_0(X59,X60))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f44864,f19052])).
% 22.30/3.34  fof(f19052,plain,(
% 22.30/3.34    ( ! [X23,X21,X22] : (k2_xboole_0(X23,k4_xboole_0(X21,X22)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X21,X21),X22),X23)) )),
% 22.30/3.34    inference(superposition,[],[f18767,f55])).
% 22.30/3.34  fof(f55,plain,(
% 22.30/3.34    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4)) )),
% 22.30/3.34    inference(superposition,[],[f20,f15])).
% 22.30/3.34  fof(f15,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 22.30/3.34    inference(cnf_transformation,[],[f1])).
% 22.30/3.34  fof(f1,axiom,(
% 22.30/3.34    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 22.30/3.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 22.30/3.34  fof(f20,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 22.30/3.34    inference(cnf_transformation,[],[f5])).
% 22.30/3.34  fof(f5,axiom,(
% 22.30/3.34    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 22.30/3.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 22.30/3.34  fof(f18767,plain,(
% 22.30/3.34    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k2_xboole_0(X5,X5),X4)) )),
% 22.30/3.34    inference(superposition,[],[f18494,f171])).
% 22.30/3.34  fof(f171,plain,(
% 22.30/3.34    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k2_xboole_0(X8,X7)) = k2_xboole_0(k2_xboole_0(X7,X8),X6)) )),
% 22.30/3.34    inference(superposition,[],[f147,f15])).
% 22.30/3.34  fof(f147,plain,(
% 22.30/3.34    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X3,k2_xboole_0(X5,X4))) )),
% 22.30/3.34    inference(superposition,[],[f90,f17])).
% 22.30/3.34  fof(f17,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 22.30/3.34    inference(cnf_transformation,[],[f3])).
% 22.30/3.34  fof(f3,axiom,(
% 22.30/3.34    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 22.30/3.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 22.30/3.34  fof(f90,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X1,X0),X2))) )),
% 22.30/3.34    inference(superposition,[],[f17,f75])).
% 22.30/3.34  fof(f75,plain,(
% 22.30/3.34    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X5),X4) = k4_xboole_0(k2_xboole_0(X5,X3),X4)) )),
% 22.30/3.34    inference(superposition,[],[f55,f20])).
% 22.30/3.34  fof(f18494,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X1))) )),
% 22.30/3.34    inference(superposition,[],[f18168,f90])).
% 22.30/3.34  fof(f18168,plain,(
% 22.30/3.34    ( ! [X26,X25] : (k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X25,X25),X26))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f18167,f10958])).
% 22.30/3.34  fof(f10958,plain,(
% 22.30/3.34    ( ! [X10,X9] : (k4_xboole_0(k2_xboole_0(X9,X9),X10) = k4_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X10,X9)))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f5405,f10945])).
% 22.30/3.34  fof(f10945,plain,(
% 22.30/3.34    ( ! [X109,X110] : (k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(X109,k4_xboole_0(X109,X110))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f8209,f10822])).
% 22.30/3.34  fof(f10822,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k2_xboole_0(X20,X19)))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f6349,f10774])).
% 22.30/3.34  fof(f10774,plain,(
% 22.30/3.34    ( ! [X17,X16] : (k4_xboole_0(X17,k2_xboole_0(X16,X17)) = k4_xboole_0(X17,k2_xboole_0(X17,k4_xboole_0(X17,X16)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f10564,f5351])).
% 22.30/3.34  fof(f5351,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X1,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X0,k4_xboole_0(X1,X1)))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f4360,f5302])).
% 22.30/3.34  fof(f5302,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k2_xboole_0(X19,k4_xboole_0(X20,X20)) = k4_xboole_0(X19,k4_xboole_0(X20,X20))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f2050,f5301])).
% 22.30/3.34  fof(f5301,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(X65,k4_xboole_0(X66,X66))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5300,f1518])).
% 22.30/3.34  fof(f1518,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2)) )),
% 22.30/3.34    inference(superposition,[],[f1509,f18])).
% 22.30/3.34  fof(f18,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 22.30/3.34    inference(cnf_transformation,[],[f4])).
% 22.30/3.34  fof(f4,axiom,(
% 22.30/3.34    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 22.30/3.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 22.30/3.34  fof(f1509,plain,(
% 22.30/3.34    ( ! [X26,X27] : (k2_xboole_0(X27,X26) = k2_xboole_0(k4_xboole_0(X26,X27),X27)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1459,f1508])).
% 22.30/3.34  fof(f1508,plain,(
% 22.30/3.34    ( ! [X24,X25] : (k2_xboole_0(X25,X24) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X24,X25)),X25))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1507,f17])).
% 22.30/3.34  fof(f1507,plain,(
% 22.30/3.34    ( ! [X24,X25] : (k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X24,X25)),X25)) = k2_xboole_0(X25,k4_xboole_0(X24,X25))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1506,f15])).
% 22.30/3.34  fof(f1506,plain,(
% 22.30/3.34    ( ! [X24,X25] : (k2_xboole_0(k4_xboole_0(X24,X25),X25) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(X24,k4_xboole_0(X24,X25)),X25))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1458,f75])).
% 22.30/3.34  fof(f1458,plain,(
% 22.30/3.34    ( ! [X24,X25] : (k2_xboole_0(k4_xboole_0(X24,X25),X25) = k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X24,X25)),k4_xboole_0(k2_xboole_0(k4_xboole_0(X24,X25),X24),X25))) )),
% 22.30/3.34    inference(superposition,[],[f1105,f55])).
% 22.30/3.34  fof(f1105,plain,(
% 22.30/3.34    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,k4_xboole_0(X6,X7)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1104,f17])).
% 22.30/3.34  fof(f1104,plain,(
% 22.30/3.34    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X7,X6)) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,k4_xboole_0(X6,X7)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1073,f15])).
% 22.30/3.34  fof(f1073,plain,(
% 22.30/3.34    ( ! [X6,X7] : (k2_xboole_0(k4_xboole_0(X7,X6),X6) = k2_xboole_0(k4_xboole_0(X7,X6),k2_xboole_0(X6,k4_xboole_0(X6,X7)))) )),
% 22.30/3.34    inference(superposition,[],[f764,f131])).
% 22.30/3.34  fof(f131,plain,(
% 22.30/3.34    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,X7))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f122,f59])).
% 22.30/3.34  fof(f59,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) )),
% 22.30/3.34    inference(superposition,[],[f30,f15])).
% 22.30/3.34  fof(f30,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 22.30/3.34    inference(superposition,[],[f17,f18])).
% 22.30/3.34  fof(f122,plain,(
% 22.30/3.34    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 22.30/3.34    inference(superposition,[],[f59,f17])).
% 22.30/3.34  fof(f764,plain,(
% 22.30/3.34    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f763,f17])).
% 22.30/3.34  fof(f763,plain,(
% 22.30/3.34    ( ! [X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k2_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(X7,X8)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f709,f15])).
% 22.30/3.34  fof(f709,plain,(
% 22.30/3.34    ( ! [X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X7,X8)) = k2_xboole_0(X8,k2_xboole_0(k4_xboole_0(X7,X8),X7))) )),
% 22.30/3.34    inference(superposition,[],[f131,f640])).
% 22.30/3.34  fof(f640,plain,(
% 22.30/3.34    ( ! [X14,X13] : (k4_xboole_0(X13,k4_xboole_0(X14,X14)) = k2_xboole_0(k4_xboole_0(X13,X14),X13)) )),
% 22.30/3.34    inference(superposition,[],[f23,f17])).
% 22.30/3.34  fof(f23,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 22.30/3.34    inference(definition_unfolding,[],[f19,f16])).
% 22.30/3.34  fof(f16,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 22.30/3.34    inference(cnf_transformation,[],[f6])).
% 22.30/3.34  fof(f6,axiom,(
% 22.30/3.34    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 22.30/3.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 22.30/3.34  fof(f19,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 22.30/3.34    inference(cnf_transformation,[],[f7])).
% 22.30/3.34  fof(f7,axiom,(
% 22.30/3.34    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 22.30/3.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 22.30/3.34  fof(f1459,plain,(
% 22.30/3.34    ( ! [X26,X27] : (k2_xboole_0(k4_xboole_0(X26,X27),X27) = k2_xboole_0(k4_xboole_0(X27,k4_xboole_0(X26,X27)),k4_xboole_0(k2_xboole_0(X26,k4_xboole_0(X26,X27)),X27))) )),
% 22.30/3.34    inference(superposition,[],[f1105,f20])).
% 22.30/3.34  fof(f5300,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(X66,X65)),X65)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5299,f17])).
% 22.30/3.34  fof(f5299,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(X66,k4_xboole_0(X65,X66))),X65)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5298,f131])).
% 22.30/3.34  fof(f5298,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(X66,k4_xboole_0(X65,k4_xboole_0(X66,X66)))),X65)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5297,f15])).
% 22.30/3.34  fof(f5297,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X66,k2_xboole_0(k4_xboole_0(X65,k4_xboole_0(X66,X66)),X66)),X65)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5296,f5246])).
% 22.30/3.34  fof(f5246,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k4_xboole_0(X2,X2))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5245,f59])).
% 22.30/3.34  fof(f5245,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X2)))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5154,f18])).
% 22.30/3.34  fof(f5154,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X2))))) )),
% 22.30/3.34    inference(superposition,[],[f4360,f18])).
% 22.30/3.34  fof(f5296,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(X65,k2_xboole_0(k4_xboole_0(X66,X66),k4_xboole_0(X65,k4_xboole_0(X66,X66)))),X65)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5295,f18])).
% 22.30/3.34  fof(f5295,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,X66))) = k2_xboole_0(k4_xboole_0(k4_xboole_0(X65,k4_xboole_0(X66,X66)),k4_xboole_0(X65,k4_xboole_0(X66,X66))),X65)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5189,f133])).
% 22.30/3.34  fof(f133,plain,(
% 22.30/3.34    ( ! [X14,X15,X13,X16] : (k2_xboole_0(X13,k4_xboole_0(X16,k4_xboole_0(X14,k2_xboole_0(X13,X15)))) = k2_xboole_0(X13,k4_xboole_0(X16,k4_xboole_0(X14,X15)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f124,f59])).
% 22.30/3.34  fof(f124,plain,(
% 22.30/3.34    ( ! [X14,X15,X13,X16] : (k2_xboole_0(X13,k4_xboole_0(X16,k4_xboole_0(X14,k2_xboole_0(X13,X15)))) = k2_xboole_0(X13,k4_xboole_0(X16,k2_xboole_0(X13,k4_xboole_0(X14,X15))))) )),
% 22.30/3.34    inference(superposition,[],[f59,f59])).
% 22.30/3.34  fof(f5189,plain,(
% 22.30/3.34    ( ! [X66,X65] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X65,k4_xboole_0(X66,X66)),k4_xboole_0(X65,k4_xboole_0(X66,X66))),X65) = k2_xboole_0(X65,k4_xboole_0(X65,k4_xboole_0(X66,k2_xboole_0(X65,X66))))) )),
% 22.30/3.34    inference(superposition,[],[f390,f4360])).
% 22.30/3.34  fof(f390,plain,(
% 22.30/3.34    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X12),X11) = k2_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 22.30/3.34    inference(superposition,[],[f363,f15])).
% 22.30/3.34  fof(f363,plain,(
% 22.30/3.34    ( ! [X4,X5] : (k2_xboole_0(X5,k4_xboole_0(X4,X4)) = k2_xboole_0(X5,k4_xboole_0(X5,k4_xboole_0(X5,X4)))) )),
% 22.30/3.34    inference(superposition,[],[f131,f22])).
% 22.30/3.34  fof(f22,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 22.30/3.34    inference(definition_unfolding,[],[f14,f16,f16])).
% 22.30/3.34  fof(f14,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 22.30/3.34    inference(cnf_transformation,[],[f2])).
% 22.30/3.34  fof(f2,axiom,(
% 22.30/3.34    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 22.30/3.34    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 22.30/3.34  fof(f2050,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k4_xboole_0(X19,k4_xboole_0(X20,X20)) = k2_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,X20)))) )),
% 22.30/3.34    inference(superposition,[],[f765,f700])).
% 22.30/3.34  fof(f700,plain,(
% 22.30/3.34    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X8)) = k2_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 22.30/3.34    inference(superposition,[],[f640,f15])).
% 22.30/3.34  fof(f765,plain,(
% 22.30/3.34    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(X9,k2_xboole_0(X9,k4_xboole_0(X9,X10)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f710,f15])).
% 22.30/3.34  fof(f710,plain,(
% 22.30/3.34    ( ! [X10,X9] : (k2_xboole_0(X9,k4_xboole_0(X9,X10)) = k2_xboole_0(X9,k2_xboole_0(k4_xboole_0(X9,X10),X9))) )),
% 22.30/3.34    inference(superposition,[],[f440,f640])).
% 22.30/3.34  fof(f440,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f439,f30])).
% 22.30/3.34  fof(f439,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(X4,X3)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f438,f17])).
% 22.30/3.34  fof(f438,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f437,f18])).
% 22.30/3.34  fof(f437,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X4)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f396,f377])).
% 22.30/3.34  fof(f377,plain,(
% 22.30/3.34    ( ! [X12,X10,X13,X11] : (k2_xboole_0(X10,k4_xboole_0(X13,k4_xboole_0(X11,k4_xboole_0(X12,X10)))) = k2_xboole_0(X10,k4_xboole_0(X13,k4_xboole_0(X11,X12)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f370,f59])).
% 22.30/3.34  fof(f370,plain,(
% 22.30/3.34    ( ! [X12,X10,X13,X11] : (k2_xboole_0(X10,k4_xboole_0(X13,k4_xboole_0(X11,k4_xboole_0(X12,X10)))) = k2_xboole_0(X10,k4_xboole_0(X13,k2_xboole_0(X10,k4_xboole_0(X11,X12))))) )),
% 22.30/3.34    inference(superposition,[],[f59,f131])).
% 22.30/3.34  fof(f396,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,X4))) = k2_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3))))) )),
% 22.30/3.34    inference(superposition,[],[f363,f22])).
% 22.30/3.34  fof(f4360,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f2289,f4194])).
% 22.30/3.34  fof(f4194,plain,(
% 22.30/3.34    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),X6) = k4_xboole_0(X7,k2_xboole_0(X6,X7))) )),
% 22.30/3.34    inference(superposition,[],[f2290,f22])).
% 22.30/3.34  fof(f2290,plain,(
% 22.30/3.34    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X5) = k4_xboole_0(X4,k2_xboole_0(X5,X4))) )),
% 22.30/3.34    inference(superposition,[],[f37,f1509])).
% 22.30/3.34  fof(f37,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 22.30/3.34    inference(superposition,[],[f18,f22])).
% 22.30/3.34  fof(f2289,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X1))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 22.30/3.34    inference(superposition,[],[f37,f640])).
% 22.30/3.34  fof(f10564,plain,(
% 22.30/3.34    ( ! [X17,X16] : (k4_xboole_0(X17,k2_xboole_0(X17,k4_xboole_0(X17,X16))) = k4_xboole_0(X16,k2_xboole_0(X16,k4_xboole_0(X17,X17)))) )),
% 22.30/3.34    inference(superposition,[],[f65,f5302])).
% 22.30/3.34  fof(f65,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2)))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f43,f59])).
% 22.30/3.34  fof(f43,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f34,f18])).
% 22.30/3.34  fof(f34,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2)))) )),
% 22.30/3.34    inference(superposition,[],[f22,f18])).
% 22.30/3.34  fof(f6349,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k2_xboole_0(X19,k4_xboole_0(X19,X20))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f6348,f2741])).
% 22.30/3.34  fof(f2741,plain,(
% 22.30/3.34    ( ! [X2,X3,X1] : (k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(X3,k2_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f2664,f765])).
% 22.30/3.34  fof(f2664,plain,(
% 22.30/3.34    ( ! [X2,X3,X1] : (k4_xboole_0(X3,k2_xboole_0(X1,k2_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(X3,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 22.30/3.34    inference(superposition,[],[f32,f1296])).
% 22.30/3.34  fof(f1296,plain,(
% 22.30/3.34    ( ! [X4,X5] : (k2_xboole_0(k2_xboole_0(X4,X4),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X5,X4))) )),
% 22.30/3.34    inference(superposition,[],[f756,f171])).
% 22.30/3.34  fof(f756,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X0))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f755,f17])).
% 22.30/3.34  fof(f755,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X0)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f705,f15])).
% 22.30/3.34  fof(f705,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X0),X0))) )),
% 22.30/3.34    inference(superposition,[],[f23,f640])).
% 22.30/3.34  fof(f32,plain,(
% 22.30/3.34    ( ! [X2,X0,X3,X1] : (k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f31,f18])).
% 22.30/3.34  fof(f31,plain,(
% 22.30/3.34    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f29,f18])).
% 22.30/3.34  fof(f29,plain,(
% 22.30/3.34    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) )),
% 22.30/3.34    inference(superposition,[],[f18,f18])).
% 22.30/3.34  fof(f6348,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,X19))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f6347,f4017])).
% 22.30/3.34  fof(f4017,plain,(
% 22.30/3.34    ( ! [X39,X37,X38] : (k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X38,k2_xboole_0(X37,X37)))) = k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X38,X37)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f3938,f23])).
% 22.30/3.34  fof(f3938,plain,(
% 22.30/3.34    ( ! [X39,X37,X38] : (k4_xboole_0(X37,k4_xboole_0(X39,k4_xboole_0(X38,k2_xboole_0(X37,X37)))) = k2_xboole_0(k4_xboole_0(X37,X39),k4_xboole_0(X37,k4_xboole_0(X37,k4_xboole_0(X38,X37))))) )),
% 22.30/3.34    inference(superposition,[],[f23,f2230])).
% 22.30/3.34  fof(f2230,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f2229,f756])).
% 22.30/3.34  fof(f2229,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f2132,f17])).
% 22.30/3.34  fof(f2132,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X0)))) )),
% 22.30/3.34    inference(superposition,[],[f23,f1005])).
% 22.30/3.34  fof(f1005,plain,(
% 22.30/3.34    ( ! [X15,X16] : (k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X16,X16)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1004,f17])).
% 22.30/3.34  fof(f1004,plain,(
% 22.30/3.34    ( ! [X15,X16] : (k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X16,k4_xboole_0(X16,X16))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f952,f18])).
% 22.30/3.34  fof(f952,plain,(
% 22.30/3.34    ( ! [X15,X16] : (k2_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(k4_xboole_0(X16,X16),k4_xboole_0(X16,X16)))) )),
% 22.30/3.34    inference(superposition,[],[f700,f440])).
% 22.30/3.34  fof(f6347,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,k2_xboole_0(X19,X19)))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f6346,f22])).
% 22.30/3.34  fof(f6346,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k2_xboole_0(X19,k4_xboole_0(X19,X20)) = k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),X19)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f6196,f131])).
% 22.30/3.34  fof(f6196,plain,(
% 22.30/3.34    ( ! [X19,X20] : (k2_xboole_0(k4_xboole_0(X19,k4_xboole_0(X20,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X19,X19)),X19))) = k2_xboole_0(X19,k4_xboole_0(X19,k4_xboole_0(X20,X19)))) )),
% 22.30/3.34    inference(superposition,[],[f45,f2230])).
% 22.30/3.34  fof(f45,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f38,f15])).
% 22.30/3.34  fof(f38,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 22.30/3.34    inference(superposition,[],[f17,f22])).
% 22.30/3.34  fof(f8209,plain,(
% 22.30/3.34    ( ! [X109,X110] : (k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(k4_xboole_0(X109,k4_xboole_0(X110,X109)),k4_xboole_0(X109,k2_xboole_0(X110,X109)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f8208,f6621])).
% 22.30/3.34  fof(f6621,plain,(
% 22.30/3.34    ( ! [X2,X3,X1] : (k4_xboole_0(X3,k2_xboole_0(X1,X2)) = k4_xboole_0(X3,k2_xboole_0(X1,k2_xboole_0(X2,X2)))) )),
% 22.30/3.34    inference(superposition,[],[f32,f6105])).
% 22.30/3.34  fof(f6105,plain,(
% 22.30/3.34    ( ! [X61,X60] : (k2_xboole_0(X61,X60) = k2_xboole_0(k2_xboole_0(X61,X60),X60)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f6083,f5956])).
% 22.30/3.34  fof(f5956,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X4))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f1406,f5950])).
% 22.30/3.34  fof(f5950,plain,(
% 22.30/3.34    ( ! [X47,X48] : (k2_xboole_0(X47,X48) = k2_xboole_0(k2_xboole_0(X48,X47),k2_xboole_0(X47,X48))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5949,f5677])).
% 22.30/3.34  fof(f5677,plain,(
% 22.30/3.34    ( ! [X21,X20] : (k2_xboole_0(X21,X20) = k2_xboole_0(X21,k2_xboole_0(X20,X21))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5676,f17])).
% 22.30/3.34  fof(f5676,plain,(
% 22.30/3.34    ( ! [X21,X20] : (k2_xboole_0(X21,k4_xboole_0(X20,X21)) = k2_xboole_0(X21,k2_xboole_0(X20,X21))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5573,f17])).
% 22.30/3.34  fof(f5573,plain,(
% 22.30/3.34    ( ! [X21,X20] : (k2_xboole_0(X21,k4_xboole_0(X20,X21)) = k2_xboole_0(X21,k4_xboole_0(k2_xboole_0(X20,X21),X21))) )),
% 22.30/3.34    inference(superposition,[],[f5320,f20])).
% 22.30/3.34  fof(f5320,plain,(
% 22.30/3.34    ( ! [X17,X18] : (k2_xboole_0(X18,X17) = k2_xboole_0(X18,k2_xboole_0(X17,k4_xboole_0(X18,X18)))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f1079,f5302])).
% 22.30/3.34  fof(f1079,plain,(
% 22.30/3.34    ( ! [X17,X18] : (k2_xboole_0(X18,X17) = k2_xboole_0(X18,k4_xboole_0(X17,k4_xboole_0(X18,X18)))) )),
% 22.30/3.34    inference(superposition,[],[f764,f700])).
% 22.30/3.34  fof(f5949,plain,(
% 22.30/3.34    ( ! [X47,X48] : (k2_xboole_0(X47,k2_xboole_0(X48,X47)) = k2_xboole_0(k2_xboole_0(X48,X47),k2_xboole_0(X47,X48))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5886,f15])).
% 22.30/3.34  fof(f5886,plain,(
% 22.30/3.34    ( ! [X47,X48] : (k2_xboole_0(k2_xboole_0(X48,X47),X47) = k2_xboole_0(k2_xboole_0(X48,X47),k2_xboole_0(X47,X48))) )),
% 22.30/3.34    inference(superposition,[],[f5677,f5677])).
% 22.30/3.34  fof(f1406,plain,(
% 22.30/3.34    ( ! [X4,X3] : (k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)),k2_xboole_0(k2_xboole_0(X4,X3),k2_xboole_0(X3,X4)))) )),
% 22.30/3.34    inference(superposition,[],[f1398,f171])).
% 22.30/3.34  fof(f1398,plain,(
% 22.30/3.34    ( ! [X36] : (k2_xboole_0(X36,X36) = k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1397,f17])).
% 22.30/3.34  fof(f1397,plain,(
% 22.30/3.34    ( ! [X36] : (k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) = k2_xboole_0(X36,k4_xboole_0(X36,X36))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1396,f131])).
% 22.30/3.34  fof(f1396,plain,(
% 22.30/3.34    ( ! [X36] : (k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) = k2_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X36,X36)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1395,f995])).
% 22.30/3.34  fof(f995,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X0)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f938,f17])).
% 22.30/3.34  fof(f938,plain,(
% 22.30/3.34    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) = k4_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))))) )),
% 22.30/3.34    inference(superposition,[],[f700,f18])).
% 22.30/3.34  fof(f1395,plain,(
% 22.30/3.34    ( ! [X36] : (k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36)) = k4_xboole_0(X36,k4_xboole_0(X36,k2_xboole_0(X36,X36)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1370,f18])).
% 22.30/3.34  fof(f1370,plain,(
% 22.30/3.34    ( ! [X36] : (k4_xboole_0(X36,k4_xboole_0(k4_xboole_0(X36,X36),X36)) = k2_xboole_0(k2_xboole_0(X36,X36),k2_xboole_0(X36,X36))) )),
% 22.30/3.34    inference(superposition,[],[f756,f1295])).
% 22.30/3.34  fof(f1295,plain,(
% 22.30/3.34    ( ! [X0] : (k2_xboole_0(X0,X0) = k4_xboole_0(X0,k4_xboole_0(X0,X0))) )),
% 22.30/3.34    inference(superposition,[],[f756,f1158])).
% 22.30/3.34  fof(f1158,plain,(
% 22.30/3.34    ( ! [X7] : (k2_xboole_0(X7,X7) = k2_xboole_0(k4_xboole_0(X7,X7),k2_xboole_0(X7,X7))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1157,f17])).
% 22.30/3.34  fof(f1157,plain,(
% 22.30/3.34    ( ! [X7] : (k2_xboole_0(X7,k4_xboole_0(X7,X7)) = k2_xboole_0(k4_xboole_0(X7,X7),k2_xboole_0(X7,X7))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1144,f15])).
% 22.30/3.34  fof(f1144,plain,(
% 22.30/3.34    ( ! [X7] : (k2_xboole_0(k4_xboole_0(X7,X7),X7) = k2_xboole_0(k4_xboole_0(X7,X7),k2_xboole_0(X7,X7))) )),
% 22.30/3.34    inference(superposition,[],[f764,f1079])).
% 22.30/3.34  fof(f6083,plain,(
% 22.30/3.34    ( ! [X61,X60] : (k2_xboole_0(k2_xboole_0(X61,X60),X60) = k2_xboole_0(k2_xboole_0(X61,X60),k2_xboole_0(X61,X60))) )),
% 22.30/3.34    inference(superposition,[],[f5677,f5787])).
% 22.30/3.34  fof(f5787,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 22.30/3.34    inference(superposition,[],[f5619,f15])).
% 22.30/3.34  fof(f5619,plain,(
% 22.30/3.34    ( ! [X19,X18] : (k2_xboole_0(X19,X18) = k2_xboole_0(X19,k2_xboole_0(X19,X18))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5618,f17])).
% 22.30/3.34  fof(f5618,plain,(
% 22.30/3.34    ( ! [X19,X18] : (k2_xboole_0(X19,k4_xboole_0(X18,X19)) = k2_xboole_0(X19,k2_xboole_0(X19,X18))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5572,f17])).
% 22.30/3.34  fof(f5572,plain,(
% 22.30/3.34    ( ! [X19,X18] : (k2_xboole_0(X19,k4_xboole_0(X18,X19)) = k2_xboole_0(X19,k4_xboole_0(k2_xboole_0(X19,X18),X19))) )),
% 22.30/3.34    inference(superposition,[],[f5320,f55])).
% 22.30/3.34  fof(f8208,plain,(
% 22.30/3.34    ( ! [X109,X110] : (k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(k4_xboole_0(X109,k4_xboole_0(X110,X109)),k4_xboole_0(X109,k2_xboole_0(X110,k2_xboole_0(X109,X109))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f8117,f18])).
% 22.30/3.34  fof(f8117,plain,(
% 22.30/3.34    ( ! [X109,X110] : (k4_xboole_0(X109,k4_xboole_0(X110,X109)) = k2_xboole_0(k4_xboole_0(X109,k4_xboole_0(X110,X109)),k4_xboole_0(k4_xboole_0(X109,X110),k2_xboole_0(X109,X109)))) )),
% 22.30/3.34    inference(superposition,[],[f6131,f1296])).
% 22.30/3.34  fof(f6131,plain,(
% 22.30/3.34    ( ! [X57,X58] : (k2_xboole_0(X58,X57) = k2_xboole_0(k2_xboole_0(X58,X57),k4_xboole_0(X57,X58))) )),
% 22.30/3.34    inference(superposition,[],[f5995,f1509])).
% 22.30/3.34  fof(f5995,plain,(
% 22.30/3.34    ( ! [X50,X49] : (k2_xboole_0(X49,X50) = k2_xboole_0(k2_xboole_0(X49,X50),X49)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5887,f5956])).
% 22.30/3.34  fof(f5887,plain,(
% 22.30/3.34    ( ! [X50,X49] : (k2_xboole_0(k2_xboole_0(X49,X50),X49) = k2_xboole_0(k2_xboole_0(X49,X50),k2_xboole_0(X49,X50))) )),
% 22.30/3.34    inference(superposition,[],[f5677,f5619])).
% 22.30/3.34  fof(f5405,plain,(
% 22.30/3.34    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X9,X10))) = k4_xboole_0(k2_xboole_0(X9,X9),X10)) )),
% 22.30/3.34    inference(backward_demodulation,[],[f638,f5403])).
% 22.30/3.34  fof(f5403,plain,(
% 22.30/3.34    ( ! [X24,X23] : (k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X23)) = k4_xboole_0(k2_xboole_0(X23,X23),X24)) )),
% 22.30/3.34    inference(forward_demodulation,[],[f5328,f1381])).
% 22.30/3.34  fof(f1381,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X0),X1) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1380,f20])).
% 22.30/3.34  fof(f1380,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X0)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1379,f59])).
% 22.30/3.34  fof(f1379,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X0))))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1378,f18])).
% 22.30/3.34  fof(f1378,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X0)))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f1346,f131])).
% 22.30/3.34  fof(f1346,plain,(
% 22.30/3.34    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))))) )),
% 22.30/3.34    inference(superposition,[],[f1295,f18])).
% 22.30/3.34  fof(f5328,plain,(
% 22.30/3.34    ( ! [X24,X23] : (k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X23)) = k4_xboole_0(X23,k2_xboole_0(X24,k4_xboole_0(X23,X23)))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f2746,f5302])).
% 22.30/3.34  fof(f2746,plain,(
% 22.30/3.34    ( ! [X24,X23] : (k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X23,X23))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,X23))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f1365,f2745])).
% 22.30/3.34  fof(f2745,plain,(
% 22.30/3.34    ( ! [X21,X19,X20] : (k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,X19))) = k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,X19))) )),
% 22.30/3.34    inference(forward_demodulation,[],[f2743,f30])).
% 22.30/3.34  fof(f2743,plain,(
% 22.30/3.34    ( ! [X21,X19,X20] : (k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,X19))) = k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,k4_xboole_0(X19,X20))))) )),
% 22.30/3.34    inference(backward_demodulation,[],[f1305,f2741])).
% 22.30/3.34  fof(f1305,plain,(
% 22.30/3.34    ( ! [X21,X19,X20] : (k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k2_xboole_0(X19,X19))) = k2_xboole_0(k4_xboole_0(X19,X20),k4_xboole_0(X21,k4_xboole_0(X19,k4_xboole_0(X20,X19))))) )),
% 22.30/3.34    inference(superposition,[],[f59,f756])).
% 22.30/3.34  fof(f1365,plain,(
% 22.30/3.34    ( ! [X24,X23] : (k4_xboole_0(X23,k4_xboole_0(X24,k4_xboole_0(X23,X23))) = k2_xboole_0(k4_xboole_0(X23,X24),k4_xboole_0(X23,k2_xboole_0(X23,X23)))) )),
% 22.30/3.34    inference(superposition,[],[f23,f1295])).
% 22.30/3.35  fof(f638,plain,(
% 22.30/3.35    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),k4_xboole_0(X9,X9)) = k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X9,X10)))) )),
% 22.30/3.35    inference(superposition,[],[f23,f131])).
% 22.30/3.35  fof(f18167,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(X25,k2_xboole_0(X26,k4_xboole_0(X26,X25))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f18166,f5619])).
% 22.30/3.35  fof(f18166,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(X25,k2_xboole_0(X26,k2_xboole_0(X26,k4_xboole_0(X26,X25)))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f18149,f842])).
% 22.30/3.35  fof(f842,plain,(
% 22.30/3.35    ( ! [X10,X8,X11,X9] : (k4_xboole_0(X11,k2_xboole_0(X8,k2_xboole_0(X9,X10))) = k4_xboole_0(X11,k2_xboole_0(X10,k2_xboole_0(X9,X8)))) )),
% 22.30/3.35    inference(superposition,[],[f32,f171])).
% 22.30/3.35  fof(f18149,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(X25,k2_xboole_0(k4_xboole_0(X26,X25),k2_xboole_0(X26,X26))))) )),
% 22.30/3.35    inference(backward_demodulation,[],[f1942,f18023])).
% 22.30/3.35  fof(f18023,plain,(
% 22.30/3.35    ( ! [X28,X26,X27] : (k4_xboole_0(k2_xboole_0(X26,k4_xboole_0(X26,X27)),X28) = k4_xboole_0(X26,k2_xboole_0(k4_xboole_0(X27,X26),X28))) )),
% 22.30/3.35    inference(superposition,[],[f18,f10945])).
% 22.30/3.35  fof(f1942,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(X26,X25) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X25,X26)),k2_xboole_0(X26,X26)))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f1941,f17])).
% 22.30/3.35  fof(f1941,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X25,k4_xboole_0(X25,X26)),k2_xboole_0(X26,X26)))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f1940,f75])).
% 22.30/3.35  fof(f1940,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(k4_xboole_0(X25,X26),X25),k2_xboole_0(X26,X26)))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f1888,f18])).
% 22.30/3.35  fof(f1888,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(X26,k4_xboole_0(X25,X26)) = k2_xboole_0(X26,k4_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X25,X26),X25),X26),X26))) )),
% 22.30/3.35    inference(superposition,[],[f1110,f55])).
% 22.30/3.35  fof(f1110,plain,(
% 22.30/3.35    ( ! [X24,X23] : (k2_xboole_0(X24,X23) = k2_xboole_0(X24,k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X23,X24)),X24))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f1109,f17])).
% 22.30/3.35  fof(f1109,plain,(
% 22.30/3.35    ( ! [X24,X23] : (k2_xboole_0(X24,k4_xboole_0(X23,X24)) = k2_xboole_0(X24,k4_xboole_0(k2_xboole_0(X23,k4_xboole_0(X23,X24)),X24))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f1080,f75])).
% 22.30/3.35  fof(f1080,plain,(
% 22.30/3.35    ( ! [X24,X23] : (k2_xboole_0(X24,k4_xboole_0(X23,X24)) = k2_xboole_0(X24,k4_xboole_0(k2_xboole_0(k4_xboole_0(X23,X24),X23),X24))) )),
% 22.30/3.35    inference(superposition,[],[f764,f55])).
% 22.30/3.35  fof(f44864,plain,(
% 22.30/3.35    ( ! [X61,X59,X60] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X59,X59),X60),k4_xboole_0(X61,X59)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X59,X59),X60),k4_xboole_0(X61,k4_xboole_0(X60,k4_xboole_0(X60,X59))))) )),
% 22.30/3.35    inference(superposition,[],[f131,f34383])).
% 22.30/3.35  fof(f34383,plain,(
% 22.30/3.35    ( ! [X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X18,k4_xboole_0(k2_xboole_0(X18,X18),X17))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f34382,f20])).
% 22.30/3.35  fof(f34382,plain,(
% 22.30/3.35    ( ! [X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,X18)) = k4_xboole_0(X18,k2_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,X17)))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f34139,f4506])).
% 22.30/3.35  fof(f4506,plain,(
% 22.30/3.35    ( ! [X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(k2_xboole_0(X15,X15),X16))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f4505,f1381])).
% 22.30/3.35  fof(f4505,plain,(
% 22.30/3.35    ( ! [X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X15,k2_xboole_0(X16,k4_xboole_0(X15,X15))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f4504,f65])).
% 22.30/3.35  fof(f4504,plain,(
% 22.30/3.35    ( ! [X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X15,X16)) = k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,X16))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f4253,f4374])).
% 22.30/3.35  fof(f4374,plain,(
% 22.30/3.35    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X2,k2_xboole_0(X3,X2)))) )),
% 22.30/3.35    inference(backward_demodulation,[],[f3373,f4360])).
% 22.30/3.35  fof(f3373,plain,(
% 22.30/3.35    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X2)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2))))) )),
% 22.30/3.35    inference(backward_demodulation,[],[f2939,f3352])).
% 22.30/3.35  fof(f3352,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k4_xboole_0(X25,k4_xboole_0(X25,X26)) = k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X25,X25)))) )),
% 22.30/3.35    inference(backward_demodulation,[],[f2563,f3299])).
% 22.30/3.35  fof(f3299,plain,(
% 22.30/3.35    ( ! [X14,X13] : (k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,k4_xboole_0(X13,X14)))) )),
% 22.30/3.35    inference(superposition,[],[f2047,f23])).
% 22.30/3.35  fof(f2047,plain,(
% 22.30/3.35    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X14,X14),X13) = k2_xboole_0(X13,k2_xboole_0(k4_xboole_0(X14,X14),X13))) )),
% 22.30/3.35    inference(superposition,[],[f765,f390])).
% 22.30/3.35  fof(f2563,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X25,X25)))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2562,f1295])).
% 22.30/3.35  fof(f2562,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X25,k4_xboole_0(X25,X25))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2561,f2295])).
% 22.30/3.35  fof(f2295,plain,(
% 22.30/3.35    ( ! [X19,X17,X18] : (k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X17)),k4_xboole_0(X17,k4_xboole_0(X17,X19))) = k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(X18,X19)))) )),
% 22.30/3.35    inference(superposition,[],[f37,f23])).
% 22.30/3.35  fof(f2561,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X26,k4_xboole_0(X26,k4_xboole_0(X25,X25))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2387,f632])).
% 22.30/3.35  fof(f632,plain,(
% 22.30/3.35    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X6,X5)) = k2_xboole_0(k4_xboole_0(X4,X6),k4_xboole_0(X5,k4_xboole_0(X5,X4)))) )),
% 22.30/3.35    inference(superposition,[],[f23,f22])).
% 22.30/3.35  fof(f2387,plain,(
% 22.30/3.35    ( ! [X26,X25] : (k2_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(k4_xboole_0(X25,k4_xboole_0(X25,X26)),k4_xboole_0(X26,k2_xboole_0(k4_xboole_0(X26,X25),k4_xboole_0(X25,k4_xboole_0(X25,X26)))))) )),
% 22.30/3.35    inference(superposition,[],[f1295,f37])).
% 22.30/3.35  fof(f2939,plain,(
% 22.30/3.35    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X3,X3))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X3,X3))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2938,f18])).
% 22.30/3.35  fof(f2938,plain,(
% 22.30/3.35    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X3)) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X3)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2937,f23])).
% 22.30/3.35  fof(f2937,plain,(
% 22.30/3.35    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X2,X2))))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2899,f632])).
% 22.30/3.35  fof(f2899,plain,(
% 22.30/3.35    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X2,k4_xboole_0(X2,X3))),k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,k4_xboole_0(X2,X3)))))) )),
% 22.30/3.35    inference(superposition,[],[f2869,f37])).
% 22.30/3.35  fof(f2869,plain,(
% 22.30/3.35    ( ! [X0] : (k2_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2868,f17])).
% 22.30/3.35  fof(f2868,plain,(
% 22.30/3.35    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,X0)) = k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X0,X0)),k4_xboole_0(X0,X0))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f2804,f15])).
% 22.30/3.35  fof(f2804,plain,(
% 22.30/3.35    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X0),X0),k4_xboole_0(X0,X0))) )),
% 22.30/3.35    inference(superposition,[],[f1457,f55])).
% 22.30/3.35  fof(f1457,plain,(
% 22.30/3.35    ( ! [X19,X18] : (k2_xboole_0(X18,X19) = k2_xboole_0(k4_xboole_0(X19,X18),k4_xboole_0(X18,k4_xboole_0(X19,X19)))) )),
% 22.30/3.35    inference(superposition,[],[f1105,f700])).
% 22.30/3.35  fof(f4253,plain,(
% 22.30/3.35    ( ! [X15,X16] : (k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X15,X16)))) = k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X16,k2_xboole_0(X15,X16)))) )),
% 22.30/3.35    inference(superposition,[],[f22,f2290])).
% 22.30/3.35  fof(f34139,plain,(
% 22.30/3.35    ( ! [X17,X18] : (k4_xboole_0(X18,k2_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X18,X17))) = k4_xboole_0(X17,k4_xboole_0(k2_xboole_0(X17,X17),X18))) )),
% 22.30/3.35    inference(superposition,[],[f65,f10753])).
% 22.30/3.35  fof(f10753,plain,(
% 22.30/3.35    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X12),X13) = k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X13,X12)))) )),
% 22.30/3.35    inference(forward_demodulation,[],[f10562,f1381])).
% 22.30/3.35  fof(f10562,plain,(
% 22.30/3.35    ( ! [X12,X13] : (k4_xboole_0(X12,k2_xboole_0(X13,k4_xboole_0(X12,X12))) = k4_xboole_0(X12,k4_xboole_0(X13,k4_xboole_0(X13,X12)))) )),
% 22.30/3.35    inference(superposition,[],[f65,f22])).
% 22.30/3.35  fof(f34149,plain,(
% 22.30/3.35    ( ! [X54,X52,X53] : (k4_xboole_0(k2_xboole_0(X54,X52),k4_xboole_0(X53,k4_xboole_0(X53,X52))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X52,X52),X53),k4_xboole_0(X54,k4_xboole_0(X53,k4_xboole_0(X53,X52))))) )),
% 22.30/3.35    inference(superposition,[],[f55,f10753])).
% 22.30/3.35  fof(f27,plain,(
% 22.30/3.35    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 22.30/3.35    inference(avatar_component_clause,[],[f25])).
% 22.30/3.35  fof(f25,plain,(
% 22.30/3.35    spl2_1 <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 22.30/3.35    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 22.30/3.35  fof(f28,plain,(
% 22.30/3.35    ~spl2_1),
% 22.30/3.35    inference(avatar_split_clause,[],[f21,f25])).
% 22.30/3.35  fof(f21,plain,(
% 22.30/3.35    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 22.30/3.35    inference(definition_unfolding,[],[f13,f16])).
% 22.30/3.35  fof(f13,plain,(
% 22.30/3.35    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 22.30/3.35    inference(cnf_transformation,[],[f12])).
% 22.30/3.35  fof(f12,plain,(
% 22.30/3.35    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 22.30/3.35    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 22.30/3.35  fof(f11,plain,(
% 22.30/3.35    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 22.30/3.35    introduced(choice_axiom,[])).
% 22.30/3.35  fof(f10,plain,(
% 22.30/3.35    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 22.30/3.35    inference(ennf_transformation,[],[f9])).
% 22.30/3.35  fof(f9,negated_conjecture,(
% 22.30/3.35    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 22.30/3.35    inference(negated_conjecture,[],[f8])).
% 22.30/3.35  fof(f8,conjecture,(
% 22.30/3.35    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 22.30/3.35    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 22.30/3.35  % SZS output end Proof for theBenchmark
% 22.30/3.35  % (7486)------------------------------
% 22.30/3.35  % (7486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.30/3.35  % (7486)Termination reason: Refutation
% 22.30/3.35  
% 22.30/3.35  % (7486)Memory used [KB]: 69721
% 22.30/3.35  % (7486)Time elapsed: 2.737 s
% 22.30/3.35  % (7486)------------------------------
% 22.30/3.35  % (7486)------------------------------
% 22.30/3.35  % (7249)Success in time 2.981 s
%------------------------------------------------------------------------------
