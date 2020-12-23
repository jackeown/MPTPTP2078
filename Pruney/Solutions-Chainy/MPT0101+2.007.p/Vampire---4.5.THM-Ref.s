%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:52 EST 2020

% Result     : Theorem 9.34s
% Output     : Refutation 9.34s
% Verified   : 
% Statistics : Number of formulae       :  140 (13656 expanded)
%              Number of leaves         :   10 (4804 expanded)
%              Depth                    :   36
%              Number of atoms          :  141 (13657 expanded)
%              Number of equality atoms :  140 (13656 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28115,f3658])).

fof(f3658,plain,(
    ! [X10,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X10,X9),X9) ),
    inference(forward_demodulation,[],[f3594,f15])).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f3594,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(k2_xboole_0(X9,X10),k1_xboole_0) ),
    inference(superposition,[],[f3285,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f3285,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3284,f2990])).

fof(f2990,plain,(
    ! [X4,X5] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f276,f2862])).

fof(f2862,plain,(
    ! [X2,X1] : k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X1),X1)) = X2 ),
    inference(superposition,[],[f2834,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2834,plain,(
    ! [X39,X38] : k2_xboole_0(X39,k4_xboole_0(k2_xboole_0(X38,X39),X38)) = X39 ),
    inference(forward_demodulation,[],[f2741,f207])).

fof(f207,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f122,f192])).

fof(f192,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f54,f191])).

fof(f191,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0)) = X1 ),
    inference(forward_demodulation,[],[f187,f15])).

fof(f187,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f27,f167])).

fof(f167,plain,(
    ! [X6] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(backward_demodulation,[],[f95,f166])).

fof(f166,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f165,f29])).

fof(f29,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f22,f15])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f165,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f164,f94])).

fof(f94,plain,(
    ! [X4,X3] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f82,f19])).

fof(f82,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f54,f22])).

fof(f164,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,X0)) ),
    inference(forward_demodulation,[],[f147,f54])).

fof(f147,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f102,f54])).

fof(f102,plain,(
    ! [X7] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f25,f54])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f95,plain,(
    ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(X6,X6)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(forward_demodulation,[],[f86,f17])).

fof(f86,plain,(
    ! [X6] : k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(X6,X6)) ),
    inference(superposition,[],[f19,f54])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f22,f15])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f15])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f18,f18])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f122,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(superposition,[],[f108,f17])).

fof(f108,plain,(
    ! [X9] : k2_xboole_0(k4_xboole_0(X9,X9),X9) = X9 ),
    inference(superposition,[],[f25,f15])).

fof(f2741,plain,(
    ! [X39,X38] : k2_xboole_0(X39,k1_xboole_0) = k2_xboole_0(X39,k4_xboole_0(k2_xboole_0(X38,X39),X38)) ),
    inference(superposition,[],[f31,f192])).

fof(f31,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f19,f22])).

fof(f276,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f202,f22])).

fof(f202,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f94,f191])).

fof(f3284,plain,(
    ! [X12,X13] : k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f3196,f15])).

fof(f3196,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k1_xboole_0) ),
    inference(superposition,[],[f24,f2990])).

fof(f28115,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    inference(forward_demodulation,[],[f28114,f323])).

fof(f323,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,X12)) = X11 ),
    inference(forward_demodulation,[],[f317,f207])).

fof(f317,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(X11,k1_xboole_0) ),
    inference(superposition,[],[f19,f274])).

fof(f274,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8) ),
    inference(superposition,[],[f202,f25])).

fof(f28114,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f28113,f17])).

fof(f28113,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(forward_demodulation,[],[f28112,f19])).

fof(f28112,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f27869,f17])).

fof(f27869,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f13059,f27201])).

fof(f27201,plain,(
    ! [X78,X79,X77] : k2_xboole_0(X79,k2_xboole_0(X77,X78)) = k2_xboole_0(k2_xboole_0(X78,X79),X77) ),
    inference(forward_demodulation,[],[f27173,f10536])).

fof(f10536,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(backward_demodulation,[],[f933,f10454])).

fof(f10454,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f10173,f17])).

fof(f10173,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(forward_demodulation,[],[f10041,f207])).

fof(f10041,plain,(
    ! [X6,X7] : k4_xboole_0(X7,X6) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,k1_xboole_0)) ),
    inference(superposition,[],[f5043,f22])).

fof(f5043,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) ),
    inference(forward_demodulation,[],[f5042,f15])).

fof(f5042,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k1_xboole_0) ),
    inference(forward_demodulation,[],[f5041,f391])).

fof(f391,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f282,f17])).

fof(f282,plain,(
    ! [X6,X8,X7] : k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8)) ),
    inference(forward_demodulation,[],[f278,f230])).

fof(f230,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f205,f167])).

fof(f205,plain,(
    ! [X9] : k2_xboole_0(k1_xboole_0,X9) = X9 ),
    inference(backward_demodulation,[],[f108,f192])).

fof(f278,plain,(
    ! [X6,X8,X7] : k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8)) ),
    inference(superposition,[],[f22,f202])).

fof(f5041,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X8,k2_xboole_0(X7,k2_xboole_0(X7,X8)))) ),
    inference(forward_demodulation,[],[f5040,f19])).

fof(f5040,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(k2_xboole_0(X7,X8),X7)))) ),
    inference(forward_demodulation,[],[f4866,f22])).

fof(f4866,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(k2_xboole_0(X7,X8),X7))) ),
    inference(superposition,[],[f24,f3053])).

fof(f3053,plain,(
    ! [X10,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),X9),k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f2897,f19])).

fof(f2897,plain,(
    ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X15,X14),X15),X14) ),
    inference(superposition,[],[f202,f2834])).

fof(f933,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X1)) ),
    inference(forward_demodulation,[],[f881,f15])).

fof(f881,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(k2_xboole_0(X2,X1),X1)) ),
    inference(superposition,[],[f99,f202])).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f25,f24])).

fof(f27173,plain,(
    ! [X78,X79,X77] : k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k2_xboole_0(X77,X78),k4_xboole_0(X79,k2_xboole_0(X77,X78))) ),
    inference(backward_demodulation,[],[f19743,f26978])).

fof(f26978,plain,(
    ! [X163,X164,X162] : k4_xboole_0(X164,k2_xboole_0(X162,X163)) = k4_xboole_0(k2_xboole_0(X163,X164),k2_xboole_0(X162,X163)) ),
    inference(superposition,[],[f23265,f11120])).

fof(f11120,plain,(
    ! [X154,X153] : k4_xboole_0(k2_xboole_0(X153,X154),k4_xboole_0(X153,X154)) = X154 ),
    inference(forward_demodulation,[],[f11048,f10219])).

fof(f10219,plain,(
    ! [X2,X1] : k4_xboole_0(X2,k4_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f9771,f10173])).

fof(f9771,plain,(
    ! [X2,X1] : k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X2 ),
    inference(superposition,[],[f9688,f17])).

fof(f9688,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(k2_xboole_0(X13,X12),X12)) = X12 ),
    inference(forward_demodulation,[],[f9557,f15])).

fof(f9557,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k1_xboole_0) = k4_xboole_0(X12,k4_xboole_0(k2_xboole_0(X13,X12),X12)) ),
    inference(superposition,[],[f320,f4948])).

fof(f4948,plain,(
    ! [X56,X55] : k1_xboole_0 = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56))) ),
    inference(forward_demodulation,[],[f4947,f15])).

fof(f4947,plain,(
    ! [X56,X55] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X56,k1_xboole_0),k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56))) ),
    inference(forward_demodulation,[],[f4946,f202])).

fof(f4946,plain,(
    ! [X56,X55] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X56,k4_xboole_0(X56,k2_xboole_0(X55,X56))),k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56))) ),
    inference(forward_demodulation,[],[f4819,f24])).

fof(f4819,plain,(
    ! [X56,X55] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X55,X56),k4_xboole_0(k2_xboole_0(X55,X56),X56)),k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56))) ),
    inference(superposition,[],[f3053,f1114])).

fof(f1114,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),X1) ),
    inference(forward_demodulation,[],[f1051,f15])).

fof(f1051,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f324,f202])).

fof(f324,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3 ),
    inference(backward_demodulation,[],[f72,f323])).

fof(f72,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f65,f17])).

fof(f65,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) ),
    inference(superposition,[],[f19,f24])).

fof(f320,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5))) ),
    inference(forward_demodulation,[],[f314,f15])).

fof(f314,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0) ),
    inference(superposition,[],[f24,f274])).

fof(f11048,plain,(
    ! [X154,X153] : k4_xboole_0(X154,k4_xboole_0(X153,X154)) = k4_xboole_0(k2_xboole_0(X153,X154),k4_xboole_0(X153,X154)) ),
    inference(superposition,[],[f10173,f10537])).

fof(f10537,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X2,X1),X1) ),
    inference(backward_demodulation,[],[f1114,f10454])).

fof(f23265,plain,(
    ! [X393,X395,X394] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X393,X394),X395),X393) = k4_xboole_0(X395,X393) ),
    inference(forward_demodulation,[],[f23173,f10173])).

fof(f23173,plain,(
    ! [X393,X395,X394] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X393,X394),X395),X393) = k4_xboole_0(k2_xboole_0(X393,X395),X393) ),
    inference(superposition,[],[f10173,f15020])).

fof(f15020,plain,(
    ! [X24,X23,X22] : k2_xboole_0(X22,X24) = k2_xboole_0(X22,k2_xboole_0(k4_xboole_0(X22,X23),X24)) ),
    inference(forward_demodulation,[],[f14907,f2814])).

fof(f2814,plain,(
    ! [X59,X57,X58] : k2_xboole_0(X57,X59) = k2_xboole_0(X57,k4_xboole_0(X59,k4_xboole_0(X57,X58))) ),
    inference(forward_demodulation,[],[f2724,f19])).

fof(f2724,plain,(
    ! [X59,X57,X58] : k2_xboole_0(X57,k4_xboole_0(X59,k4_xboole_0(X57,X58))) = k2_xboole_0(X57,k4_xboole_0(X59,X57)) ),
    inference(superposition,[],[f31,f609])).

fof(f609,plain,(
    ! [X10,X9] : k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9 ),
    inference(superposition,[],[f417,f323])).

fof(f417,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f284,f17])).

fof(f284,plain,(
    ! [X10,X9] : k2_xboole_0(X10,X9) = k2_xboole_0(k2_xboole_0(X10,X9),X9) ),
    inference(forward_demodulation,[],[f283,f205])).

fof(f283,plain,(
    ! [X10,X9] : k2_xboole_0(k2_xboole_0(X10,X9),X9) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X10,X9)) ),
    inference(forward_demodulation,[],[f279,f17])).

fof(f279,plain,(
    ! [X10,X9] : k2_xboole_0(k2_xboole_0(X10,X9),X9) = k2_xboole_0(k2_xboole_0(X10,X9),k1_xboole_0) ),
    inference(superposition,[],[f19,f202])).

fof(f14907,plain,(
    ! [X24,X23,X22] : k2_xboole_0(X22,k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k2_xboole_0(X22,k4_xboole_0(X24,k4_xboole_0(X22,X23))) ),
    inference(superposition,[],[f2814,f10173])).

fof(f19743,plain,(
    ! [X78,X79,X77] : k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k2_xboole_0(X77,X78),k4_xboole_0(k2_xboole_0(X78,X79),k2_xboole_0(X77,X78))) ),
    inference(forward_demodulation,[],[f19742,f15])).

fof(f19742,plain,(
    ! [X78,X79,X77] : k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X77,X78),k1_xboole_0),k4_xboole_0(k2_xboole_0(X78,X79),k2_xboole_0(X77,X78))) ),
    inference(forward_demodulation,[],[f19644,f11241])).

fof(f11241,plain,(
    ! [X14,X12,X13] : k4_xboole_0(X12,k2_xboole_0(X13,X14)) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f11174,f22])).

fof(f11174,plain,(
    ! [X14,X12,X13] : k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,X14)) ),
    inference(superposition,[],[f22,f10454])).

fof(f19644,plain,(
    ! [X78,X79,X77] : k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X77,X78),k1_xboole_0),k4_xboole_0(k2_xboole_0(k2_xboole_0(X78,X79),X77),k2_xboole_0(X77,X78))) ),
    inference(superposition,[],[f99,f8274])).

fof(f8274,plain,(
    ! [X6,X8,X7] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(k2_xboole_0(X7,X8),X6)) ),
    inference(superposition,[],[f4336,f17])).

fof(f4336,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9))) ),
    inference(superposition,[],[f2899,f22])).

fof(f2899,plain,(
    ! [X19,X20,X18] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X19,X18),X19),k2_xboole_0(X18,X20)) ),
    inference(superposition,[],[f282,f2834])).

fof(f13059,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f10434,f10537])).

fof(f10434,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f477,f10427])).

fof(f10427,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X7,X5))) ),
    inference(forward_demodulation,[],[f10377,f4099])).

fof(f4099,plain,(
    ! [X17,X18,X16] : k2_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X16,X17))) = k2_xboole_0(X17,k4_xboole_0(X18,X16)) ),
    inference(forward_demodulation,[],[f4018,f2712])).

fof(f2712,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2))) ),
    inference(superposition,[],[f31,f17])).

fof(f4018,plain,(
    ! [X17,X18,X16] : k2_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X16,X17))) = k2_xboole_0(X17,k4_xboole_0(X18,k2_xboole_0(X17,X16))) ),
    inference(superposition,[],[f31,f3658])).

fof(f10377,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X5,X6)))) ),
    inference(superposition,[],[f10219,f22])).

fof(f477,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f26,f465])).

fof(f465,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f300,f17])).

fof(f300,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k2_xboole_0(X10,X11),X10) ),
    inference(forward_demodulation,[],[f299,f205])).

fof(f299,plain,(
    ! [X10,X11] : k2_xboole_0(k2_xboole_0(X10,X11),X10) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f295,f17])).

fof(f295,plain,(
    ! [X10,X11] : k2_xboole_0(k2_xboole_0(X10,X11),X10) = k2_xboole_0(k2_xboole_0(X10,X11),k1_xboole_0) ),
    inference(superposition,[],[f19,f241])).

fof(f241,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f193,f230])).

fof(f193,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f87,f191])).

fof(f87,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),X3) ),
    inference(superposition,[],[f22,f54])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f23,f22])).

fof(f23,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f14,f21,f21,f18])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:45:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (1309)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (1303)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (1305)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (1312)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (1306)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (1307)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (1316)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (1308)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (1310)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (1315)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (1302)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (1317)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (1314)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (1313)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (1313)Refutation not found, incomplete strategy% (1313)------------------------------
% 0.21/0.52  % (1313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1313)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1313)Memory used [KB]: 10490
% 0.21/0.52  % (1313)Time elapsed: 0.102 s
% 0.21/0.52  % (1313)------------------------------
% 0.21/0.52  % (1313)------------------------------
% 0.21/0.52  % (1304)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (1318)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (1311)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.53  % (1319)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.28/1.02  % (1306)Time limit reached!
% 5.28/1.02  % (1306)------------------------------
% 5.28/1.02  % (1306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.28/1.02  % (1306)Termination reason: Time limit
% 5.28/1.02  
% 5.28/1.02  % (1306)Memory used [KB]: 14711
% 5.28/1.02  % (1306)Time elapsed: 0.611 s
% 5.28/1.02  % (1306)------------------------------
% 5.28/1.02  % (1306)------------------------------
% 9.34/1.53  % (1315)Refutation found. Thanks to Tanya!
% 9.34/1.53  % SZS status Theorem for theBenchmark
% 9.34/1.53  % SZS output start Proof for theBenchmark
% 9.34/1.53  fof(f28116,plain,(
% 9.34/1.53    $false),
% 9.34/1.53    inference(subsumption_resolution,[],[f28115,f3658])).
% 9.34/1.53  fof(f3658,plain,(
% 9.34/1.53    ( ! [X10,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(k4_xboole_0(X10,X9),X9)) )),
% 9.34/1.53    inference(forward_demodulation,[],[f3594,f15])).
% 9.34/1.53  fof(f15,plain,(
% 9.34/1.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.34/1.53    inference(cnf_transformation,[],[f5])).
% 9.34/1.53  fof(f5,axiom,(
% 9.34/1.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 9.34/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 9.34/1.53  fof(f3594,plain,(
% 9.34/1.53    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X10,X9),X9) = k4_xboole_0(k2_xboole_0(X9,X10),k1_xboole_0)) )),
% 9.34/1.53    inference(superposition,[],[f3285,f19])).
% 9.34/1.53  fof(f19,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 9.34/1.53    inference(cnf_transformation,[],[f4])).
% 9.34/1.53  fof(f4,axiom,(
% 9.34/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 9.34/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 9.34/1.53  fof(f3285,plain,(
% 9.34/1.53    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k1_xboole_0)) )),
% 9.34/1.53    inference(forward_demodulation,[],[f3284,f2990])).
% 9.34/1.53  fof(f2990,plain,(
% 9.34/1.53    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X4))) )),
% 9.34/1.53    inference(superposition,[],[f276,f2862])).
% 9.34/1.53  fof(f2862,plain,(
% 9.34/1.53    ( ! [X2,X1] : (k2_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X1),X1)) = X2) )),
% 9.34/1.53    inference(superposition,[],[f2834,f17])).
% 9.34/1.53  fof(f17,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 9.34/1.53    inference(cnf_transformation,[],[f1])).
% 9.34/1.53  fof(f1,axiom,(
% 9.34/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 9.34/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 9.34/1.53  fof(f2834,plain,(
% 9.34/1.53    ( ! [X39,X38] : (k2_xboole_0(X39,k4_xboole_0(k2_xboole_0(X38,X39),X38)) = X39) )),
% 9.34/1.53    inference(forward_demodulation,[],[f2741,f207])).
% 9.34/1.53  fof(f207,plain,(
% 9.34/1.53    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 9.34/1.53    inference(backward_demodulation,[],[f122,f192])).
% 9.34/1.53  fof(f192,plain,(
% 9.34/1.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 9.34/1.53    inference(backward_demodulation,[],[f54,f191])).
% 9.34/1.53  fof(f191,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0)) = X1) )),
% 9.34/1.53    inference(forward_demodulation,[],[f187,f15])).
% 9.34/1.53  fof(f187,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(k1_xboole_0,X0))) )),
% 9.34/1.53    inference(superposition,[],[f27,f167])).
% 9.34/1.53  fof(f167,plain,(
% 9.34/1.53    ( ! [X6] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 9.34/1.53    inference(backward_demodulation,[],[f95,f166])).
% 9.34/1.53  fof(f166,plain,(
% 9.34/1.53    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(X0,X0))) )),
% 9.34/1.53    inference(forward_demodulation,[],[f165,f29])).
% 9.34/1.53  fof(f29,plain,(
% 9.34/1.53    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 9.34/1.53    inference(superposition,[],[f22,f15])).
% 9.34/1.53  fof(f22,plain,(
% 9.34/1.53    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 9.34/1.53    inference(cnf_transformation,[],[f6])).
% 9.34/1.53  fof(f6,axiom,(
% 9.34/1.53    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 9.34/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 9.34/1.53  fof(f165,plain,(
% 9.34/1.53    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k1_xboole_0)),k4_xboole_0(X0,X0))) )),
% 9.34/1.53    inference(forward_demodulation,[],[f164,f94])).
% 9.34/1.53  fof(f94,plain,(
% 9.34/1.53    ( ! [X4,X3] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 9.34/1.53    inference(forward_demodulation,[],[f82,f19])).
% 9.34/1.53  fof(f82,plain,(
% 9.34/1.53    ( ! [X4,X3] : (k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4)))) )),
% 9.34/1.53    inference(superposition,[],[f54,f22])).
% 9.34/1.53  fof(f164,plain,(
% 9.34/1.53    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))),k4_xboole_0(X0,X0))) )),
% 9.34/1.53    inference(forward_demodulation,[],[f147,f54])).
% 9.34/1.53  fof(f147,plain,(
% 9.34/1.53    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0)),k4_xboole_0(X0,X0))) )),
% 9.34/1.53    inference(superposition,[],[f102,f54])).
% 9.34/1.53  fof(f102,plain,(
% 9.34/1.53    ( ! [X7] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X7,X7),k4_xboole_0(k1_xboole_0,X7))) )),
% 9.34/1.53    inference(superposition,[],[f25,f54])).
% 9.34/1.53  fof(f25,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 9.34/1.53    inference(definition_unfolding,[],[f20,f18])).
% 9.34/1.53  fof(f18,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 9.34/1.53    inference(cnf_transformation,[],[f7])).
% 9.34/1.53  fof(f7,axiom,(
% 9.34/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 9.34/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 9.34/1.53  fof(f20,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 9.34/1.53    inference(cnf_transformation,[],[f8])).
% 9.34/1.53  fof(f8,axiom,(
% 9.34/1.53    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 9.34/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 9.34/1.53  fof(f95,plain,(
% 9.34/1.53    ( ! [X6] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(X6,X6)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 9.34/1.53    inference(forward_demodulation,[],[f86,f17])).
% 9.34/1.53  fof(f86,plain,(
% 9.34/1.53    ( ! [X6] : (k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k1_xboole_0) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X6),k4_xboole_0(X6,X6))) )),
% 9.34/1.53    inference(superposition,[],[f19,f54])).
% 9.34/1.53  fof(f27,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 9.34/1.53    inference(superposition,[],[f22,f15])).
% 9.34/1.53  fof(f54,plain,(
% 9.34/1.53    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 9.34/1.53    inference(superposition,[],[f24,f15])).
% 9.34/1.53  fof(f24,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 9.34/1.53    inference(definition_unfolding,[],[f16,f18,f18])).
% 9.34/1.53  fof(f16,plain,(
% 9.34/1.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 9.34/1.53    inference(cnf_transformation,[],[f2])).
% 9.34/1.53  fof(f2,axiom,(
% 9.34/1.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 9.34/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 9.34/1.53  fof(f122,plain,(
% 9.34/1.53    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 9.34/1.53    inference(superposition,[],[f108,f17])).
% 9.34/1.53  fof(f108,plain,(
% 9.34/1.53    ( ! [X9] : (k2_xboole_0(k4_xboole_0(X9,X9),X9) = X9) )),
% 9.34/1.53    inference(superposition,[],[f25,f15])).
% 9.34/1.53  fof(f2741,plain,(
% 9.34/1.53    ( ! [X39,X38] : (k2_xboole_0(X39,k1_xboole_0) = k2_xboole_0(X39,k4_xboole_0(k2_xboole_0(X38,X39),X38))) )),
% 9.34/1.53    inference(superposition,[],[f31,f192])).
% 9.34/1.53  fof(f31,plain,(
% 9.34/1.53    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 9.34/1.53    inference(superposition,[],[f19,f22])).
% 9.34/1.53  fof(f276,plain,(
% 9.34/1.53    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X2,X3))))) )),
% 9.34/1.53    inference(superposition,[],[f202,f22])).
% 9.34/1.53  fof(f202,plain,(
% 9.34/1.53    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 9.34/1.53    inference(backward_demodulation,[],[f94,f191])).
% 9.34/1.53  fof(f3284,plain,(
% 9.34/1.53    ( ! [X12,X13] : (k2_xboole_0(X12,X13) = k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13)))) )),
% 9.34/1.53    inference(forward_demodulation,[],[f3196,f15])).
% 9.34/1.53  fof(f3196,plain,(
% 9.34/1.53    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X13,X12),k4_xboole_0(k2_xboole_0(X13,X12),k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k1_xboole_0)) )),
% 9.34/1.53    inference(superposition,[],[f24,f2990])).
% 9.34/1.53  fof(f28115,plain,(
% 9.34/1.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 9.34/1.53    inference(forward_demodulation,[],[f28114,f323])).
% 9.34/1.53  fof(f323,plain,(
% 9.34/1.53    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,X12)) = X11) )),
% 9.34/1.53    inference(forward_demodulation,[],[f317,f207])).
% 9.34/1.53  fof(f317,plain,(
% 9.34/1.53    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X11,X12)) = k2_xboole_0(X11,k1_xboole_0)) )),
% 9.34/1.53    inference(superposition,[],[f19,f274])).
% 9.34/1.53  fof(f274,plain,(
% 9.34/1.53    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),X8)) )),
% 9.34/1.53    inference(superposition,[],[f202,f25])).
% 9.34/1.53  fof(f28114,plain,(
% 9.34/1.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 9.34/1.53    inference(forward_demodulation,[],[f28113,f17])).
% 9.34/1.53  fof(f28113,plain,(
% 9.34/1.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 9.34/1.53    inference(forward_demodulation,[],[f28112,f19])).
% 9.34/1.53  fof(f28112,plain,(
% 9.34/1.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 9.34/1.53    inference(forward_demodulation,[],[f27869,f17])).
% 9.34/1.53  fof(f27869,plain,(
% 9.34/1.53    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)))),
% 9.34/1.53    inference(superposition,[],[f13059,f27201])).
% 9.34/1.53  fof(f27201,plain,(
% 9.34/1.53    ( ! [X78,X79,X77] : (k2_xboole_0(X79,k2_xboole_0(X77,X78)) = k2_xboole_0(k2_xboole_0(X78,X79),X77)) )),
% 9.34/1.53    inference(forward_demodulation,[],[f27173,f10536])).
% 9.34/1.53  fof(f10536,plain,(
% 9.34/1.53    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 9.34/1.53    inference(backward_demodulation,[],[f933,f10454])).
% 9.34/1.53  fof(f10454,plain,(
% 9.34/1.53    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 9.34/1.53    inference(superposition,[],[f10173,f17])).
% 9.34/1.53  fof(f10173,plain,(
% 9.34/1.53    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 9.34/1.53    inference(forward_demodulation,[],[f10041,f207])).
% 9.34/1.53  fof(f10041,plain,(
% 9.34/1.53    ( ! [X6,X7] : (k4_xboole_0(X7,X6) = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,k1_xboole_0))) )),
% 9.34/1.53    inference(superposition,[],[f5043,f22])).
% 9.34/1.53  fof(f5043,plain,(
% 9.34/1.53    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0)) )),
% 9.34/1.53    inference(forward_demodulation,[],[f5042,f15])).
% 9.34/1.53  fof(f5042,plain,(
% 9.34/1.53    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k1_xboole_0)) )),
% 9.34/1.53    inference(forward_demodulation,[],[f5041,f391])).
% 9.34/1.53  fof(f391,plain,(
% 9.34/1.53    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 9.34/1.53    inference(superposition,[],[f282,f17])).
% 9.34/1.53  fof(f282,plain,(
% 9.34/1.53    ( ! [X6,X8,X7] : (k1_xboole_0 = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8))) )),
% 9.34/1.53    inference(forward_demodulation,[],[f278,f230])).
% 9.34/1.54  fof(f230,plain,(
% 9.34/1.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 9.34/1.54    inference(superposition,[],[f205,f167])).
% 9.34/1.54  fof(f205,plain,(
% 9.34/1.54    ( ! [X9] : (k2_xboole_0(k1_xboole_0,X9) = X9) )),
% 9.34/1.54    inference(backward_demodulation,[],[f108,f192])).
% 9.34/1.54  fof(f278,plain,(
% 9.34/1.54    ( ! [X6,X8,X7] : (k4_xboole_0(k1_xboole_0,X8) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X6),X8))) )),
% 9.34/1.54    inference(superposition,[],[f22,f202])).
% 9.34/1.54  fof(f5041,plain,(
% 9.34/1.54    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X8,k2_xboole_0(X7,k2_xboole_0(X7,X8))))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f5040,f19])).
% 9.34/1.54  fof(f5040,plain,(
% 9.34/1.54    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X8,k2_xboole_0(X7,k4_xboole_0(k2_xboole_0(X7,X8),X7))))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f4866,f22])).
% 9.34/1.54  fof(f4866,plain,(
% 9.34/1.54    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(k2_xboole_0(X7,X8),X7),k1_xboole_0) = k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(k2_xboole_0(X7,X8),X7)))) )),
% 9.34/1.54    inference(superposition,[],[f24,f3053])).
% 9.34/1.54  fof(f3053,plain,(
% 9.34/1.54    ( ! [X10,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X10),X9),k4_xboole_0(X10,X9))) )),
% 9.34/1.54    inference(superposition,[],[f2897,f19])).
% 9.34/1.54  fof(f2897,plain,(
% 9.34/1.54    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X15,X14),X15),X14)) )),
% 9.34/1.54    inference(superposition,[],[f202,f2834])).
% 9.34/1.54  fof(f933,plain,(
% 9.34/1.54    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k4_xboole_0(k2_xboole_0(X2,X1),X1))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f881,f15])).
% 9.34/1.54  fof(f881,plain,(
% 9.34/1.54    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X1,k1_xboole_0),k4_xboole_0(k2_xboole_0(X2,X1),X1))) )),
% 9.34/1.54    inference(superposition,[],[f99,f202])).
% 9.34/1.54  fof(f99,plain,(
% 9.34/1.54    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 9.34/1.54    inference(superposition,[],[f25,f24])).
% 9.34/1.54  fof(f27173,plain,(
% 9.34/1.54    ( ! [X78,X79,X77] : (k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k2_xboole_0(X77,X78),k4_xboole_0(X79,k2_xboole_0(X77,X78)))) )),
% 9.34/1.54    inference(backward_demodulation,[],[f19743,f26978])).
% 9.34/1.54  fof(f26978,plain,(
% 9.34/1.54    ( ! [X163,X164,X162] : (k4_xboole_0(X164,k2_xboole_0(X162,X163)) = k4_xboole_0(k2_xboole_0(X163,X164),k2_xboole_0(X162,X163))) )),
% 9.34/1.54    inference(superposition,[],[f23265,f11120])).
% 9.34/1.54  fof(f11120,plain,(
% 9.34/1.54    ( ! [X154,X153] : (k4_xboole_0(k2_xboole_0(X153,X154),k4_xboole_0(X153,X154)) = X154) )),
% 9.34/1.54    inference(forward_demodulation,[],[f11048,f10219])).
% 9.34/1.54  fof(f10219,plain,(
% 9.34/1.54    ( ! [X2,X1] : (k4_xboole_0(X2,k4_xboole_0(X1,X2)) = X2) )),
% 9.34/1.54    inference(backward_demodulation,[],[f9771,f10173])).
% 9.34/1.54  fof(f9771,plain,(
% 9.34/1.54    ( ! [X2,X1] : (k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X1),X2)) = X2) )),
% 9.34/1.54    inference(superposition,[],[f9688,f17])).
% 9.34/1.54  fof(f9688,plain,(
% 9.34/1.54    ( ! [X12,X13] : (k4_xboole_0(X12,k4_xboole_0(k2_xboole_0(X13,X12),X12)) = X12) )),
% 9.34/1.54    inference(forward_demodulation,[],[f9557,f15])).
% 9.34/1.54  fof(f9557,plain,(
% 9.34/1.54    ( ! [X12,X13] : (k4_xboole_0(X12,k1_xboole_0) = k4_xboole_0(X12,k4_xboole_0(k2_xboole_0(X13,X12),X12))) )),
% 9.34/1.54    inference(superposition,[],[f320,f4948])).
% 9.34/1.54  fof(f4948,plain,(
% 9.34/1.54    ( ! [X56,X55] : (k1_xboole_0 = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f4947,f15])).
% 9.34/1.54  fof(f4947,plain,(
% 9.34/1.54    ( ! [X56,X55] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X56,k1_xboole_0),k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f4946,f202])).
% 9.34/1.54  fof(f4946,plain,(
% 9.34/1.54    ( ! [X56,X55] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X56,k4_xboole_0(X56,k2_xboole_0(X55,X56))),k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f4819,f24])).
% 9.34/1.54  fof(f4819,plain,(
% 9.34/1.54    ( ! [X56,X55] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X55,X56),k4_xboole_0(k2_xboole_0(X55,X56),X56)),k4_xboole_0(X56,k4_xboole_0(k2_xboole_0(X55,X56),X56)))) )),
% 9.34/1.54    inference(superposition,[],[f3053,f1114])).
% 9.34/1.54  fof(f1114,plain,(
% 9.34/1.54    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),X1)) )),
% 9.34/1.54    inference(forward_demodulation,[],[f1051,f15])).
% 9.34/1.54  fof(f1051,plain,(
% 9.34/1.54    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X2,X1),X1),k4_xboole_0(X1,k1_xboole_0))) )),
% 9.34/1.54    inference(superposition,[],[f324,f202])).
% 9.34/1.54  fof(f324,plain,(
% 9.34/1.54    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = X3) )),
% 9.34/1.54    inference(backward_demodulation,[],[f72,f323])).
% 9.34/1.54  fof(f72,plain,(
% 9.34/1.54    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3))) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f65,f17])).
% 9.34/1.54  fof(f65,plain,(
% 9.34/1.54    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X4,k4_xboole_0(X4,X3)))) )),
% 9.34/1.54    inference(superposition,[],[f19,f24])).
% 9.34/1.54  fof(f320,plain,(
% 9.34/1.54    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f314,f15])).
% 9.34/1.54  fof(f314,plain,(
% 9.34/1.54    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k4_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)) )),
% 9.34/1.54    inference(superposition,[],[f24,f274])).
% 9.34/1.54  fof(f11048,plain,(
% 9.34/1.54    ( ! [X154,X153] : (k4_xboole_0(X154,k4_xboole_0(X153,X154)) = k4_xboole_0(k2_xboole_0(X153,X154),k4_xboole_0(X153,X154))) )),
% 9.34/1.54    inference(superposition,[],[f10173,f10537])).
% 9.34/1.54  fof(f10537,plain,(
% 9.34/1.54    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X2,X1),X1)) )),
% 9.34/1.54    inference(backward_demodulation,[],[f1114,f10454])).
% 9.34/1.54  fof(f23265,plain,(
% 9.34/1.54    ( ! [X393,X395,X394] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X393,X394),X395),X393) = k4_xboole_0(X395,X393)) )),
% 9.34/1.54    inference(forward_demodulation,[],[f23173,f10173])).
% 9.34/1.54  fof(f23173,plain,(
% 9.34/1.54    ( ! [X393,X395,X394] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X393,X394),X395),X393) = k4_xboole_0(k2_xboole_0(X393,X395),X393)) )),
% 9.34/1.54    inference(superposition,[],[f10173,f15020])).
% 9.34/1.54  fof(f15020,plain,(
% 9.34/1.54    ( ! [X24,X23,X22] : (k2_xboole_0(X22,X24) = k2_xboole_0(X22,k2_xboole_0(k4_xboole_0(X22,X23),X24))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f14907,f2814])).
% 9.34/1.54  fof(f2814,plain,(
% 9.34/1.54    ( ! [X59,X57,X58] : (k2_xboole_0(X57,X59) = k2_xboole_0(X57,k4_xboole_0(X59,k4_xboole_0(X57,X58)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f2724,f19])).
% 9.34/1.54  fof(f2724,plain,(
% 9.34/1.54    ( ! [X59,X57,X58] : (k2_xboole_0(X57,k4_xboole_0(X59,k4_xboole_0(X57,X58))) = k2_xboole_0(X57,k4_xboole_0(X59,X57))) )),
% 9.34/1.54    inference(superposition,[],[f31,f609])).
% 9.34/1.54  fof(f609,plain,(
% 9.34/1.54    ( ! [X10,X9] : (k2_xboole_0(k4_xboole_0(X9,X10),X9) = X9) )),
% 9.34/1.54    inference(superposition,[],[f417,f323])).
% 9.34/1.54  fof(f417,plain,(
% 9.34/1.54    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,k2_xboole_0(X2,X3))) )),
% 9.34/1.54    inference(superposition,[],[f284,f17])).
% 9.34/1.54  fof(f284,plain,(
% 9.34/1.54    ( ! [X10,X9] : (k2_xboole_0(X10,X9) = k2_xboole_0(k2_xboole_0(X10,X9),X9)) )),
% 9.34/1.54    inference(forward_demodulation,[],[f283,f205])).
% 9.34/1.54  fof(f283,plain,(
% 9.34/1.54    ( ! [X10,X9] : (k2_xboole_0(k2_xboole_0(X10,X9),X9) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X10,X9))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f279,f17])).
% 9.34/1.54  fof(f279,plain,(
% 9.34/1.54    ( ! [X10,X9] : (k2_xboole_0(k2_xboole_0(X10,X9),X9) = k2_xboole_0(k2_xboole_0(X10,X9),k1_xboole_0)) )),
% 9.34/1.54    inference(superposition,[],[f19,f202])).
% 9.34/1.54  fof(f14907,plain,(
% 9.34/1.54    ( ! [X24,X23,X22] : (k2_xboole_0(X22,k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k2_xboole_0(X22,k4_xboole_0(X24,k4_xboole_0(X22,X23)))) )),
% 9.34/1.54    inference(superposition,[],[f2814,f10173])).
% 9.34/1.54  fof(f19743,plain,(
% 9.34/1.54    ( ! [X78,X79,X77] : (k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k2_xboole_0(X77,X78),k4_xboole_0(k2_xboole_0(X78,X79),k2_xboole_0(X77,X78)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f19742,f15])).
% 9.34/1.54  fof(f19742,plain,(
% 9.34/1.54    ( ! [X78,X79,X77] : (k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X77,X78),k1_xboole_0),k4_xboole_0(k2_xboole_0(X78,X79),k2_xboole_0(X77,X78)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f19644,f11241])).
% 9.34/1.54  fof(f11241,plain,(
% 9.34/1.54    ( ! [X14,X12,X13] : (k4_xboole_0(X12,k2_xboole_0(X13,X14)) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,X14))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f11174,f22])).
% 9.34/1.54  fof(f11174,plain,(
% 9.34/1.54    ( ! [X14,X12,X13] : (k4_xboole_0(k4_xboole_0(X12,X13),X14) = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,X14))) )),
% 9.34/1.54    inference(superposition,[],[f22,f10454])).
% 9.34/1.54  fof(f19644,plain,(
% 9.34/1.54    ( ! [X78,X79,X77] : (k2_xboole_0(k2_xboole_0(X78,X79),X77) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X77,X78),k1_xboole_0),k4_xboole_0(k2_xboole_0(k2_xboole_0(X78,X79),X77),k2_xboole_0(X77,X78)))) )),
% 9.34/1.54    inference(superposition,[],[f99,f8274])).
% 9.34/1.54  fof(f8274,plain,(
% 9.34/1.54    ( ! [X6,X8,X7] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(k2_xboole_0(X7,X8),X6))) )),
% 9.34/1.54    inference(superposition,[],[f4336,f17])).
% 9.34/1.54  fof(f4336,plain,(
% 9.34/1.54    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X8,X9)))) )),
% 9.34/1.54    inference(superposition,[],[f2899,f22])).
% 9.34/1.54  fof(f2899,plain,(
% 9.34/1.54    ( ! [X19,X20,X18] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X19,X18),X19),k2_xboole_0(X18,X20))) )),
% 9.34/1.54    inference(superposition,[],[f282,f2834])).
% 9.34/1.54  fof(f13059,plain,(
% 9.34/1.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 9.34/1.54    inference(superposition,[],[f10434,f10537])).
% 9.34/1.54  fof(f10434,plain,(
% 9.34/1.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 9.34/1.54    inference(backward_demodulation,[],[f477,f10427])).
% 9.34/1.54  fof(f10427,plain,(
% 9.34/1.54    ( ! [X6,X7,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X7,X5)))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f10377,f4099])).
% 9.34/1.54  fof(f4099,plain,(
% 9.34/1.54    ( ! [X17,X18,X16] : (k2_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X16,X17))) = k2_xboole_0(X17,k4_xboole_0(X18,X16))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f4018,f2712])).
% 9.34/1.54  fof(f2712,plain,(
% 9.34/1.54    ( ! [X4,X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X4,X2)) = k2_xboole_0(X3,k4_xboole_0(X4,k2_xboole_0(X3,X2)))) )),
% 9.34/1.54    inference(superposition,[],[f31,f17])).
% 9.34/1.54  fof(f4018,plain,(
% 9.34/1.54    ( ! [X17,X18,X16] : (k2_xboole_0(X17,k4_xboole_0(X18,k4_xboole_0(X16,X17))) = k2_xboole_0(X17,k4_xboole_0(X18,k2_xboole_0(X17,X16)))) )),
% 9.34/1.54    inference(superposition,[],[f31,f3658])).
% 9.34/1.54  fof(f10377,plain,(
% 9.34/1.54    ( ! [X6,X7,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X7,k4_xboole_0(X5,X6))))) )),
% 9.34/1.54    inference(superposition,[],[f10219,f22])).
% 9.34/1.54  fof(f477,plain,(
% 9.34/1.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 9.34/1.54    inference(backward_demodulation,[],[f26,f465])).
% 9.34/1.54  fof(f465,plain,(
% 9.34/1.54    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 9.34/1.54    inference(superposition,[],[f300,f17])).
% 9.34/1.54  fof(f300,plain,(
% 9.34/1.54    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k2_xboole_0(X10,X11),X10)) )),
% 9.34/1.54    inference(forward_demodulation,[],[f299,f205])).
% 9.34/1.54  fof(f299,plain,(
% 9.34/1.54    ( ! [X10,X11] : (k2_xboole_0(k2_xboole_0(X10,X11),X10) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X10,X11))) )),
% 9.34/1.54    inference(forward_demodulation,[],[f295,f17])).
% 9.34/1.54  fof(f295,plain,(
% 9.34/1.54    ( ! [X10,X11] : (k2_xboole_0(k2_xboole_0(X10,X11),X10) = k2_xboole_0(k2_xboole_0(X10,X11),k1_xboole_0)) )),
% 9.34/1.54    inference(superposition,[],[f19,f241])).
% 9.34/1.54  fof(f241,plain,(
% 9.34/1.54    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 9.34/1.54    inference(backward_demodulation,[],[f193,f230])).
% 9.34/1.54  fof(f193,plain,(
% 9.34/1.54    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 9.34/1.54    inference(backward_demodulation,[],[f87,f191])).
% 9.34/1.54  fof(f87,plain,(
% 9.34/1.54    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)),X3)) )),
% 9.34/1.54    inference(superposition,[],[f22,f54])).
% 9.34/1.54  fof(f26,plain,(
% 9.34/1.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 9.34/1.54    inference(backward_demodulation,[],[f23,f22])).
% 9.34/1.54  fof(f23,plain,(
% 9.34/1.54    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 9.34/1.54    inference(definition_unfolding,[],[f14,f21,f21,f18])).
% 9.34/1.54  fof(f21,plain,(
% 9.34/1.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 9.34/1.54    inference(cnf_transformation,[],[f3])).
% 9.34/1.54  fof(f3,axiom,(
% 9.34/1.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 9.34/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 9.34/1.54  fof(f14,plain,(
% 9.34/1.54    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 9.34/1.54    inference(cnf_transformation,[],[f13])).
% 9.34/1.54  fof(f13,plain,(
% 9.34/1.54    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 9.34/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 9.34/1.54  fof(f12,plain,(
% 9.34/1.54    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 9.34/1.54    introduced(choice_axiom,[])).
% 9.34/1.54  fof(f11,plain,(
% 9.34/1.54    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.34/1.54    inference(ennf_transformation,[],[f10])).
% 9.34/1.54  fof(f10,negated_conjecture,(
% 9.34/1.54    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.34/1.54    inference(negated_conjecture,[],[f9])).
% 9.34/1.54  fof(f9,conjecture,(
% 9.34/1.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 9.34/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 9.34/1.54  % SZS output end Proof for theBenchmark
% 9.34/1.54  % (1315)------------------------------
% 9.34/1.54  % (1315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.34/1.54  % (1315)Termination reason: Refutation
% 9.34/1.54  
% 9.34/1.54  % (1315)Memory used [KB]: 22899
% 9.34/1.54  % (1315)Time elapsed: 1.102 s
% 9.34/1.54  % (1315)------------------------------
% 9.34/1.54  % (1315)------------------------------
% 9.34/1.54  % (1301)Success in time 1.185 s
%------------------------------------------------------------------------------
