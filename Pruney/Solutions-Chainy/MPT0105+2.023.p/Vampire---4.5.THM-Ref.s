%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:06 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  138 (15756 expanded)
%              Number of leaves         :   12 (5252 expanded)
%              Depth                    :   38
%              Number of atoms          :  139 (15757 expanded)
%              Number of equality atoms :  138 (15756 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4434,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4388,f3845])).

fof(f3845,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f3666,f18])).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f3666,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(backward_demodulation,[],[f3188,f3665])).

fof(f3665,plain,(
    ! [X8,X7] : k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f3664,f3194])).

fof(f3194,plain,(
    ! [X21,X22] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X21,X22)) ),
    inference(backward_demodulation,[],[f955,f3150])).

fof(f3150,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(backward_demodulation,[],[f210,f3149])).

fof(f3149,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f2843,f3148])).

fof(f3148,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k4_xboole_0(X12,k3_xboole_0(X12,X13)) ),
    inference(forward_demodulation,[],[f3147,f2860])).

fof(f2860,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f2848,f2859])).

fof(f2859,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f2850,f128])).

fof(f128,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f125,f61])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f47,f60])).

fof(f60,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f59,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f19,f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f59,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f51,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f35,f17])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f22,f27])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f51,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k4_xboole_0(k2_xboole_0(X1,X1),X1) ),
    inference(superposition,[],[f24,f32])).

fof(f32,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f28,f18])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f21,f27])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f46,f39])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),X0) ),
    inference(superposition,[],[f23,f32])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f125,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f60])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2850,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f1023,f2844])).

fof(f2844,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k5_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f30,f2843])).

fof(f30,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f21,f21])).

fof(f1023,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f1022,f30])).

fof(f1022,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f985,f883])).

fof(f883,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f177,f872])).

fof(f872,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f24,f746])).

fof(f746,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f723,f17])).

fof(f723,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f80,f89])).

fof(f89,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f75,f22])).

fof(f75,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f25,f27])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f80,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f22,f25])).

fof(f177,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k3_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f21,f30])).

fof(f985,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[],[f53,f715])).

fof(f715,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k3_xboole_0(X11,X12)) = X11 ),
    inference(forward_demodulation,[],[f708,f17])).

fof(f708,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k3_xboole_0(X11,X12)) = k2_xboole_0(X11,k1_xboole_0) ),
    inference(superposition,[],[f22,f687])).

fof(f687,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f686,f27])).

fof(f686,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f660,f71])).

fof(f71,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) = k4_xboole_0(k3_xboole_0(X5,X6),X7) ),
    inference(superposition,[],[f25,f21])).

fof(f660,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[],[f71,f37])).

fof(f37,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f22,f21])).

fof(f53,plain,(
    ! [X2,X3] : k3_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f21,f24])).

fof(f2848,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k5_xboole_0(X5,k3_xboole_0(X5,X6))) ),
    inference(backward_demodulation,[],[f872,f2844])).

fof(f3147,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k4_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f3146,f128])).

fof(f3146,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13))) = k5_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13))) ),
    inference(forward_demodulation,[],[f3081,f103])).

fof(f103,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7)) ),
    inference(superposition,[],[f26,f20])).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f3081,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13))) = k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X12,X13),X12)) ),
    inference(superposition,[],[f2956,f746])).

fof(f2956,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f53,f2955])).

fof(f2955,plain,(
    ! [X35,X36] : k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(X35,k5_xboole_0(X36,k2_xboole_0(X35,X36))) ),
    inference(forward_demodulation,[],[f2954,f26])).

fof(f2954,plain,(
    ! [X35,X36] : k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(k5_xboole_0(X35,X36),k2_xboole_0(X35,X36)) ),
    inference(forward_demodulation,[],[f2953,f20])).

fof(f2953,plain,(
    ! [X35,X36] : k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(k2_xboole_0(X35,X36),k5_xboole_0(X35,X36)) ),
    inference(forward_demodulation,[],[f2952,f1507])).

fof(f1507,plain,(
    ! [X39,X40] : k5_xboole_0(X39,X40) = k3_xboole_0(k2_xboole_0(X39,X40),k5_xboole_0(X39,X40)) ),
    inference(superposition,[],[f1193,f1445])).

fof(f1445,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f1444,f61])).

fof(f1444,plain,(
    ! [X4,X5] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f1442,f20])).

fof(f1442,plain,(
    ! [X4,X5] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0) ),
    inference(backward_demodulation,[],[f43,f1422])).

fof(f1422,plain,(
    ! [X24,X23] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24)) ),
    inference(superposition,[],[f1271,f24])).

fof(f1271,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f1219,f27])).

fof(f1219,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f81,f39])).

fof(f81,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f21,f25])).

fof(f43,plain,(
    ! [X4,X5] : k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))) ),
    inference(superposition,[],[f23,f23])).

fof(f1193,plain,(
    ! [X12,X13] : k3_xboole_0(k2_xboole_0(X12,X13),X12) = X12 ),
    inference(forward_demodulation,[],[f1192,f33])).

fof(f33,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f29,f18])).

fof(f29,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f21,f19])).

fof(f1192,plain,(
    ! [X12,X13] : k3_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(X12,k2_xboole_0(X12,X13))) = X12 ),
    inference(forward_demodulation,[],[f1175,f1033])).

fof(f1033,plain,(
    ! [X12,X11] : k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = X11 ),
    inference(forward_demodulation,[],[f1032,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f54,f18])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f48,f34])).

fof(f34,plain,(
    ! [X5] : k1_xboole_0 = k3_xboole_0(X5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f31,f27])).

fof(f31,plain,(
    ! [X5] : k3_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f21,f18])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f24,f17])).

fof(f1032,plain,(
    ! [X12,X11] : k5_xboole_0(X11,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f1031,f60])).

fof(f1031,plain,(
    ! [X12,X11] : k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = k5_xboole_0(X11,k5_xboole_0(k2_xboole_0(X11,X12),k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f1030,f103])).

fof(f1030,plain,(
    ! [X12,X11] : k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = k5_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f1029,f373])).

fof(f373,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f122,f371])).

fof(f371,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f349,f321])).

fof(f321,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f128,f20])).

fof(f349,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k2_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X2,X3),X2)) ),
    inference(superposition,[],[f102,f33])).

fof(f102,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f26,f23])).

fof(f122,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f24,f33])).

fof(f1029,plain,(
    ! [X12,X11] : k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(k2_xboole_0(X11,X12),X11)) ),
    inference(forward_demodulation,[],[f1028,f883])).

fof(f1028,plain,(
    ! [X12,X11] : k3_xboole_0(k2_xboole_0(X11,X12),k3_xboole_0(k2_xboole_0(X11,X12),X11)) = k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f990,f20])).

fof(f990,plain,(
    ! [X12,X11] : k3_xboole_0(k2_xboole_0(X11,X12),k3_xboole_0(k2_xboole_0(X11,X12),X11)) = k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(k2_xboole_0(X11,X12),X11)) ),
    inference(superposition,[],[f53,f40])).

fof(f40,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1) ),
    inference(forward_demodulation,[],[f36,f17])).

fof(f36,plain,(
    ! [X2,X1] : k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0) ),
    inference(superposition,[],[f22,f19])).

fof(f1175,plain,(
    ! [X12,X13] : k3_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(X12,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f53,f371])).

fof(f2952,plain,(
    ! [X35,X36] : k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(k2_xboole_0(X35,X36),k5_xboole_0(X35,X36))) ),
    inference(forward_demodulation,[],[f2903,f2861])).

fof(f2861,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f883,f2860])).

fof(f2903,plain,(
    ! [X35,X36] : k5_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(k2_xboole_0(X35,X36),k5_xboole_0(X35,X36))) = k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36))) ),
    inference(superposition,[],[f2844,f53])).

fof(f2843,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f2842,f20])).

fof(f2842,plain,(
    ! [X2,X3] : k5_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f2820,f2833])).

fof(f2833,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(forward_demodulation,[],[f2819,f392])).

fof(f392,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f321,f321])).

fof(f2819,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f716])).

fof(f716,plain,(
    ! [X14,X13] : k3_xboole_0(X13,X14) = k3_xboole_0(k3_xboole_0(X13,X14),X13) ),
    inference(forward_demodulation,[],[f709,f18])).

fof(f709,plain,(
    ! [X14,X13] : k3_xboole_0(k3_xboole_0(X13,X14),X13) = k4_xboole_0(k3_xboole_0(X13,X14),k1_xboole_0) ),
    inference(superposition,[],[f21,f687])).

fof(f2820,plain,(
    ! [X2,X3] : k5_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(k3_xboole_0(X2,X3),X2),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f24,f716])).

fof(f210,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) ),
    inference(superposition,[],[f41,f26])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f20])).

fof(f955,plain,(
    ! [X21,X22] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k2_xboole_0(X21,X22)) ),
    inference(superposition,[],[f877,f49])).

fof(f49,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f24,f22])).

fof(f877,plain,(
    ! [X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,X20),X19) ),
    inference(superposition,[],[f89,f746])).

fof(f3664,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f3614,f3150])).

fof(f3614,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k5_xboole_0(X7,k4_xboole_0(X8,X7))) ),
    inference(superposition,[],[f3254,f22])).

fof(f3254,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f3231,f2860])).

fof(f3231,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f2956,f3158])).

fof(f3158,plain,(
    ! [X39,X40] : k5_xboole_0(X39,k2_xboole_0(X40,X39)) = k4_xboole_0(X40,X39) ),
    inference(backward_demodulation,[],[f2366,f3149])).

fof(f2366,plain,(
    ! [X39,X40] : k5_xboole_0(X40,k3_xboole_0(X40,X39)) = k5_xboole_0(X39,k2_xboole_0(X40,X39)) ),
    inference(superposition,[],[f128,f210])).

fof(f3188,plain,(
    ! [X2,X1] : k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1))) = k2_xboole_0(X2,X1) ),
    inference(backward_demodulation,[],[f49,f3150])).

fof(f4388,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f16,f3150])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:43:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (21295)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (21294)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (21304)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (21296)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (21303)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (21302)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (21291)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (21300)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (21301)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (21292)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (21293)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (21299)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (21299)Refutation not found, incomplete strategy% (21299)------------------------------
% 0.22/0.50  % (21299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21299)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (21299)Memory used [KB]: 10490
% 0.22/0.51  % (21299)Time elapsed: 0.064 s
% 0.22/0.51  % (21299)------------------------------
% 0.22/0.51  % (21299)------------------------------
% 0.22/0.54  % (21305)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.54  % (21288)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.54  % (21297)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.54  % (21290)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.54  % (21289)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.60/0.56  % (21298)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 2.40/0.70  % (21291)Refutation found. Thanks to Tanya!
% 2.40/0.70  % SZS status Theorem for theBenchmark
% 2.40/0.70  % SZS output start Proof for theBenchmark
% 2.40/0.70  fof(f4434,plain,(
% 2.40/0.70    $false),
% 2.40/0.70    inference(subsumption_resolution,[],[f4388,f3845])).
% 2.40/0.70  fof(f3845,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 2.40/0.70    inference(superposition,[],[f3666,f18])).
% 2.40/0.70  fof(f18,plain,(
% 2.40/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.40/0.70    inference(cnf_transformation,[],[f5])).
% 2.40/0.70  fof(f5,axiom,(
% 2.40/0.70    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.40/0.70  fof(f3666,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k4_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 2.40/0.70    inference(backward_demodulation,[],[f3188,f3665])).
% 2.40/0.70  fof(f3665,plain,(
% 2.40/0.70    ( ! [X8,X7] : (k1_xboole_0 = k3_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f3664,f3194])).
% 2.40/0.70  fof(f3194,plain,(
% 2.40/0.70    ( ! [X21,X22] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X21,X22))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f955,f3150])).
% 2.40/0.70  fof(f3150,plain,(
% 2.40/0.70    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f210,f3149])).
% 2.40/0.70  fof(f3149,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f2843,f3148])).
% 2.40/0.70  fof(f3148,plain,(
% 2.40/0.70    ( ! [X12,X13] : (k4_xboole_0(X12,X13) = k4_xboole_0(X12,k3_xboole_0(X12,X13))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f3147,f2860])).
% 2.40/0.70  fof(f2860,plain,(
% 2.40/0.70    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f2848,f2859])).
% 2.40/0.70  fof(f2859,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2850,f128])).
% 2.40/0.70  fof(f128,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.40/0.70    inference(forward_demodulation,[],[f125,f61])).
% 2.40/0.70  fof(f61,plain,(
% 2.40/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.40/0.70    inference(backward_demodulation,[],[f47,f60])).
% 2.40/0.70  fof(f60,plain,(
% 2.40/0.70    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f59,f27])).
% 2.40/0.70  fof(f27,plain,(
% 2.40/0.70    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.40/0.70    inference(superposition,[],[f19,f17])).
% 2.40/0.70  fof(f17,plain,(
% 2.40/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.40/0.70    inference(cnf_transformation,[],[f3])).
% 2.40/0.70  fof(f3,axiom,(
% 2.40/0.70    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.40/0.70  fof(f19,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f7])).
% 2.40/0.70  fof(f7,axiom,(
% 2.40/0.70    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.40/0.70  fof(f59,plain,(
% 2.40/0.70    ( ! [X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f51,f39])).
% 2.40/0.70  fof(f39,plain,(
% 2.40/0.70    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.40/0.70    inference(forward_demodulation,[],[f35,f17])).
% 2.40/0.70  fof(f35,plain,(
% 2.40/0.70    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)) )),
% 2.40/0.70    inference(superposition,[],[f22,f27])).
% 2.40/0.70  fof(f22,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f4])).
% 2.40/0.70  fof(f4,axiom,(
% 2.40/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.40/0.70  fof(f51,plain,(
% 2.40/0.70    ( ! [X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(k2_xboole_0(X1,X1),X1)) )),
% 2.40/0.70    inference(superposition,[],[f24,f32])).
% 2.40/0.70  fof(f32,plain,(
% 2.40/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.40/0.70    inference(forward_demodulation,[],[f28,f18])).
% 2.40/0.70  fof(f28,plain,(
% 2.40/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 2.40/0.70    inference(superposition,[],[f21,f27])).
% 2.40/0.70  fof(f21,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f8])).
% 2.40/0.70  fof(f8,axiom,(
% 2.40/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.40/0.70  fof(f24,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f2])).
% 2.40/0.70  fof(f2,axiom,(
% 2.40/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.40/0.70  fof(f47,plain,(
% 2.40/0.70    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.40/0.70    inference(forward_demodulation,[],[f46,f39])).
% 2.40/0.70  fof(f46,plain,(
% 2.40/0.70    ( ! [X0] : (k2_xboole_0(X0,X0) = k5_xboole_0(k5_xboole_0(X0,X0),X0)) )),
% 2.40/0.70    inference(superposition,[],[f23,f32])).
% 2.40/0.70  fof(f23,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f10])).
% 2.40/0.70  fof(f10,axiom,(
% 2.40/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.40/0.70  fof(f125,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(superposition,[],[f26,f60])).
% 2.40/0.70  fof(f26,plain,(
% 2.40/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f9])).
% 2.40/0.70  fof(f9,axiom,(
% 2.40/0.70    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.40/0.70  fof(f2850,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f1023,f2844])).
% 2.40/0.70  fof(f2844,plain,(
% 2.40/0.70    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k5_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f30,f2843])).
% 2.40/0.70  fof(f30,plain,(
% 2.40/0.70    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 2.40/0.70    inference(superposition,[],[f21,f21])).
% 2.40/0.70  fof(f1023,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k3_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1022,f30])).
% 2.40/0.70  fof(f1022,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(X1,k4_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f985,f883])).
% 2.40/0.70  fof(f883,plain,(
% 2.40/0.70    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f177,f872])).
% 2.40/0.70  fof(f872,plain,(
% 2.40/0.70    ( ! [X6,X5] : (k4_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X5,X6))) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 2.40/0.70    inference(superposition,[],[f24,f746])).
% 2.40/0.70  fof(f746,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.40/0.70    inference(forward_demodulation,[],[f723,f17])).
% 2.40/0.70  fof(f723,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(superposition,[],[f80,f89])).
% 2.40/0.70  fof(f89,plain,(
% 2.40/0.70    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,X3))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f75,f22])).
% 2.40/0.70  fof(f75,plain,(
% 2.40/0.70    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k4_xboole_0(X3,X4)))) )),
% 2.40/0.70    inference(superposition,[],[f25,f27])).
% 2.40/0.70  fof(f25,plain,(
% 2.40/0.70    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.40/0.70    inference(cnf_transformation,[],[f6])).
% 2.40/0.70  fof(f6,axiom,(
% 2.40/0.70    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.40/0.70  fof(f80,plain,(
% 2.40/0.70    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 2.40/0.70    inference(superposition,[],[f22,f25])).
% 2.40/0.70  fof(f177,plain,(
% 2.40/0.70    ( ! [X6,X5] : (k3_xboole_0(X5,k3_xboole_0(X5,X6)) = k4_xboole_0(X5,k3_xboole_0(X5,k4_xboole_0(X5,X6)))) )),
% 2.40/0.70    inference(superposition,[],[f21,f30])).
% 2.40/0.70  fof(f985,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k3_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X1,X2))) = k4_xboole_0(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 2.40/0.70    inference(superposition,[],[f53,f715])).
% 2.40/0.70  fof(f715,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k2_xboole_0(X11,k3_xboole_0(X11,X12)) = X11) )),
% 2.40/0.70    inference(forward_demodulation,[],[f708,f17])).
% 2.40/0.70  fof(f708,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k2_xboole_0(X11,k3_xboole_0(X11,X12)) = k2_xboole_0(X11,k1_xboole_0)) )),
% 2.40/0.70    inference(superposition,[],[f22,f687])).
% 2.40/0.70  fof(f687,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f686,f27])).
% 2.40/0.70  fof(f686,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f660,f71])).
% 2.40/0.70  fof(f71,plain,(
% 2.40/0.70    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k2_xboole_0(k4_xboole_0(X5,X6),X7)) = k4_xboole_0(k3_xboole_0(X5,X6),X7)) )),
% 2.40/0.70    inference(superposition,[],[f25,f21])).
% 2.40/0.70  fof(f660,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 2.40/0.70    inference(superposition,[],[f71,f37])).
% 2.40/0.70  fof(f37,plain,(
% 2.40/0.70    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X4))) )),
% 2.40/0.70    inference(superposition,[],[f22,f21])).
% 2.40/0.70  fof(f53,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k3_xboole_0(k2_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(superposition,[],[f21,f24])).
% 2.40/0.70  fof(f2848,plain,(
% 2.40/0.70    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k5_xboole_0(X5,k3_xboole_0(X5,X6)))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f872,f2844])).
% 2.40/0.70  fof(f3147,plain,(
% 2.40/0.70    ( ! [X12,X13] : (k4_xboole_0(X12,X13) = k4_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f3146,f128])).
% 2.40/0.70  fof(f3146,plain,(
% 2.40/0.70    ( ! [X12,X13] : (k4_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13))) = k5_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f3081,f103])).
% 2.40/0.70  fof(f103,plain,(
% 2.40/0.70    ( ! [X6,X7,X5] : (k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))) )),
% 2.40/0.70    inference(superposition,[],[f26,f20])).
% 2.40/0.70  fof(f20,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.40/0.70    inference(cnf_transformation,[],[f1])).
% 2.40/0.70  fof(f1,axiom,(
% 2.40/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.40/0.70  fof(f3081,plain,(
% 2.40/0.70    ( ! [X12,X13] : (k4_xboole_0(X12,k5_xboole_0(X12,k4_xboole_0(X12,X13))) = k5_xboole_0(X12,k5_xboole_0(k4_xboole_0(X12,X13),X12))) )),
% 2.40/0.70    inference(superposition,[],[f2956,f746])).
% 2.40/0.70  fof(f2956,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(X3,k2_xboole_0(X2,X3)))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f53,f2955])).
% 2.40/0.70  fof(f2955,plain,(
% 2.40/0.70    ( ! [X35,X36] : (k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(X35,k5_xboole_0(X36,k2_xboole_0(X35,X36)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2954,f26])).
% 2.40/0.70  fof(f2954,plain,(
% 2.40/0.70    ( ! [X35,X36] : (k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(k5_xboole_0(X35,X36),k2_xboole_0(X35,X36))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2953,f20])).
% 2.40/0.70  fof(f2953,plain,(
% 2.40/0.70    ( ! [X35,X36] : (k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(k2_xboole_0(X35,X36),k5_xboole_0(X35,X36))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2952,f1507])).
% 2.40/0.70  fof(f1507,plain,(
% 2.40/0.70    ( ! [X39,X40] : (k5_xboole_0(X39,X40) = k3_xboole_0(k2_xboole_0(X39,X40),k5_xboole_0(X39,X40))) )),
% 2.40/0.70    inference(superposition,[],[f1193,f1445])).
% 2.40/0.70  fof(f1445,plain,(
% 2.40/0.70    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1444,f61])).
% 2.40/0.70  fof(f1444,plain,(
% 2.40/0.70    ( ! [X4,X5] : (k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X4,X5))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1442,f20])).
% 2.40/0.70  fof(f1442,plain,(
% 2.40/0.70    ( ! [X4,X5] : (k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k1_xboole_0)) )),
% 2.40/0.70    inference(backward_demodulation,[],[f43,f1422])).
% 2.40/0.70  fof(f1422,plain,(
% 2.40/0.70    ( ! [X24,X23] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X23,X24),k3_xboole_0(X23,X24))) )),
% 2.40/0.70    inference(superposition,[],[f1271,f24])).
% 2.40/0.70  fof(f1271,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1219,f27])).
% 2.40/0.70  fof(f1219,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X1,X0),X0) = k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 2.40/0.70    inference(superposition,[],[f81,f39])).
% 2.40/0.70  fof(f81,plain,(
% 2.40/0.70    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),X7) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 2.40/0.70    inference(superposition,[],[f21,f25])).
% 2.40/0.70  fof(f43,plain,(
% 2.40/0.70    ( ! [X4,X5] : (k2_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = k5_xboole_0(k2_xboole_0(X4,X5),k3_xboole_0(k5_xboole_0(X4,X5),k3_xboole_0(X4,X5)))) )),
% 2.40/0.70    inference(superposition,[],[f23,f23])).
% 2.40/0.70  fof(f1193,plain,(
% 2.40/0.70    ( ! [X12,X13] : (k3_xboole_0(k2_xboole_0(X12,X13),X12) = X12) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1192,f33])).
% 2.40/0.70  fof(f33,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 2.40/0.70    inference(forward_demodulation,[],[f29,f18])).
% 2.40/0.70  fof(f29,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k1_xboole_0)) )),
% 2.40/0.70    inference(superposition,[],[f21,f19])).
% 2.40/0.70  fof(f1192,plain,(
% 2.40/0.70    ( ! [X12,X13] : (k3_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(X12,k2_xboole_0(X12,X13))) = X12) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1175,f1033])).
% 2.40/0.70  fof(f1033,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = X11) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1032,f55])).
% 2.40/0.70  fof(f55,plain,(
% 2.40/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.40/0.70    inference(forward_demodulation,[],[f54,f18])).
% 2.40/0.70  fof(f54,plain,(
% 2.40/0.70    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f48,f34])).
% 2.40/0.70  fof(f34,plain,(
% 2.40/0.70    ( ! [X5] : (k1_xboole_0 = k3_xboole_0(X5,k1_xboole_0)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f31,f27])).
% 2.40/0.70  fof(f31,plain,(
% 2.40/0.70    ( ! [X5] : (k3_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,X5)) )),
% 2.40/0.70    inference(superposition,[],[f21,f18])).
% 2.40/0.70  fof(f48,plain,(
% 2.40/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 2.40/0.70    inference(superposition,[],[f24,f17])).
% 2.40/0.70  fof(f1032,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k5_xboole_0(X11,k1_xboole_0) = k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1031,f60])).
% 2.40/0.70  fof(f1031,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = k5_xboole_0(X11,k5_xboole_0(k2_xboole_0(X11,X12),k2_xboole_0(X11,X12)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1030,f103])).
% 2.40/0.70  fof(f1030,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = k5_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1029,f373])).
% 2.40/0.70  fof(f373,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 2.40/0.70    inference(backward_demodulation,[],[f122,f371])).
% 2.40/0.70  fof(f371,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f349,f321])).
% 2.40/0.70  fof(f321,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.40/0.70    inference(superposition,[],[f128,f20])).
% 2.40/0.70  fof(f349,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k2_xboole_0(X2,k2_xboole_0(X2,X3)) = k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(X2,X3),X2))) )),
% 2.40/0.70    inference(superposition,[],[f102,f33])).
% 2.40/0.70  fof(f102,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 2.40/0.70    inference(superposition,[],[f26,f23])).
% 2.40/0.70  fof(f122,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X0,X1)),X0)) )),
% 2.40/0.70    inference(superposition,[],[f24,f33])).
% 2.40/0.70  fof(f1029,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12))) = k5_xboole_0(k2_xboole_0(X11,X12),k4_xboole_0(k2_xboole_0(X11,X12),X11))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f1028,f883])).
% 2.40/0.70  fof(f1028,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k3_xboole_0(k2_xboole_0(X11,X12),k3_xboole_0(k2_xboole_0(X11,X12),X11)) = k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(X11,k2_xboole_0(X11,X12)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f990,f20])).
% 2.40/0.70  fof(f990,plain,(
% 2.40/0.70    ( ! [X12,X11] : (k3_xboole_0(k2_xboole_0(X11,X12),k3_xboole_0(k2_xboole_0(X11,X12),X11)) = k4_xboole_0(k2_xboole_0(X11,X12),k5_xboole_0(k2_xboole_0(X11,X12),X11))) )),
% 2.40/0.70    inference(superposition,[],[f53,f40])).
% 2.40/0.70  fof(f40,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(k2_xboole_0(X1,X2),X1)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f36,f17])).
% 2.40/0.70  fof(f36,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k2_xboole_0(k2_xboole_0(X1,X2),X1) = k2_xboole_0(k2_xboole_0(X1,X2),k1_xboole_0)) )),
% 2.40/0.70    inference(superposition,[],[f22,f19])).
% 2.40/0.70  fof(f1175,plain,(
% 2.40/0.70    ( ! [X12,X13] : (k3_xboole_0(k2_xboole_0(X12,X13),k3_xboole_0(X12,k2_xboole_0(X12,X13))) = k4_xboole_0(k2_xboole_0(X12,X13),k5_xboole_0(X12,k2_xboole_0(X12,X13)))) )),
% 2.40/0.70    inference(superposition,[],[f53,f371])).
% 2.40/0.70  fof(f2952,plain,(
% 2.40/0.70    ( ! [X35,X36] : (k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)) = k5_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(k2_xboole_0(X35,X36),k5_xboole_0(X35,X36)))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2903,f2861])).
% 2.40/0.70  fof(f2861,plain,(
% 2.40/0.70    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X5,X6))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f883,f2860])).
% 2.40/0.70  fof(f2903,plain,(
% 2.40/0.70    ( ! [X35,X36] : (k5_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(k2_xboole_0(X35,X36),k5_xboole_0(X35,X36))) = k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(k2_xboole_0(X35,X36),k3_xboole_0(X35,X36)))) )),
% 2.40/0.70    inference(superposition,[],[f2844,f53])).
% 2.40/0.70  fof(f2843,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2842,f20])).
% 2.40/0.70  fof(f2842,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k5_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2820,f2833])).
% 2.40/0.70  fof(f2833,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 2.40/0.70    inference(forward_demodulation,[],[f2819,f392])).
% 2.40/0.70  fof(f392,plain,(
% 2.40/0.70    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 2.40/0.70    inference(superposition,[],[f321,f321])).
% 2.40/0.70  fof(f2819,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(superposition,[],[f23,f716])).
% 2.40/0.70  fof(f716,plain,(
% 2.40/0.70    ( ! [X14,X13] : (k3_xboole_0(X13,X14) = k3_xboole_0(k3_xboole_0(X13,X14),X13)) )),
% 2.40/0.70    inference(forward_demodulation,[],[f709,f18])).
% 2.40/0.70  fof(f709,plain,(
% 2.40/0.70    ( ! [X14,X13] : (k3_xboole_0(k3_xboole_0(X13,X14),X13) = k4_xboole_0(k3_xboole_0(X13,X14),k1_xboole_0)) )),
% 2.40/0.70    inference(superposition,[],[f21,f687])).
% 2.40/0.70  fof(f2820,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k5_xboole_0(k3_xboole_0(X2,X3),X2) = k4_xboole_0(k2_xboole_0(k3_xboole_0(X2,X3),X2),k3_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(superposition,[],[f24,f716])).
% 2.40/0.70  fof(f210,plain,(
% 2.40/0.70    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))) )),
% 2.40/0.70    inference(superposition,[],[f41,f26])).
% 2.40/0.70  fof(f41,plain,(
% 2.40/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1))) )),
% 2.40/0.70    inference(superposition,[],[f23,f20])).
% 2.40/0.70  fof(f955,plain,(
% 2.40/0.70    ( ! [X21,X22] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X21,k4_xboole_0(X22,X21)),k2_xboole_0(X21,X22))) )),
% 2.40/0.70    inference(superposition,[],[f877,f49])).
% 2.40/0.70  fof(f49,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.40/0.70    inference(superposition,[],[f24,f22])).
% 2.40/0.70  fof(f877,plain,(
% 2.40/0.70    ( ! [X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,X20),X19)) )),
% 2.40/0.70    inference(superposition,[],[f89,f746])).
% 2.40/0.70  fof(f3664,plain,(
% 2.40/0.70    ( ! [X8,X7] : (k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X8,X7))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f3614,f3150])).
% 2.40/0.70  fof(f3614,plain,(
% 2.40/0.70    ( ! [X8,X7] : (k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k5_xboole_0(X7,k4_xboole_0(X8,X7)))) )),
% 2.40/0.70    inference(superposition,[],[f3254,f22])).
% 2.40/0.70  fof(f3254,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(forward_demodulation,[],[f3231,f2860])).
% 2.40/0.70  fof(f3231,plain,(
% 2.40/0.70    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.40/0.70    inference(backward_demodulation,[],[f2956,f3158])).
% 2.40/0.70  fof(f3158,plain,(
% 2.40/0.70    ( ! [X39,X40] : (k5_xboole_0(X39,k2_xboole_0(X40,X39)) = k4_xboole_0(X40,X39)) )),
% 2.40/0.70    inference(backward_demodulation,[],[f2366,f3149])).
% 2.40/0.70  fof(f2366,plain,(
% 2.40/0.70    ( ! [X39,X40] : (k5_xboole_0(X40,k3_xboole_0(X40,X39)) = k5_xboole_0(X39,k2_xboole_0(X40,X39))) )),
% 2.40/0.70    inference(superposition,[],[f128,f210])).
% 2.40/0.70  fof(f3188,plain,(
% 2.40/0.70    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X2,X1))) = k2_xboole_0(X2,X1)) )),
% 2.40/0.70    inference(backward_demodulation,[],[f49,f3150])).
% 2.40/0.70  fof(f4388,plain,(
% 2.40/0.70    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK1,sK0)),
% 2.40/0.70    inference(superposition,[],[f16,f3150])).
% 2.40/0.70  fof(f16,plain,(
% 2.40/0.70    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.40/0.70    inference(cnf_transformation,[],[f15])).
% 2.40/0.70  fof(f15,plain,(
% 2.40/0.70    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.40/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 2.40/0.70  fof(f14,plain,(
% 2.40/0.70    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.40/0.70    introduced(choice_axiom,[])).
% 2.40/0.70  fof(f13,plain,(
% 2.40/0.70    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.40/0.70    inference(ennf_transformation,[],[f12])).
% 2.40/0.70  fof(f12,negated_conjecture,(
% 2.40/0.70    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.40/0.70    inference(negated_conjecture,[],[f11])).
% 2.40/0.70  fof(f11,conjecture,(
% 2.40/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.40/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.40/0.70  % SZS output end Proof for theBenchmark
% 2.40/0.70  % (21291)------------------------------
% 2.40/0.70  % (21291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.70  % (21291)Termination reason: Refutation
% 2.40/0.70  
% 2.40/0.70  % (21291)Memory used [KB]: 6012
% 2.40/0.70  % (21291)Time elapsed: 0.253 s
% 2.40/0.70  % (21291)------------------------------
% 2.40/0.70  % (21291)------------------------------
% 2.40/0.71  % (21287)Success in time 0.343 s
%------------------------------------------------------------------------------
