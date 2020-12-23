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
% DateTime   : Thu Dec  3 12:32:25 EST 2020

% Result     : Theorem 8.19s
% Output     : Refutation 8.19s
% Verified   : 
% Statistics : Number of formulae       :  141 (34932 expanded)
%              Number of leaves         :   13 (11644 expanded)
%              Depth                    :   40
%              Number of atoms          :  142 (34933 expanded)
%              Number of equality atoms :  141 (34932 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22851,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18,f22850])).

fof(f22850,plain,(
    ! [X57,X56] : k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k3_xboole_0(X56,X57)) ),
    inference(forward_demodulation,[],[f22842,f164])).

fof(f164,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(superposition,[],[f160,f24])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f160,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f141,f112])).

fof(f112,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f35,f111])).

fof(f111,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f110,f76])).

fof(f76,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(forward_demodulation,[],[f74,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f52,f19])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f23,f48])).

fof(f48,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f24,f37])).

fof(f37,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f35,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f74,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f23,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f54,f62])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f60,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f60,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f56,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f56,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f25,f48])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f54,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f25,f20])).

fof(f110,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f99,f75])).

fof(f75,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f73,f20])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f25,f70])).

fof(f99,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f26,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f77,f70])).

fof(f77,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f75])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f23,f20])).

fof(f141,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f27,f80])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f22842,plain,(
    ! [X57,X56] : k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(X56,X57))) ),
    inference(backward_demodulation,[],[f22674,f22823])).

fof(f22823,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f22562,f22822])).

fof(f22822,plain,(
    ! [X2,X1] : k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f22719,f22507])).

fof(f22507,plain,(
    ! [X47,X46] : k4_xboole_0(X46,X47) = k4_xboole_0(k5_xboole_0(X46,X47),X47) ),
    inference(backward_demodulation,[],[f22264,f22506])).

fof(f22506,plain,(
    ! [X28,X27] : k4_xboole_0(X27,X28) = k3_xboole_0(k5_xboole_0(X27,X28),X27) ),
    inference(forward_demodulation,[],[f22290,f355])).

fof(f355,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X13) = k5_xboole_0(k3_xboole_0(X12,X13),X12) ),
    inference(superposition,[],[f224,f164])).

fof(f224,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f209,f209])).

fof(f209,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f197,f53])).

fof(f197,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f160,f149])).

fof(f149,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f27,f80])).

fof(f22290,plain,(
    ! [X28,X27] : k3_xboole_0(k5_xboole_0(X27,X28),X27) = k5_xboole_0(k3_xboole_0(X27,X28),X27) ),
    inference(superposition,[],[f291,f21510])).

fof(f21510,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f21292,f416])).

fof(f416,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f410,f164])).

fof(f410,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k3_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f164,f368])).

fof(f368,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f360,f21])).

fof(f360,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(backward_demodulation,[],[f55,f359])).

fof(f359,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f343,f24])).

fof(f343,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f164,f25])).

fof(f55,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f25,f25])).

fof(f21292,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f4437,f3144])).

fof(f3144,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k5_xboole_0(X24,X25)) = k3_xboole_0(X25,X24) ),
    inference(backward_demodulation,[],[f1356,f3141])).

fof(f3141,plain,(
    ! [X28,X29] : k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k3_xboole_0(X29,X28) ),
    inference(forward_demodulation,[],[f3140,f164])).

fof(f3140,plain,(
    ! [X28,X29] : k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k5_xboole_0(X29,k4_xboole_0(X29,X28)) ),
    inference(forward_demodulation,[],[f3139,f231])).

fof(f231,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f160,f209])).

fof(f3139,plain,(
    ! [X28,X29] : k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k5_xboole_0(k4_xboole_0(X29,X28),X29) ),
    inference(backward_demodulation,[],[f3132,f3104])).

fof(f3104,plain,(
    ! [X4,X2,X3] : k5_xboole_0(k4_xboole_0(X3,X2),X4) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X4)) ),
    inference(superposition,[],[f27,f292])).

fof(f292,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f224,f23])).

fof(f3132,plain,(
    ! [X28,X29] : k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k5_xboole_0(k2_xboole_0(X28,X29),k5_xboole_0(X28,X29)) ),
    inference(forward_demodulation,[],[f3097,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f3097,plain,(
    ! [X28,X29] : k4_xboole_0(k3_xboole_0(X28,X29),k5_xboole_0(X28,X29)) = k5_xboole_0(k2_xboole_0(X28,X29),k5_xboole_0(X28,X29)) ),
    inference(superposition,[],[f292,f26])).

fof(f1356,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k5_xboole_0(X24,X25)) = k3_xboole_0(X24,k4_xboole_0(X25,k5_xboole_0(X24,X25))) ),
    inference(forward_demodulation,[],[f1328,f29])).

fof(f1328,plain,(
    ! [X24,X25] : k4_xboole_0(k3_xboole_0(X24,X25),k5_xboole_0(X24,X25)) = k4_xboole_0(k2_xboole_0(X24,X25),k5_xboole_0(X24,X25)) ),
    inference(superposition,[],[f940,f26])).

fof(f940,plain,(
    ! [X12,X13] : k4_xboole_0(X13,X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(forward_demodulation,[],[f926,f292])).

fof(f926,plain,(
    ! [X12,X13] : k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12) ),
    inference(superposition,[],[f46,f893])).

fof(f893,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f876,f20])).

fof(f876,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f25,f842])).

fof(f842,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f805,f48])).

fof(f805,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f28,f70])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f21])).

fof(f4437,plain,(
    ! [X26,X27,X25] : k3_xboole_0(X25,k4_xboole_0(k2_xboole_0(X25,X26),X27)) = k4_xboole_0(X25,X27) ),
    inference(superposition,[],[f29,f893])).

fof(f291,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(superposition,[],[f224,f46])).

fof(f22264,plain,(
    ! [X47,X46] : k4_xboole_0(k5_xboole_0(X46,X47),X47) = k3_xboole_0(k5_xboole_0(X46,X47),X46) ),
    inference(superposition,[],[f21510,f224])).

fof(f22719,plain,(
    ! [X2,X1] : k4_xboole_0(k5_xboole_0(X2,X1),X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f166,f22409])).

fof(f22409,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k5_xboole_0(X7,X6)) = k2_xboole_0(X7,X6) ),
    inference(forward_demodulation,[],[f22400,f946])).

fof(f946,plain,(
    ! [X33,X32] : k2_xboole_0(X32,X33) = k2_xboole_0(X32,k4_xboole_0(X33,X32)) ),
    inference(forward_demodulation,[],[f935,f940])).

fof(f935,plain,(
    ! [X33,X32] : k2_xboole_0(X32,X33) = k2_xboole_0(X32,k4_xboole_0(k2_xboole_0(X32,X33),X32)) ),
    inference(superposition,[],[f439,f893])).

fof(f439,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f394,f21])).

fof(f394,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f384,f359])).

fof(f384,plain,(
    ! [X4,X3] : k2_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X3,X4))) = X3 ),
    inference(superposition,[],[f379,f25])).

fof(f379,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(backward_demodulation,[],[f113,f378])).

fof(f378,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f372,f164])).

fof(f372,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f164,f360])).

fof(f113,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))) = X1 ),
    inference(forward_demodulation,[],[f100,f22])).

fof(f100,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[],[f26,f24])).

fof(f22400,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k5_xboole_0(X7,X6)) = k2_xboole_0(X7,k4_xboole_0(X6,X7)) ),
    inference(backward_demodulation,[],[f233,f22249])).

fof(f22249,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k3_xboole_0(X17,k5_xboole_0(X18,X17)) ),
    inference(superposition,[],[f21510,f209])).

fof(f233,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k5_xboole_0(X7,X6)) = k2_xboole_0(X7,k3_xboole_0(X6,k5_xboole_0(X7,X6))) ),
    inference(superposition,[],[f26,f209])).

fof(f166,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f160,f23])).

fof(f22562,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f166,f22357])).

fof(f22357,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k5_xboole_0(X3,X4)) = k2_xboole_0(X4,X3) ),
    inference(forward_demodulation,[],[f22348,f946])).

fof(f22348,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k5_xboole_0(X3,X4)) = k2_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f174,f22248])).

fof(f22248,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k3_xboole_0(X15,k5_xboole_0(X15,X16)) ),
    inference(superposition,[],[f21510,f160])).

fof(f174,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k5_xboole_0(X3,X4)) = k2_xboole_0(X4,k3_xboole_0(X3,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f26,f160])).

fof(f22674,plain,(
    ! [X57,X56] : k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k5_xboole_0(X57,X56),X57))) ),
    inference(backward_demodulation,[],[f21425,f22659])).

fof(f22659,plain,(
    ! [X33,X32] : k4_xboole_0(k2_xboole_0(X32,X33),X33) = k4_xboole_0(k5_xboole_0(X33,X32),X33) ),
    inference(backward_demodulation,[],[f3166,f22562])).

fof(f3166,plain,(
    ! [X33,X32] : k4_xboole_0(k2_xboole_0(X32,X33),X33) = k5_xboole_0(X33,k2_xboole_0(X32,X33)) ),
    inference(superposition,[],[f355,f1029])).

fof(f1029,plain,(
    ! [X10,X11] : k3_xboole_0(k2_xboole_0(X11,X10),X10) = X10 ),
    inference(forward_demodulation,[],[f1012,f53])).

fof(f1012,plain,(
    ! [X10,X11] : k3_xboole_0(k2_xboole_0(X11,X10),X10) = k5_xboole_0(X10,k1_xboole_0) ),
    inference(superposition,[],[f165,f815])).

fof(f815,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f28,f534])).

fof(f534,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f510,f80])).

fof(f510,plain,(
    ! [X6,X5] : k5_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f166,f395])).

fof(f395,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(backward_demodulation,[],[f366,f394])).

fof(f366,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f350,f359])).

fof(f350,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f26,f164])).

fof(f165,plain,(
    ! [X4,X3] : k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f160,f46])).

fof(f21425,plain,(
    ! [X57,X56] : k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X56,X57),X57))) ),
    inference(forward_demodulation,[],[f21424,f920])).

fof(f920,plain,(
    ! [X23,X22] : k5_xboole_0(X22,X23) = k3_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23)) ),
    inference(superposition,[],[f893,f26])).

fof(f21424,plain,(
    ! [X57,X56] : k3_xboole_0(k5_xboole_0(X56,X57),k2_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X56,X57),X57))) ),
    inference(forward_demodulation,[],[f21423,f21])).

fof(f21423,plain,(
    ! [X57,X56] : k3_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X56,X57),X57))) ),
    inference(forward_demodulation,[],[f21422,f3166])).

fof(f21422,plain,(
    ! [X57,X56] : k3_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k5_xboole_0(X57,k2_xboole_0(X56,X57)))) ),
    inference(forward_demodulation,[],[f21253,f27])).

fof(f21253,plain,(
    ! [X57,X56] : k3_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(k5_xboole_0(X56,X57),k2_xboole_0(X56,X57))) ),
    inference(superposition,[],[f3144,f1302])).

fof(f1302,plain,(
    ! [X24,X25] : k2_xboole_0(X24,X25) = k2_xboole_0(k5_xboole_0(X24,X25),k2_xboole_0(X24,X25)) ),
    inference(superposition,[],[f930,f26])).

fof(f930,plain,(
    ! [X21,X20] : k2_xboole_0(X20,X21) = k2_xboole_0(X20,k2_xboole_0(X20,X21)) ),
    inference(superposition,[],[f275,f893])).

fof(f275,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),X0) = X0 ),
    inference(superposition,[],[f270,f21])).

fof(f270,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1 ),
    inference(superposition,[],[f264,f25])).

fof(f264,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(backward_demodulation,[],[f58,f247])).

fof(f247,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f223,f24])).

fof(f223,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7 ),
    inference(superposition,[],[f209,f160])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f23,f25])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (26881)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (26877)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.45  % (26879)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (26889)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (26875)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (26888)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (26880)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (26878)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (26874)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (26885)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (26891)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (26882)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (26885)Refutation not found, incomplete strategy% (26885)------------------------------
% 0.20/0.48  % (26885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (26885)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (26885)Memory used [KB]: 10490
% 0.20/0.48  % (26885)Time elapsed: 0.072 s
% 0.20/0.48  % (26885)------------------------------
% 0.20/0.48  % (26885)------------------------------
% 0.20/0.49  % (26883)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (26887)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (26886)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (26884)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (26890)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (26876)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 5.30/1.02  % (26878)Time limit reached!
% 5.30/1.02  % (26878)------------------------------
% 5.30/1.02  % (26878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.30/1.02  % (26878)Termination reason: Time limit
% 5.30/1.02  % (26878)Termination phase: Saturation
% 5.30/1.02  
% 5.30/1.02  % (26878)Memory used [KB]: 15991
% 5.30/1.02  % (26878)Time elapsed: 0.600 s
% 5.30/1.02  % (26878)------------------------------
% 5.30/1.02  % (26878)------------------------------
% 8.19/1.42  % (26890)Refutation found. Thanks to Tanya!
% 8.19/1.42  % SZS status Theorem for theBenchmark
% 8.19/1.42  % SZS output start Proof for theBenchmark
% 8.19/1.42  fof(f22851,plain,(
% 8.19/1.42    $false),
% 8.19/1.42    inference(subsumption_resolution,[],[f18,f22850])).
% 8.19/1.42  fof(f22850,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k3_xboole_0(X56,X57))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f22842,f164])).
% 8.19/1.42  fof(f164,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(superposition,[],[f160,f24])).
% 8.19/1.42  fof(f24,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(cnf_transformation,[],[f2])).
% 8.19/1.42  fof(f2,axiom,(
% 8.19/1.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 8.19/1.42  fof(f160,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 8.19/1.42    inference(forward_demodulation,[],[f141,f112])).
% 8.19/1.42  fof(f112,plain,(
% 8.19/1.42    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 8.19/1.42    inference(backward_demodulation,[],[f35,f111])).
% 8.19/1.42  fof(f111,plain,(
% 8.19/1.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 8.19/1.42    inference(forward_demodulation,[],[f110,f76])).
% 8.19/1.42  fof(f76,plain,(
% 8.19/1.42    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 8.19/1.42    inference(forward_demodulation,[],[f74,f53])).
% 8.19/1.42  fof(f53,plain,(
% 8.19/1.42    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.19/1.42    inference(forward_demodulation,[],[f52,f19])).
% 8.19/1.42  fof(f19,plain,(
% 8.19/1.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.19/1.42    inference(cnf_transformation,[],[f4])).
% 8.19/1.42  fof(f4,axiom,(
% 8.19/1.42    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 8.19/1.42  fof(f52,plain,(
% 8.19/1.42    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 8.19/1.42    inference(superposition,[],[f23,f48])).
% 8.19/1.42  fof(f48,plain,(
% 8.19/1.42    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 8.19/1.42    inference(superposition,[],[f24,f37])).
% 8.19/1.42  fof(f37,plain,(
% 8.19/1.42    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X1))) )),
% 8.19/1.42    inference(superposition,[],[f35,f22])).
% 8.19/1.42  fof(f22,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 8.19/1.42    inference(cnf_transformation,[],[f5])).
% 8.19/1.42  fof(f5,axiom,(
% 8.19/1.42    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 8.19/1.42  fof(f23,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.19/1.42    inference(cnf_transformation,[],[f12])).
% 8.19/1.42  fof(f12,axiom,(
% 8.19/1.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 8.19/1.42  fof(f74,plain,(
% 8.19/1.42    ( ! [X1] : (k2_xboole_0(X1,X1) = k5_xboole_0(X1,k1_xboole_0)) )),
% 8.19/1.42    inference(superposition,[],[f23,f70])).
% 8.19/1.42  fof(f70,plain,(
% 8.19/1.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 8.19/1.42    inference(backward_demodulation,[],[f54,f62])).
% 8.19/1.42  fof(f62,plain,(
% 8.19/1.42    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 8.19/1.42    inference(superposition,[],[f60,f21])).
% 8.19/1.42  fof(f21,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.19/1.42    inference(cnf_transformation,[],[f1])).
% 8.19/1.42  fof(f1,axiom,(
% 8.19/1.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.19/1.42  fof(f60,plain,(
% 8.19/1.42    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f56,f20])).
% 8.19/1.42  fof(f20,plain,(
% 8.19/1.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.19/1.42    inference(cnf_transformation,[],[f6])).
% 8.19/1.42  fof(f6,axiom,(
% 8.19/1.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 8.19/1.42  fof(f56,plain,(
% 8.19/1.42    ( ! [X3] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,X3)) )),
% 8.19/1.42    inference(superposition,[],[f25,f48])).
% 8.19/1.42  fof(f25,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(cnf_transformation,[],[f8])).
% 8.19/1.42  fof(f8,axiom,(
% 8.19/1.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 8.19/1.42  fof(f54,plain,(
% 8.19/1.42    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 8.19/1.42    inference(superposition,[],[f25,f20])).
% 8.19/1.42  fof(f110,plain,(
% 8.19/1.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(X0,X0)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f99,f75])).
% 8.19/1.42  fof(f75,plain,(
% 8.19/1.42    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 8.19/1.42    inference(forward_demodulation,[],[f73,f20])).
% 8.19/1.42  fof(f73,plain,(
% 8.19/1.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 8.19/1.42    inference(superposition,[],[f25,f70])).
% 8.19/1.42  fof(f99,plain,(
% 8.19/1.42    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0))) )),
% 8.19/1.42    inference(superposition,[],[f26,f80])).
% 8.19/1.42  fof(f80,plain,(
% 8.19/1.42    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f77,f70])).
% 8.19/1.42  fof(f77,plain,(
% 8.19/1.42    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 8.19/1.42    inference(superposition,[],[f24,f75])).
% 8.19/1.42  fof(f26,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(cnf_transformation,[],[f11])).
% 8.19/1.42  fof(f11,axiom,(
% 8.19/1.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 8.19/1.42  fof(f35,plain,(
% 8.19/1.42    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 8.19/1.42    inference(superposition,[],[f23,f20])).
% 8.19/1.42  fof(f141,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 8.19/1.42    inference(superposition,[],[f27,f80])).
% 8.19/1.42  fof(f27,plain,(
% 8.19/1.42    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(cnf_transformation,[],[f10])).
% 8.19/1.42  fof(f10,axiom,(
% 8.19/1.42    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 8.19/1.42  fof(f22842,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(X56,X57)))) )),
% 8.19/1.42    inference(backward_demodulation,[],[f22674,f22823])).
% 8.19/1.42  fof(f22823,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 8.19/1.42    inference(backward_demodulation,[],[f22562,f22822])).
% 8.19/1.42  fof(f22822,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f22719,f22507])).
% 8.19/1.42  fof(f22507,plain,(
% 8.19/1.42    ( ! [X47,X46] : (k4_xboole_0(X46,X47) = k4_xboole_0(k5_xboole_0(X46,X47),X47)) )),
% 8.19/1.42    inference(backward_demodulation,[],[f22264,f22506])).
% 8.19/1.42  fof(f22506,plain,(
% 8.19/1.42    ( ! [X28,X27] : (k4_xboole_0(X27,X28) = k3_xboole_0(k5_xboole_0(X27,X28),X27)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f22290,f355])).
% 8.19/1.42  fof(f355,plain,(
% 8.19/1.42    ( ! [X12,X13] : (k4_xboole_0(X12,X13) = k5_xboole_0(k3_xboole_0(X12,X13),X12)) )),
% 8.19/1.42    inference(superposition,[],[f224,f164])).
% 8.19/1.42  fof(f224,plain,(
% 8.19/1.42    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 8.19/1.42    inference(superposition,[],[f209,f209])).
% 8.19/1.42  fof(f209,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 8.19/1.42    inference(forward_demodulation,[],[f197,f53])).
% 8.19/1.42  fof(f197,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(superposition,[],[f160,f149])).
% 8.19/1.42  fof(f149,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 8.19/1.42    inference(superposition,[],[f27,f80])).
% 8.19/1.42  fof(f22290,plain,(
% 8.19/1.42    ( ! [X28,X27] : (k3_xboole_0(k5_xboole_0(X27,X28),X27) = k5_xboole_0(k3_xboole_0(X27,X28),X27)) )),
% 8.19/1.42    inference(superposition,[],[f291,f21510])).
% 8.19/1.42  fof(f21510,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f21292,f416])).
% 8.19/1.42  fof(f416,plain,(
% 8.19/1.42    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f410,f164])).
% 8.19/1.42  fof(f410,plain,(
% 8.19/1.42    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(X5,X6)) = k3_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 8.19/1.42    inference(superposition,[],[f164,f368])).
% 8.19/1.42  fof(f368,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 8.19/1.42    inference(superposition,[],[f360,f21])).
% 8.19/1.42  fof(f360,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(backward_demodulation,[],[f55,f359])).
% 8.19/1.42  fof(f359,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f343,f24])).
% 8.19/1.42  fof(f343,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(superposition,[],[f164,f25])).
% 8.19/1.42  fof(f55,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(superposition,[],[f25,f25])).
% 8.19/1.42  fof(f21292,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(superposition,[],[f4437,f3144])).
% 8.19/1.42  fof(f3144,plain,(
% 8.19/1.42    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k5_xboole_0(X24,X25)) = k3_xboole_0(X25,X24)) )),
% 8.19/1.42    inference(backward_demodulation,[],[f1356,f3141])).
% 8.19/1.42  fof(f3141,plain,(
% 8.19/1.42    ( ! [X28,X29] : (k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k3_xboole_0(X29,X28)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f3140,f164])).
% 8.19/1.42  fof(f3140,plain,(
% 8.19/1.42    ( ! [X28,X29] : (k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k5_xboole_0(X29,k4_xboole_0(X29,X28))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f3139,f231])).
% 8.19/1.42  fof(f231,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 8.19/1.42    inference(superposition,[],[f160,f209])).
% 8.19/1.42  fof(f3139,plain,(
% 8.19/1.42    ( ! [X28,X29] : (k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k5_xboole_0(k4_xboole_0(X29,X28),X29)) )),
% 8.19/1.42    inference(backward_demodulation,[],[f3132,f3104])).
% 8.19/1.42  fof(f3104,plain,(
% 8.19/1.42    ( ! [X4,X2,X3] : (k5_xboole_0(k4_xboole_0(X3,X2),X4) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X4))) )),
% 8.19/1.42    inference(superposition,[],[f27,f292])).
% 8.19/1.42  fof(f292,plain,(
% 8.19/1.42    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k2_xboole_0(X5,X6),X5)) )),
% 8.19/1.42    inference(superposition,[],[f224,f23])).
% 8.19/1.42  fof(f3132,plain,(
% 8.19/1.42    ( ! [X28,X29] : (k3_xboole_0(X28,k4_xboole_0(X29,k5_xboole_0(X28,X29))) = k5_xboole_0(k2_xboole_0(X28,X29),k5_xboole_0(X28,X29))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f3097,f29])).
% 8.19/1.42  fof(f29,plain,(
% 8.19/1.42    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 8.19/1.42    inference(cnf_transformation,[],[f9])).
% 8.19/1.42  fof(f9,axiom,(
% 8.19/1.42    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 8.19/1.42  fof(f3097,plain,(
% 8.19/1.42    ( ! [X28,X29] : (k4_xboole_0(k3_xboole_0(X28,X29),k5_xboole_0(X28,X29)) = k5_xboole_0(k2_xboole_0(X28,X29),k5_xboole_0(X28,X29))) )),
% 8.19/1.42    inference(superposition,[],[f292,f26])).
% 8.19/1.42  fof(f1356,plain,(
% 8.19/1.42    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k5_xboole_0(X24,X25)) = k3_xboole_0(X24,k4_xboole_0(X25,k5_xboole_0(X24,X25)))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f1328,f29])).
% 8.19/1.42  fof(f1328,plain,(
% 8.19/1.42    ( ! [X24,X25] : (k4_xboole_0(k3_xboole_0(X24,X25),k5_xboole_0(X24,X25)) = k4_xboole_0(k2_xboole_0(X24,X25),k5_xboole_0(X24,X25))) )),
% 8.19/1.42    inference(superposition,[],[f940,f26])).
% 8.19/1.42  fof(f940,plain,(
% 8.19/1.42    ( ! [X12,X13] : (k4_xboole_0(X13,X12) = k4_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f926,f292])).
% 8.19/1.42  fof(f926,plain,(
% 8.19/1.42    ( ! [X12,X13] : (k4_xboole_0(k2_xboole_0(X12,X13),X12) = k5_xboole_0(k2_xboole_0(X12,X13),X12)) )),
% 8.19/1.42    inference(superposition,[],[f46,f893])).
% 8.19/1.42  fof(f893,plain,(
% 8.19/1.42    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2) )),
% 8.19/1.42    inference(forward_demodulation,[],[f876,f20])).
% 8.19/1.42  fof(f876,plain,(
% 8.19/1.42    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(X2,k1_xboole_0)) )),
% 8.19/1.42    inference(superposition,[],[f25,f842])).
% 8.19/1.42  fof(f842,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f805,f48])).
% 8.19/1.42  fof(f805,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(superposition,[],[f28,f70])).
% 8.19/1.42  fof(f28,plain,(
% 8.19/1.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(cnf_transformation,[],[f7])).
% 8.19/1.42  fof(f7,axiom,(
% 8.19/1.42    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 8.19/1.42  fof(f46,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 8.19/1.42    inference(superposition,[],[f24,f21])).
% 8.19/1.42  fof(f4437,plain,(
% 8.19/1.42    ( ! [X26,X27,X25] : (k3_xboole_0(X25,k4_xboole_0(k2_xboole_0(X25,X26),X27)) = k4_xboole_0(X25,X27)) )),
% 8.19/1.42    inference(superposition,[],[f29,f893])).
% 8.19/1.42  fof(f291,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 8.19/1.42    inference(superposition,[],[f224,f46])).
% 8.19/1.42  fof(f22264,plain,(
% 8.19/1.42    ( ! [X47,X46] : (k4_xboole_0(k5_xboole_0(X46,X47),X47) = k3_xboole_0(k5_xboole_0(X46,X47),X46)) )),
% 8.19/1.42    inference(superposition,[],[f21510,f224])).
% 8.19/1.42  fof(f22719,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k4_xboole_0(k5_xboole_0(X2,X1),X1) = k5_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 8.19/1.42    inference(superposition,[],[f166,f22409])).
% 8.19/1.42  fof(f22409,plain,(
% 8.19/1.42    ( ! [X6,X7] : (k2_xboole_0(X6,k5_xboole_0(X7,X6)) = k2_xboole_0(X7,X6)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f22400,f946])).
% 8.19/1.42  fof(f946,plain,(
% 8.19/1.42    ( ! [X33,X32] : (k2_xboole_0(X32,X33) = k2_xboole_0(X32,k4_xboole_0(X33,X32))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f935,f940])).
% 8.19/1.42  fof(f935,plain,(
% 8.19/1.42    ( ! [X33,X32] : (k2_xboole_0(X32,X33) = k2_xboole_0(X32,k4_xboole_0(k2_xboole_0(X32,X33),X32))) )),
% 8.19/1.42    inference(superposition,[],[f439,f893])).
% 8.19/1.42  fof(f439,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) = X0) )),
% 8.19/1.42    inference(superposition,[],[f394,f21])).
% 8.19/1.42  fof(f394,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) = X3) )),
% 8.19/1.42    inference(forward_demodulation,[],[f384,f359])).
% 8.19/1.42  fof(f384,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k2_xboole_0(k3_xboole_0(X3,X4),k3_xboole_0(X3,k4_xboole_0(X3,X4))) = X3) )),
% 8.19/1.42    inference(superposition,[],[f379,f25])).
% 8.19/1.42  fof(f379,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) )),
% 8.19/1.42    inference(backward_demodulation,[],[f113,f378])).
% 8.19/1.42  fof(f378,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f372,f164])).
% 8.19/1.42  fof(f372,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(superposition,[],[f164,f360])).
% 8.19/1.42  fof(f113,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2))) = X1) )),
% 8.19/1.42    inference(forward_demodulation,[],[f100,f22])).
% 8.19/1.42  fof(f100,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 8.19/1.42    inference(superposition,[],[f26,f24])).
% 8.19/1.42  fof(f22400,plain,(
% 8.19/1.42    ( ! [X6,X7] : (k2_xboole_0(X6,k5_xboole_0(X7,X6)) = k2_xboole_0(X7,k4_xboole_0(X6,X7))) )),
% 8.19/1.42    inference(backward_demodulation,[],[f233,f22249])).
% 8.19/1.42  fof(f22249,plain,(
% 8.19/1.42    ( ! [X17,X18] : (k4_xboole_0(X17,X18) = k3_xboole_0(X17,k5_xboole_0(X18,X17))) )),
% 8.19/1.42    inference(superposition,[],[f21510,f209])).
% 8.19/1.42  fof(f233,plain,(
% 8.19/1.42    ( ! [X6,X7] : (k2_xboole_0(X6,k5_xboole_0(X7,X6)) = k2_xboole_0(X7,k3_xboole_0(X6,k5_xboole_0(X7,X6)))) )),
% 8.19/1.42    inference(superposition,[],[f26,f209])).
% 8.19/1.42  fof(f166,plain,(
% 8.19/1.42    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 8.19/1.42    inference(superposition,[],[f160,f23])).
% 8.19/1.42  fof(f22562,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k5_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 8.19/1.42    inference(superposition,[],[f166,f22357])).
% 8.19/1.42  fof(f22357,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k2_xboole_0(X3,k5_xboole_0(X3,X4)) = k2_xboole_0(X4,X3)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f22348,f946])).
% 8.19/1.42  fof(f22348,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k2_xboole_0(X3,k5_xboole_0(X3,X4)) = k2_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 8.19/1.42    inference(backward_demodulation,[],[f174,f22248])).
% 8.19/1.42  fof(f22248,plain,(
% 8.19/1.42    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k3_xboole_0(X15,k5_xboole_0(X15,X16))) )),
% 8.19/1.42    inference(superposition,[],[f21510,f160])).
% 8.19/1.42  fof(f174,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k2_xboole_0(X3,k5_xboole_0(X3,X4)) = k2_xboole_0(X4,k3_xboole_0(X3,k5_xboole_0(X3,X4)))) )),
% 8.19/1.42    inference(superposition,[],[f26,f160])).
% 8.19/1.42  fof(f22674,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k5_xboole_0(X57,X56),X57)))) )),
% 8.19/1.42    inference(backward_demodulation,[],[f21425,f22659])).
% 8.19/1.42  fof(f22659,plain,(
% 8.19/1.42    ( ! [X33,X32] : (k4_xboole_0(k2_xboole_0(X32,X33),X33) = k4_xboole_0(k5_xboole_0(X33,X32),X33)) )),
% 8.19/1.42    inference(backward_demodulation,[],[f3166,f22562])).
% 8.19/1.42  fof(f3166,plain,(
% 8.19/1.42    ( ! [X33,X32] : (k4_xboole_0(k2_xboole_0(X32,X33),X33) = k5_xboole_0(X33,k2_xboole_0(X32,X33))) )),
% 8.19/1.42    inference(superposition,[],[f355,f1029])).
% 8.19/1.42  fof(f1029,plain,(
% 8.19/1.42    ( ! [X10,X11] : (k3_xboole_0(k2_xboole_0(X11,X10),X10) = X10) )),
% 8.19/1.42    inference(forward_demodulation,[],[f1012,f53])).
% 8.19/1.42  fof(f1012,plain,(
% 8.19/1.42    ( ! [X10,X11] : (k3_xboole_0(k2_xboole_0(X11,X10),X10) = k5_xboole_0(X10,k1_xboole_0)) )),
% 8.19/1.42    inference(superposition,[],[f165,f815])).
% 8.19/1.42  fof(f815,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 8.19/1.42    inference(superposition,[],[f28,f534])).
% 8.19/1.42  fof(f534,plain,(
% 8.19/1.42    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 8.19/1.42    inference(forward_demodulation,[],[f510,f80])).
% 8.19/1.42  fof(f510,plain,(
% 8.19/1.42    ( ! [X6,X5] : (k5_xboole_0(X5,X5) = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 8.19/1.42    inference(superposition,[],[f166,f395])).
% 8.19/1.42  fof(f395,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1) )),
% 8.19/1.42    inference(backward_demodulation,[],[f366,f394])).
% 8.19/1.42  fof(f366,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f350,f359])).
% 8.19/1.42  fof(f350,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 8.19/1.42    inference(superposition,[],[f26,f164])).
% 8.19/1.42  fof(f165,plain,(
% 8.19/1.42    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 8.19/1.42    inference(superposition,[],[f160,f46])).
% 8.19/1.42  fof(f21425,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k5_xboole_0(X56,X57) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X56,X57),X57)))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f21424,f920])).
% 8.19/1.42  fof(f920,plain,(
% 8.19/1.42    ( ! [X23,X22] : (k5_xboole_0(X22,X23) = k3_xboole_0(k5_xboole_0(X22,X23),k2_xboole_0(X22,X23))) )),
% 8.19/1.42    inference(superposition,[],[f893,f26])).
% 8.19/1.42  fof(f21424,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k3_xboole_0(k5_xboole_0(X56,X57),k2_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X56,X57),X57)))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f21423,f21])).
% 8.19/1.42  fof(f21423,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k3_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k4_xboole_0(k2_xboole_0(X56,X57),X57)))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f21422,f3166])).
% 8.19/1.42  fof(f21422,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k3_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,k5_xboole_0(X57,k2_xboole_0(X56,X57))))) )),
% 8.19/1.42    inference(forward_demodulation,[],[f21253,f27])).
% 8.19/1.42  fof(f21253,plain,(
% 8.19/1.42    ( ! [X57,X56] : (k3_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(X56,X57)) = k4_xboole_0(k2_xboole_0(X56,X57),k5_xboole_0(k5_xboole_0(X56,X57),k2_xboole_0(X56,X57)))) )),
% 8.19/1.42    inference(superposition,[],[f3144,f1302])).
% 8.19/1.42  fof(f1302,plain,(
% 8.19/1.42    ( ! [X24,X25] : (k2_xboole_0(X24,X25) = k2_xboole_0(k5_xboole_0(X24,X25),k2_xboole_0(X24,X25))) )),
% 8.19/1.42    inference(superposition,[],[f930,f26])).
% 8.19/1.42  fof(f930,plain,(
% 8.19/1.42    ( ! [X21,X20] : (k2_xboole_0(X20,X21) = k2_xboole_0(X20,k2_xboole_0(X20,X21))) )),
% 8.19/1.42    inference(superposition,[],[f275,f893])).
% 8.19/1.42  fof(f275,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),X0) = X0) )),
% 8.19/1.42    inference(superposition,[],[f270,f21])).
% 8.19/1.42  fof(f270,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = X1) )),
% 8.19/1.42    inference(superposition,[],[f264,f25])).
% 8.19/1.42  fof(f264,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 8.19/1.42    inference(backward_demodulation,[],[f58,f247])).
% 8.19/1.42  fof(f247,plain,(
% 8.19/1.42    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) )),
% 8.19/1.42    inference(superposition,[],[f223,f24])).
% 8.19/1.42  fof(f223,plain,(
% 8.19/1.42    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7) )),
% 8.19/1.42    inference(superposition,[],[f209,f160])).
% 8.19/1.42  fof(f58,plain,(
% 8.19/1.42    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 8.19/1.42    inference(superposition,[],[f23,f25])).
% 8.19/1.42  fof(f18,plain,(
% 8.19/1.42    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.19/1.42    inference(cnf_transformation,[],[f17])).
% 8.19/1.42  fof(f17,plain,(
% 8.19/1.42    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.19/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 8.19/1.42  fof(f16,plain,(
% 8.19/1.42    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 8.19/1.42    introduced(choice_axiom,[])).
% 8.19/1.42  fof(f15,plain,(
% 8.19/1.42    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.19/1.42    inference(ennf_transformation,[],[f14])).
% 8.19/1.42  fof(f14,negated_conjecture,(
% 8.19/1.42    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.19/1.42    inference(negated_conjecture,[],[f13])).
% 8.19/1.42  fof(f13,conjecture,(
% 8.19/1.42    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 8.19/1.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 8.19/1.42  % SZS output end Proof for theBenchmark
% 8.19/1.42  % (26890)------------------------------
% 8.19/1.42  % (26890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.19/1.42  % (26890)Termination reason: Refutation
% 8.19/1.42  
% 8.19/1.42  % (26890)Memory used [KB]: 21108
% 8.19/1.42  % (26890)Time elapsed: 1.007 s
% 8.19/1.42  % (26890)------------------------------
% 8.19/1.42  % (26890)------------------------------
% 8.19/1.43  % (26873)Success in time 1.069 s
%------------------------------------------------------------------------------
