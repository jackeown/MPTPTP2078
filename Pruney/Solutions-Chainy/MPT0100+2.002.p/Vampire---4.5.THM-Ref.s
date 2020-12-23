%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:49 EST 2020

% Result     : Theorem 7.13s
% Output     : Refutation 7.13s
% Verified   : 
% Statistics : Number of formulae       :  117 (2187 expanded)
%              Number of leaves         :   11 ( 740 expanded)
%              Depth                    :   28
%              Number of atoms          :  118 (2188 expanded)
%              Number of equality atoms :  117 (2187 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25939,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25938,f13292])).

fof(f13292,plain,(
    ! [X171,X172] : k2_xboole_0(X172,X171) = k2_xboole_0(k4_xboole_0(X172,X171),X171) ),
    inference(forward_demodulation,[],[f13013,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f13013,plain,(
    ! [X171,X172] : k2_xboole_0(k4_xboole_0(X172,X171),X171) = k4_xboole_0(k2_xboole_0(X172,X171),k1_xboole_0) ),
    inference(superposition,[],[f7536,f12671])).

fof(f12671,plain,(
    ! [X26,X27] : k2_xboole_0(X27,X26) = k2_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(forward_demodulation,[],[f12670,f21])).

fof(f12670,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),k1_xboole_0) ),
    inference(forward_demodulation,[],[f12669,f66])).

fof(f66,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f28,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f31,f21])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f12669,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X27,k2_xboole_0(X26,k4_xboole_0(X27,X26)))) ),
    inference(forward_demodulation,[],[f12668,f70])).

fof(f70,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f61,f28])).

fof(f61,plain,(
    ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6) ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f12668,plain,(
    ! [X26,X27] : k2_xboole_0(X26,k4_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(k2_xboole_0(X27,X26),k2_xboole_0(X26,k4_xboole_0(X27,X26)))) ),
    inference(forward_demodulation,[],[f12385,f21])).

fof(f12385,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(k2_xboole_0(X27,X26),k2_xboole_0(X26,k4_xboole_0(X27,X26)))) = k4_xboole_0(k2_xboole_0(X26,k4_xboole_0(X27,X26)),k1_xboole_0) ),
    inference(superposition,[],[f32,f12162])).

fof(f12162,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(X122,X123)) ),
    inference(forward_demodulation,[],[f12161,f21])).

fof(f12161,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f12160,f41])).

fof(f41,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f39,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f39,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f37,f21])).

fof(f37,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f26,f21])).

fof(f12160,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f12159,f24])).

fof(f12159,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f12158,f118])).

fof(f118,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f83,f24])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(forward_demodulation,[],[f81,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f81,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f28,f69])).

fof(f69,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f60,f20])).

fof(f60,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f28,f34])).

fof(f12158,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k4_xboole_0(X122,k2_xboole_0(X123,k2_xboole_0(X122,X123))))) ),
    inference(forward_demodulation,[],[f12157,f28])).

fof(f12157,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k4_xboole_0(k4_xboole_0(X122,X123),k2_xboole_0(X122,X123)))) ),
    inference(forward_demodulation,[],[f12156,f1173])).

fof(f1173,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X4,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X4),k2_xboole_0(X3,X2)) ),
    inference(superposition,[],[f71,f24])).

fof(f71,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(X8,k2_xboole_0(X7,X9)) ),
    inference(forward_demodulation,[],[f62,f28])).

fof(f62,plain,(
    ! [X8,X7,X9] : k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k4_xboole_0(X8,X7),X9) ),
    inference(superposition,[],[f28,f35])).

fof(f35,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f26,f24])).

fof(f12156,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(X122,X123)))) ),
    inference(forward_demodulation,[],[f11728,f24])).

fof(f11728,plain,(
    ! [X123,X122] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(X122,X123)),k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0))) ),
    inference(superposition,[],[f190,f98])).

fof(f98,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f66,f26])).

fof(f190,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f66,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f7536,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k4_xboole_0(k2_xboole_0(X22,X21),k1_xboole_0) ),
    inference(forward_demodulation,[],[f7535,f76])).

fof(f76,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f69,f24])).

fof(f7535,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X22,k2_xboole_0(X21,X22))) ),
    inference(forward_demodulation,[],[f7534,f70])).

fof(f7534,plain,(
    ! [X21,X22] : k2_xboole_0(X21,X22) = k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X21,X22))) ),
    inference(forward_demodulation,[],[f7466,f21])).

fof(f7466,plain,(
    ! [X21,X22] : k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X21,X22))) = k4_xboole_0(k2_xboole_0(X21,X22),k1_xboole_0) ),
    inference(superposition,[],[f32,f7248])).

fof(f7248,plain,(
    ! [X12,X13] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,X12)) ),
    inference(superposition,[],[f4387,f202])).

fof(f202,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26)) = X26 ),
    inference(forward_demodulation,[],[f201,f21])).

fof(f201,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26)) = k4_xboole_0(X26,k1_xboole_0) ),
    inference(forward_demodulation,[],[f178,f69])).

fof(f178,plain,(
    ! [X26,X27] : k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X26,X27))) = k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26)) ),
    inference(superposition,[],[f32,f35])).

fof(f4387,plain,(
    ! [X30,X28,X29] : k1_xboole_0 = k4_xboole_0(X30,k2_xboole_0(X28,k4_xboole_0(X30,k4_xboole_0(X28,X29)))) ),
    inference(superposition,[],[f2872,f1834])).

fof(f1834,plain,(
    ! [X76,X77] : k2_xboole_0(k4_xboole_0(X76,X77),X76) = X76 ),
    inference(superposition,[],[f580,f1731])).

fof(f1731,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f1730,f21])).

fof(f1730,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f1729,f69])).

fof(f1729,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,k4_xboole_0(X5,X6)))) ),
    inference(forward_demodulation,[],[f1670,f21])).

fof(f1670,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,k4_xboole_0(X5,X6)))) = k4_xboole_0(k2_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0) ),
    inference(superposition,[],[f32,f1443])).

fof(f1443,plain,(
    ! [X17,X18] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X17,k4_xboole_0(X17,X18)),X17) ),
    inference(forward_demodulation,[],[f1442,f24])).

fof(f1442,plain,(
    ! [X17,X18] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X17,X18),X17),X17) ),
    inference(forward_demodulation,[],[f1430,f39])).

fof(f1430,plain,(
    ! [X17,X18] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X17,X18),X17),k2_xboole_0(X17,k1_xboole_0)) ),
    inference(superposition,[],[f98,f1329])).

fof(f1329,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f1275,f39])).

fof(f1275,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f100,f76])).

fof(f100,plain,(
    ! [X14,X12,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X14,k4_xboole_0(X12,k2_xboole_0(X13,X14)))) ),
    inference(superposition,[],[f66,f28])).

fof(f580,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f536,f24])).

fof(f536,plain,(
    ! [X4,X3] : k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f226,f21])).

fof(f226,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X2)),k1_xboole_0) ),
    inference(superposition,[],[f200,f69])).

fof(f200,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25 ),
    inference(forward_demodulation,[],[f199,f21])).

fof(f199,plain,(
    ! [X24,X25] : k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0) ),
    inference(forward_demodulation,[],[f177,f76])).

fof(f177,plain,(
    ! [X24,X25] : k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) ),
    inference(superposition,[],[f32,f26])).

fof(f2872,plain,(
    ! [X4,X5,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X3,X4))) ),
    inference(superposition,[],[f1417,f28])).

fof(f1417,plain,(
    ! [X88,X87,X86] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X86,k2_xboole_0(X87,X88)),k4_xboole_0(X86,X87)) ),
    inference(superposition,[],[f1329,f28])).

fof(f25938,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f25701,f13068])).

fof(f13068,plain,(
    ! [X76,X75] : k2_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X76,k4_xboole_0(X76,X75))) = X75 ),
    inference(forward_demodulation,[],[f12910,f1731])).

fof(f12910,plain,(
    ! [X76,X75] : k2_xboole_0(X75,k4_xboole_0(X75,X76)) = k2_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X76,k4_xboole_0(X76,X75))) ),
    inference(superposition,[],[f12671,f32])).

fof(f25701,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f30,f16218])).

fof(f16218,plain,(
    ! [X92,X90,X91] : k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(X91,k2_xboole_0(X90,X92)) ),
    inference(forward_demodulation,[],[f16217,f13905])).

fof(f13905,plain,(
    ! [X83,X81,X82] : k2_xboole_0(k4_xboole_0(X82,k2_xboole_0(X81,X83)),k2_xboole_0(X81,X83)) = k2_xboole_0(X83,k2_xboole_0(X81,X82)) ),
    inference(forward_demodulation,[],[f13757,f13092])).

fof(f13092,plain,(
    ! [X101,X99,X100] : k2_xboole_0(k2_xboole_0(X99,X100),k2_xboole_0(X99,X101)) = k2_xboole_0(X100,k2_xboole_0(X99,X101)) ),
    inference(forward_demodulation,[],[f12921,f12671])).

fof(f12921,plain,(
    ! [X101,X99,X100] : k2_xboole_0(k2_xboole_0(X99,X100),k2_xboole_0(X99,X101)) = k2_xboole_0(k2_xboole_0(X99,X101),k4_xboole_0(X100,k2_xboole_0(X99,X101))) ),
    inference(superposition,[],[f12671,f71])).

fof(f13757,plain,(
    ! [X83,X81,X82] : k2_xboole_0(k4_xboole_0(X82,k2_xboole_0(X81,X83)),k2_xboole_0(X81,X83)) = k2_xboole_0(k2_xboole_0(X81,X83),k2_xboole_0(X81,X82)) ),
    inference(superposition,[],[f13104,f71])).

fof(f13104,plain,(
    ! [X111,X110] : k2_xboole_0(X110,X111) = k2_xboole_0(k4_xboole_0(X111,X110),X110) ),
    inference(forward_demodulation,[],[f12925,f2153])).

fof(f2153,plain,(
    ! [X94,X92,X93] : k2_xboole_0(X94,X92) = k2_xboole_0(k2_xboole_0(X94,X92),k4_xboole_0(X92,X93)) ),
    inference(forward_demodulation,[],[f2072,f21])).

fof(f2072,plain,(
    ! [X94,X92,X93] : k2_xboole_0(X94,X92) = k2_xboole_0(k2_xboole_0(X94,X92),k4_xboole_0(k4_xboole_0(X92,X93),k1_xboole_0)) ),
    inference(superposition,[],[f1789,f1333])).

fof(f1333,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X9)) ),
    inference(forward_demodulation,[],[f1332,f41])).

fof(f1332,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k1_xboole_0,k2_xboole_0(X11,X9))) ),
    inference(forward_demodulation,[],[f1278,f24])).

fof(f1278,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k2_xboole_0(X11,X9),k1_xboole_0)) ),
    inference(superposition,[],[f100,f134])).

fof(f134,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f92,f24])).

fof(f92,plain,(
    ! [X2,X3,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(forward_demodulation,[],[f90,f20])).

fof(f90,plain,(
    ! [X2,X3,X1] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3)) ),
    inference(superposition,[],[f28,f76])).

fof(f1789,plain,(
    ! [X64,X63] : k2_xboole_0(X63,k4_xboole_0(X64,k4_xboole_0(X64,X63))) = X63 ),
    inference(superposition,[],[f1731,f32])).

fof(f12925,plain,(
    ! [X111,X110] : k2_xboole_0(k4_xboole_0(X111,X110),X110) = k2_xboole_0(k2_xboole_0(X110,X111),k4_xboole_0(X111,X110)) ),
    inference(superposition,[],[f12671,f202])).

fof(f16217,plain,(
    ! [X92,X90,X91] : k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(k4_xboole_0(X92,k2_xboole_0(X90,X91)),k2_xboole_0(X90,X91)) ),
    inference(forward_demodulation,[],[f16216,f7635])).

fof(f7635,plain,(
    ! [X105,X106,X104] : k4_xboole_0(X106,k2_xboole_0(X104,X105)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X105,X104),X106),k2_xboole_0(X104,X105)) ),
    inference(superposition,[],[f1915,f7536])).

fof(f1915,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X21,X22),X23),X21) = k4_xboole_0(X23,X21) ),
    inference(superposition,[],[f71,f1834])).

fof(f16216,plain,(
    ! [X92,X90,X91] : k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X91,X90),X92),k2_xboole_0(X90,X91)),k2_xboole_0(X90,X91)) ),
    inference(forward_demodulation,[],[f15909,f21])).

fof(f15909,plain,(
    ! [X92,X90,X91] : k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X91,X90),X92),k2_xboole_0(X90,X91)),k4_xboole_0(k2_xboole_0(X90,X91),k1_xboole_0)) ),
    inference(superposition,[],[f13068,f7533])).

fof(f7533,plain,(
    ! [X19,X20,X18] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(k2_xboole_0(X19,X18),X20)) ),
    inference(forward_demodulation,[],[f7465,f20])).

fof(f7465,plain,(
    ! [X19,X20,X18] : k4_xboole_0(k1_xboole_0,X20) = k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(k2_xboole_0(X19,X18),X20)) ),
    inference(superposition,[],[f28,f7248])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f18,f27,f25])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (1723)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (1711)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (1715)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (1724)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (1719)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (1714)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (1712)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (1717)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (1726)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (1713)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (1722)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (1721)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (1710)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (1720)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (1721)Refutation not found, incomplete strategy% (1721)------------------------------
% 0.21/0.51  % (1721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1721)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1721)Memory used [KB]: 10618
% 0.21/0.51  % (1721)Time elapsed: 0.081 s
% 0.21/0.51  % (1721)------------------------------
% 0.21/0.51  % (1721)------------------------------
% 0.21/0.51  % (1728)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.51  % (1716)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (1725)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (1718)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 5.05/1.02  % (1714)Time limit reached!
% 5.05/1.02  % (1714)------------------------------
% 5.05/1.02  % (1714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.05/1.04  % (1714)Termination reason: Time limit
% 5.05/1.04  
% 5.05/1.04  % (1714)Memory used [KB]: 21620
% 5.05/1.04  % (1714)Time elapsed: 0.602 s
% 5.05/1.04  % (1714)------------------------------
% 5.05/1.04  % (1714)------------------------------
% 7.13/1.29  % (1724)Refutation found. Thanks to Tanya!
% 7.13/1.29  % SZS status Theorem for theBenchmark
% 7.13/1.29  % SZS output start Proof for theBenchmark
% 7.13/1.29  fof(f25939,plain,(
% 7.13/1.29    $false),
% 7.13/1.29    inference(subsumption_resolution,[],[f25938,f13292])).
% 7.13/1.29  fof(f13292,plain,(
% 7.13/1.29    ( ! [X171,X172] : (k2_xboole_0(X172,X171) = k2_xboole_0(k4_xboole_0(X172,X171),X171)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f13013,f21])).
% 7.13/1.29  fof(f21,plain,(
% 7.13/1.29    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.13/1.29    inference(cnf_transformation,[],[f7])).
% 7.13/1.29  fof(f7,axiom,(
% 7.13/1.29    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 7.13/1.29  fof(f13013,plain,(
% 7.13/1.29    ( ! [X171,X172] : (k2_xboole_0(k4_xboole_0(X172,X171),X171) = k4_xboole_0(k2_xboole_0(X172,X171),k1_xboole_0)) )),
% 7.13/1.29    inference(superposition,[],[f7536,f12671])).
% 7.13/1.29  fof(f12671,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k2_xboole_0(X27,X26) = k2_xboole_0(X26,k4_xboole_0(X27,X26))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12670,f21])).
% 7.13/1.29  fof(f12670,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),k1_xboole_0)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12669,f66])).
% 7.13/1.29  fof(f66,plain,(
% 7.13/1.29    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 7.13/1.29    inference(superposition,[],[f28,f34])).
% 7.13/1.29  fof(f34,plain,(
% 7.13/1.29    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 7.13/1.29    inference(backward_demodulation,[],[f31,f21])).
% 7.13/1.29  fof(f31,plain,(
% 7.13/1.29    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.13/1.29    inference(definition_unfolding,[],[f19,f25])).
% 7.13/1.29  fof(f25,plain,(
% 7.13/1.29    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.13/1.29    inference(cnf_transformation,[],[f10])).
% 7.13/1.29  fof(f10,axiom,(
% 7.13/1.29    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 7.13/1.29  fof(f19,plain,(
% 7.13/1.29    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 7.13/1.29    inference(cnf_transformation,[],[f6])).
% 7.13/1.29  fof(f6,axiom,(
% 7.13/1.29    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 7.13/1.29  fof(f28,plain,(
% 7.13/1.29    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.13/1.29    inference(cnf_transformation,[],[f9])).
% 7.13/1.29  fof(f9,axiom,(
% 7.13/1.29    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.13/1.29  fof(f12669,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X27,k2_xboole_0(X26,k4_xboole_0(X27,X26))))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12668,f70])).
% 7.13/1.29  fof(f70,plain,(
% 7.13/1.29    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X4,k2_xboole_0(X5,X6))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f61,f28])).
% 7.13/1.29  fof(f61,plain,(
% 7.13/1.29    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(k4_xboole_0(X4,X5),X6)) )),
% 7.13/1.29    inference(superposition,[],[f28,f26])).
% 7.13/1.29  fof(f26,plain,(
% 7.13/1.29    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.13/1.29    inference(cnf_transformation,[],[f8])).
% 7.13/1.29  fof(f8,axiom,(
% 7.13/1.29    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 7.13/1.29  fof(f12668,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k2_xboole_0(X26,k4_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(k2_xboole_0(X27,X26),k2_xboole_0(X26,k4_xboole_0(X27,X26))))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12385,f21])).
% 7.13/1.29  fof(f12385,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(k2_xboole_0(X27,X26),k2_xboole_0(X26,k4_xboole_0(X27,X26)))) = k4_xboole_0(k2_xboole_0(X26,k4_xboole_0(X27,X26)),k1_xboole_0)) )),
% 7.13/1.29    inference(superposition,[],[f32,f12162])).
% 7.13/1.29  fof(f12162,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(X122,X123))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12161,f21])).
% 7.13/1.29  fof(f12161,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12160,f41])).
% 7.13/1.29  fof(f41,plain,(
% 7.13/1.29    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 7.13/1.29    inference(superposition,[],[f39,f24])).
% 7.13/1.29  fof(f24,plain,(
% 7.13/1.29    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.13/1.29    inference(cnf_transformation,[],[f1])).
% 7.13/1.29  fof(f1,axiom,(
% 7.13/1.29    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 7.13/1.29  fof(f39,plain,(
% 7.13/1.29    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 7.13/1.29    inference(forward_demodulation,[],[f37,f21])).
% 7.13/1.29  fof(f37,plain,(
% 7.13/1.29    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 7.13/1.29    inference(superposition,[],[f26,f21])).
% 7.13/1.29  fof(f12160,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0)))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12159,f24])).
% 7.13/1.29  fof(f12159,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k1_xboole_0))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12158,f118])).
% 7.13/1.29  fof(f118,plain,(
% 7.13/1.29    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 7.13/1.29    inference(superposition,[],[f83,f24])).
% 7.13/1.29  fof(f83,plain,(
% 7.13/1.29    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f81,f20])).
% 7.13/1.29  fof(f20,plain,(
% 7.13/1.29    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 7.13/1.29    inference(cnf_transformation,[],[f11])).
% 7.13/1.29  fof(f11,axiom,(
% 7.13/1.29    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 7.13/1.29  fof(f81,plain,(
% 7.13/1.29    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k4_xboole_0(k1_xboole_0,X2)) )),
% 7.13/1.29    inference(superposition,[],[f28,f69])).
% 7.13/1.29  fof(f69,plain,(
% 7.13/1.29    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f60,f20])).
% 7.13/1.29  fof(f60,plain,(
% 7.13/1.29    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 7.13/1.29    inference(superposition,[],[f28,f34])).
% 7.13/1.29  fof(f12158,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k4_xboole_0(X122,k2_xboole_0(X123,k2_xboole_0(X122,X123)))))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12157,f28])).
% 7.13/1.29  fof(f12157,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k4_xboole_0(k4_xboole_0(X122,X123),k2_xboole_0(X122,X123))))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12156,f1173])).
% 7.13/1.29  fof(f1173,plain,(
% 7.13/1.29    ( ! [X4,X2,X3] : (k4_xboole_0(X4,k2_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X4),k2_xboole_0(X3,X2))) )),
% 7.13/1.29    inference(superposition,[],[f71,f24])).
% 7.13/1.29  fof(f71,plain,(
% 7.13/1.29    ( ! [X8,X7,X9] : (k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(X8,k2_xboole_0(X7,X9))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f62,f28])).
% 7.13/1.29  fof(f62,plain,(
% 7.13/1.29    ( ! [X8,X7,X9] : (k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,X9)) = k4_xboole_0(k4_xboole_0(X8,X7),X9)) )),
% 7.13/1.29    inference(superposition,[],[f28,f35])).
% 7.13/1.29  fof(f35,plain,(
% 7.13/1.29    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 7.13/1.29    inference(superposition,[],[f26,f24])).
% 7.13/1.29  fof(f12156,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0),k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(X122,X123))))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f11728,f24])).
% 7.13/1.29  fof(f11728,plain,(
% 7.13/1.29    ( ! [X123,X122] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(k4_xboole_0(k2_xboole_0(X123,k4_xboole_0(X122,X123)),k2_xboole_0(X122,X123)),k4_xboole_0(k2_xboole_0(X122,X123),k1_xboole_0)))) )),
% 7.13/1.29    inference(superposition,[],[f190,f98])).
% 7.13/1.29  fof(f98,plain,(
% 7.13/1.29    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 7.13/1.29    inference(superposition,[],[f66,f26])).
% 7.13/1.29  fof(f190,plain,(
% 7.13/1.29    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 7.13/1.29    inference(superposition,[],[f66,f32])).
% 7.13/1.29  fof(f32,plain,(
% 7.13/1.29    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.13/1.29    inference(definition_unfolding,[],[f23,f25,f25])).
% 7.13/1.29  fof(f23,plain,(
% 7.13/1.29    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.13/1.29    inference(cnf_transformation,[],[f2])).
% 7.13/1.29  fof(f2,axiom,(
% 7.13/1.29    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.13/1.29  fof(f7536,plain,(
% 7.13/1.29    ( ! [X21,X22] : (k2_xboole_0(X21,X22) = k4_xboole_0(k2_xboole_0(X22,X21),k1_xboole_0)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f7535,f76])).
% 7.13/1.29  fof(f76,plain,(
% 7.13/1.29    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 7.13/1.29    inference(superposition,[],[f69,f24])).
% 7.13/1.29  fof(f7535,plain,(
% 7.13/1.29    ( ! [X21,X22] : (k2_xboole_0(X21,X22) = k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(X22,k2_xboole_0(X21,X22)))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f7534,f70])).
% 7.13/1.29  fof(f7534,plain,(
% 7.13/1.29    ( ! [X21,X22] : (k2_xboole_0(X21,X22) = k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X21,X22)))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f7466,f21])).
% 7.13/1.29  fof(f7466,plain,(
% 7.13/1.29    ( ! [X21,X22] : (k4_xboole_0(k2_xboole_0(X22,X21),k4_xboole_0(k2_xboole_0(X22,X21),k2_xboole_0(X21,X22))) = k4_xboole_0(k2_xboole_0(X21,X22),k1_xboole_0)) )),
% 7.13/1.29    inference(superposition,[],[f32,f7248])).
% 7.13/1.29  fof(f7248,plain,(
% 7.13/1.29    ( ! [X12,X13] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X12,X13),k2_xboole_0(X13,X12))) )),
% 7.13/1.29    inference(superposition,[],[f4387,f202])).
% 7.13/1.29  fof(f202,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26)) = X26) )),
% 7.13/1.29    inference(forward_demodulation,[],[f201,f21])).
% 7.13/1.29  fof(f201,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26)) = k4_xboole_0(X26,k1_xboole_0)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f178,f69])).
% 7.13/1.29  fof(f178,plain,(
% 7.13/1.29    ( ! [X26,X27] : (k4_xboole_0(X26,k4_xboole_0(X26,k2_xboole_0(X26,X27))) = k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26))) )),
% 7.13/1.29    inference(superposition,[],[f32,f35])).
% 7.13/1.29  fof(f4387,plain,(
% 7.13/1.29    ( ! [X30,X28,X29] : (k1_xboole_0 = k4_xboole_0(X30,k2_xboole_0(X28,k4_xboole_0(X30,k4_xboole_0(X28,X29))))) )),
% 7.13/1.29    inference(superposition,[],[f2872,f1834])).
% 7.13/1.29  fof(f1834,plain,(
% 7.13/1.29    ( ! [X76,X77] : (k2_xboole_0(k4_xboole_0(X76,X77),X76) = X76) )),
% 7.13/1.29    inference(superposition,[],[f580,f1731])).
% 7.13/1.29  fof(f1731,plain,(
% 7.13/1.29    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1730,f21])).
% 7.13/1.29  fof(f1730,plain,(
% 7.13/1.29    ( ! [X6,X5] : (k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1729,f69])).
% 7.13/1.29  fof(f1729,plain,(
% 7.13/1.29    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,k4_xboole_0(X5,X6))))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1670,f21])).
% 7.13/1.29  fof(f1670,plain,(
% 7.13/1.29    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,k4_xboole_0(X5,X6)))) = k4_xboole_0(k2_xboole_0(X5,k4_xboole_0(X5,X6)),k1_xboole_0)) )),
% 7.13/1.29    inference(superposition,[],[f32,f1443])).
% 7.13/1.29  fof(f1443,plain,(
% 7.13/1.29    ( ! [X17,X18] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X17,k4_xboole_0(X17,X18)),X17)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1442,f24])).
% 7.13/1.29  fof(f1442,plain,(
% 7.13/1.29    ( ! [X17,X18] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X17,X18),X17),X17)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1430,f39])).
% 7.13/1.29  fof(f1430,plain,(
% 7.13/1.29    ( ! [X17,X18] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X17,X18),X17),k2_xboole_0(X17,k1_xboole_0))) )),
% 7.13/1.29    inference(superposition,[],[f98,f1329])).
% 7.13/1.29  fof(f1329,plain,(
% 7.13/1.29    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1275,f39])).
% 7.13/1.29  fof(f1275,plain,(
% 7.13/1.29    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,k1_xboole_0))) )),
% 7.13/1.29    inference(superposition,[],[f100,f76])).
% 7.13/1.29  fof(f100,plain,(
% 7.13/1.29    ( ! [X14,X12,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X12,X13),k2_xboole_0(X14,k4_xboole_0(X12,k2_xboole_0(X13,X14))))) )),
% 7.13/1.29    inference(superposition,[],[f66,f28])).
% 7.13/1.29  fof(f580,plain,(
% 7.13/1.29    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 7.13/1.29    inference(superposition,[],[f536,f24])).
% 7.13/1.29  fof(f536,plain,(
% 7.13/1.29    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k2_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 7.13/1.29    inference(superposition,[],[f226,f21])).
% 7.13/1.29  fof(f226,plain,(
% 7.13/1.29    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X1,k2_xboole_0(X1,X2)),k1_xboole_0)) )),
% 7.13/1.29    inference(superposition,[],[f200,f69])).
% 7.13/1.29  fof(f200,plain,(
% 7.13/1.29    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = X25) )),
% 7.13/1.29    inference(forward_demodulation,[],[f199,f21])).
% 7.13/1.29  fof(f199,plain,(
% 7.13/1.29    ( ! [X24,X25] : (k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25)) = k4_xboole_0(X25,k1_xboole_0)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f177,f76])).
% 7.13/1.29  fof(f177,plain,(
% 7.13/1.29    ( ! [X24,X25] : (k4_xboole_0(X25,k4_xboole_0(X25,k2_xboole_0(X24,X25))) = k4_xboole_0(k2_xboole_0(X24,X25),k4_xboole_0(X24,X25))) )),
% 7.13/1.29    inference(superposition,[],[f32,f26])).
% 7.13/1.29  fof(f2872,plain,(
% 7.13/1.29    ( ! [X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X3,X4)))) )),
% 7.13/1.29    inference(superposition,[],[f1417,f28])).
% 7.13/1.29  fof(f1417,plain,(
% 7.13/1.29    ( ! [X88,X87,X86] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X86,k2_xboole_0(X87,X88)),k4_xboole_0(X86,X87))) )),
% 7.13/1.29    inference(superposition,[],[f1329,f28])).
% 7.13/1.29  fof(f25938,plain,(
% 7.13/1.29    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 7.13/1.29    inference(forward_demodulation,[],[f25701,f13068])).
% 7.13/1.29  fof(f13068,plain,(
% 7.13/1.29    ( ! [X76,X75] : (k2_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X76,k4_xboole_0(X76,X75))) = X75) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12910,f1731])).
% 7.13/1.29  fof(f12910,plain,(
% 7.13/1.29    ( ! [X76,X75] : (k2_xboole_0(X75,k4_xboole_0(X75,X76)) = k2_xboole_0(k4_xboole_0(X75,X76),k4_xboole_0(X76,k4_xboole_0(X76,X75)))) )),
% 7.13/1.29    inference(superposition,[],[f12671,f32])).
% 7.13/1.29  fof(f25701,plain,(
% 7.13/1.29    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 7.13/1.29    inference(superposition,[],[f30,f16218])).
% 7.13/1.29  fof(f16218,plain,(
% 7.13/1.29    ( ! [X92,X90,X91] : (k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(X91,k2_xboole_0(X90,X92))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f16217,f13905])).
% 7.13/1.29  fof(f13905,plain,(
% 7.13/1.29    ( ! [X83,X81,X82] : (k2_xboole_0(k4_xboole_0(X82,k2_xboole_0(X81,X83)),k2_xboole_0(X81,X83)) = k2_xboole_0(X83,k2_xboole_0(X81,X82))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f13757,f13092])).
% 7.13/1.29  fof(f13092,plain,(
% 7.13/1.29    ( ! [X101,X99,X100] : (k2_xboole_0(k2_xboole_0(X99,X100),k2_xboole_0(X99,X101)) = k2_xboole_0(X100,k2_xboole_0(X99,X101))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12921,f12671])).
% 7.13/1.29  fof(f12921,plain,(
% 7.13/1.29    ( ! [X101,X99,X100] : (k2_xboole_0(k2_xboole_0(X99,X100),k2_xboole_0(X99,X101)) = k2_xboole_0(k2_xboole_0(X99,X101),k4_xboole_0(X100,k2_xboole_0(X99,X101)))) )),
% 7.13/1.29    inference(superposition,[],[f12671,f71])).
% 7.13/1.29  fof(f13757,plain,(
% 7.13/1.29    ( ! [X83,X81,X82] : (k2_xboole_0(k4_xboole_0(X82,k2_xboole_0(X81,X83)),k2_xboole_0(X81,X83)) = k2_xboole_0(k2_xboole_0(X81,X83),k2_xboole_0(X81,X82))) )),
% 7.13/1.29    inference(superposition,[],[f13104,f71])).
% 7.13/1.29  fof(f13104,plain,(
% 7.13/1.29    ( ! [X111,X110] : (k2_xboole_0(X110,X111) = k2_xboole_0(k4_xboole_0(X111,X110),X110)) )),
% 7.13/1.29    inference(forward_demodulation,[],[f12925,f2153])).
% 7.13/1.29  fof(f2153,plain,(
% 7.13/1.29    ( ! [X94,X92,X93] : (k2_xboole_0(X94,X92) = k2_xboole_0(k2_xboole_0(X94,X92),k4_xboole_0(X92,X93))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f2072,f21])).
% 7.13/1.29  fof(f2072,plain,(
% 7.13/1.29    ( ! [X94,X92,X93] : (k2_xboole_0(X94,X92) = k2_xboole_0(k2_xboole_0(X94,X92),k4_xboole_0(k4_xboole_0(X92,X93),k1_xboole_0))) )),
% 7.13/1.29    inference(superposition,[],[f1789,f1333])).
% 7.13/1.29  fof(f1333,plain,(
% 7.13/1.29    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X9))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1332,f41])).
% 7.13/1.29  fof(f1332,plain,(
% 7.13/1.29    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k1_xboole_0,k2_xboole_0(X11,X9)))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f1278,f24])).
% 7.13/1.29  fof(f1278,plain,(
% 7.13/1.29    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(k2_xboole_0(X11,X9),k1_xboole_0))) )),
% 7.13/1.29    inference(superposition,[],[f100,f134])).
% 7.13/1.29  fof(f134,plain,(
% 7.13/1.29    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X3,k2_xboole_0(X4,k2_xboole_0(X2,X3)))) )),
% 7.13/1.29    inference(superposition,[],[f92,f24])).
% 7.13/1.29  fof(f92,plain,(
% 7.13/1.29    ( ! [X2,X3,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f90,f20])).
% 7.13/1.29  fof(f90,plain,(
% 7.13/1.29    ( ! [X2,X3,X1] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X1,k2_xboole_0(k2_xboole_0(X2,X1),X3))) )),
% 7.13/1.29    inference(superposition,[],[f28,f76])).
% 7.13/1.29  fof(f1789,plain,(
% 7.13/1.29    ( ! [X64,X63] : (k2_xboole_0(X63,k4_xboole_0(X64,k4_xboole_0(X64,X63))) = X63) )),
% 7.13/1.29    inference(superposition,[],[f1731,f32])).
% 7.13/1.29  fof(f12925,plain,(
% 7.13/1.29    ( ! [X111,X110] : (k2_xboole_0(k4_xboole_0(X111,X110),X110) = k2_xboole_0(k2_xboole_0(X110,X111),k4_xboole_0(X111,X110))) )),
% 7.13/1.29    inference(superposition,[],[f12671,f202])).
% 7.13/1.29  fof(f16217,plain,(
% 7.13/1.29    ( ! [X92,X90,X91] : (k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(k4_xboole_0(X92,k2_xboole_0(X90,X91)),k2_xboole_0(X90,X91))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f16216,f7635])).
% 7.13/1.29  fof(f7635,plain,(
% 7.13/1.29    ( ! [X105,X106,X104] : (k4_xboole_0(X106,k2_xboole_0(X104,X105)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X105,X104),X106),k2_xboole_0(X104,X105))) )),
% 7.13/1.29    inference(superposition,[],[f1915,f7536])).
% 7.13/1.29  fof(f1915,plain,(
% 7.13/1.29    ( ! [X23,X21,X22] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X21,X22),X23),X21) = k4_xboole_0(X23,X21)) )),
% 7.13/1.29    inference(superposition,[],[f71,f1834])).
% 7.13/1.29  fof(f16216,plain,(
% 7.13/1.29    ( ! [X92,X90,X91] : (k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X91,X90),X92),k2_xboole_0(X90,X91)),k2_xboole_0(X90,X91))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f15909,f21])).
% 7.13/1.29  fof(f15909,plain,(
% 7.13/1.29    ( ! [X92,X90,X91] : (k2_xboole_0(k2_xboole_0(X91,X90),X92) = k2_xboole_0(k4_xboole_0(k2_xboole_0(k2_xboole_0(X91,X90),X92),k2_xboole_0(X90,X91)),k4_xboole_0(k2_xboole_0(X90,X91),k1_xboole_0))) )),
% 7.13/1.29    inference(superposition,[],[f13068,f7533])).
% 7.13/1.29  fof(f7533,plain,(
% 7.13/1.29    ( ! [X19,X20,X18] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(k2_xboole_0(X19,X18),X20))) )),
% 7.13/1.29    inference(forward_demodulation,[],[f7465,f20])).
% 7.13/1.29  fof(f7465,plain,(
% 7.13/1.29    ( ! [X19,X20,X18] : (k4_xboole_0(k1_xboole_0,X20) = k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(k2_xboole_0(X19,X18),X20))) )),
% 7.13/1.29    inference(superposition,[],[f28,f7248])).
% 7.13/1.29  fof(f30,plain,(
% 7.13/1.29    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 7.13/1.29    inference(definition_unfolding,[],[f18,f27,f25])).
% 7.13/1.29  fof(f27,plain,(
% 7.13/1.29    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 7.13/1.29    inference(cnf_transformation,[],[f3])).
% 7.13/1.29  fof(f3,axiom,(
% 7.13/1.29    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 7.13/1.29  fof(f18,plain,(
% 7.13/1.29    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.13/1.29    inference(cnf_transformation,[],[f17])).
% 7.13/1.29  fof(f17,plain,(
% 7.13/1.29    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.13/1.29    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 7.13/1.29  fof(f16,plain,(
% 7.13/1.29    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.13/1.29    introduced(choice_axiom,[])).
% 7.13/1.29  fof(f15,plain,(
% 7.13/1.29    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.13/1.29    inference(ennf_transformation,[],[f13])).
% 7.13/1.29  fof(f13,negated_conjecture,(
% 7.13/1.29    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.13/1.29    inference(negated_conjecture,[],[f12])).
% 7.13/1.29  fof(f12,conjecture,(
% 7.13/1.29    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.13/1.29    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 7.13/1.29  % SZS output end Proof for theBenchmark
% 7.13/1.29  % (1724)------------------------------
% 7.13/1.29  % (1724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.13/1.29  % (1724)Termination reason: Refutation
% 7.13/1.29  
% 7.13/1.29  % (1724)Memory used [KB]: 23794
% 7.13/1.29  % (1724)Time elapsed: 0.820 s
% 7.13/1.29  % (1724)------------------------------
% 7.13/1.29  % (1724)------------------------------
% 7.13/1.30  % (1701)Success in time 0.932 s
%------------------------------------------------------------------------------
