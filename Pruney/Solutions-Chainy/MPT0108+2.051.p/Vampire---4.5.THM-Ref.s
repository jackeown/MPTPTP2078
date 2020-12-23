%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:25 EST 2020

% Result     : Theorem 40.35s
% Output     : Refutation 40.35s
% Verified   : 
% Statistics : Number of formulae       :  207 (117073 expanded)
%              Number of leaves         :   14 (39885 expanded)
%              Depth                    :   41
%              Number of atoms          :  217 (117218 expanded)
%              Number of equality atoms :  216 (117217 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64261,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f64260])).

fof(f64260,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f407,f64259])).

fof(f64259,plain,(
    ! [X287,X286] : k5_xboole_0(X286,X287) = k4_xboole_0(k5_xboole_0(X286,k4_xboole_0(X287,X286)),k4_xboole_0(X286,k4_xboole_0(X286,X287))) ),
    inference(forward_demodulation,[],[f64025,f64134])).

fof(f64134,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k4_xboole_0(X30,k5_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f64133,f149])).

fof(f149,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f64133,plain,(
    ! [X30,X31] : k5_xboole_0(X30,k4_xboole_0(X30,X31)) = k4_xboole_0(X30,k5_xboole_0(X30,X31)) ),
    inference(forward_demodulation,[],[f63936,f52632])).

fof(f52632,plain,(
    ! [X114,X113] : k4_xboole_0(X113,X114) = k4_xboole_0(k5_xboole_0(X113,X114),k4_xboole_0(X114,X113)) ),
    inference(forward_demodulation,[],[f52628,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f34,f20])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f52628,plain,(
    ! [X114,X113] : k5_xboole_0(k4_xboole_0(X113,X114),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X113,X114),k4_xboole_0(X114,X113)) ),
    inference(backward_demodulation,[],[f36890,f52498])).

fof(f52498,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3)) ),
    inference(superposition,[],[f2450,f33243])).

fof(f33243,plain,(
    ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f291,f30935])).

fof(f30935,plain,(
    ! [X76,X77] : k4_xboole_0(X77,X76) = k5_xboole_0(X76,k5_xboole_0(X77,k4_xboole_0(X76,X77))) ),
    inference(backward_demodulation,[],[f24814,f30929])).

fof(f30929,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(forward_demodulation,[],[f30749,f29524])).

fof(f29524,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),X0)) ),
    inference(forward_demodulation,[],[f29305,f14262])).

fof(f14262,plain,(
    ! [X33,X34,X32] : k4_xboole_0(k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X34),X32) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X34),k4_xboole_0(X32,X34)) ),
    inference(superposition,[],[f145,f1209])).

fof(f1209,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19) ),
    inference(forward_demodulation,[],[f1132,f114])).

fof(f114,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f111,f40])).

fof(f111,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f32,f103])).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f91,f20])).

fof(f91,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f36,f20])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f25,f25])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1132,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(k4_xboole_0(X17,k1_xboole_0),X19) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f25,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f145,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f37,f36])).

fof(f29305,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),k4_xboole_0(X0,X1))) ),
    inference(unit_resulting_resolution,[],[f14266,f18138])).

fof(f18138,plain,(
    ! [X12,X11] :
      ( k1_xboole_0 != k4_xboole_0(X11,X12)
      | k4_xboole_0(X12,k4_xboole_0(X12,X11)) = X11 ) ),
    inference(forward_demodulation,[],[f18072,f471])).

fof(f471,plain,(
    ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6 ),
    inference(superposition,[],[f257,f96])).

fof(f96,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f32,f36])).

fof(f257,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f246,f40])).

fof(f246,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f200,f118])).

fof(f118,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(backward_demodulation,[],[f86,f114])).

fof(f86,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0))) ),
    inference(superposition,[],[f72,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f32,f35])).

fof(f200,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2 ),
    inference(forward_demodulation,[],[f197,f196])).

fof(f196,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f185,f40])).

fof(f185,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f116,f117])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f72,f114])).

fof(f116,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f88,f114])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1)) ),
    inference(superposition,[],[f29,f72])).

fof(f197,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2 ),
    inference(backward_demodulation,[],[f166,f196])).

fof(f166,plain,(
    ! [X2,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f29,f121])).

fof(f121,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1) ),
    inference(superposition,[],[f117,f57])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f29,f40])).

fof(f18072,plain,(
    ! [X12,X11] :
      ( k1_xboole_0 != k4_xboole_0(X11,X12)
      | k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),k4_xboole_0(X11,X12)) ) ),
    inference(superposition,[],[f725,f145])).

fof(f725,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,X0)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f691,f35])).

fof(f691,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X1,X0) != k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ) ),
    inference(superposition,[],[f28,f485])).

fof(f485,plain,(
    ! [X8,X9] : k4_xboole_0(X9,X8) = k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8) ),
    inference(forward_demodulation,[],[f484,f267])).

fof(f267,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5 ),
    inference(superposition,[],[f257,f257])).

fof(f484,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8) = k5_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8) ),
    inference(forward_demodulation,[],[f458,f114])).

fof(f458,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8) = k5_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k1_xboole_0)) ),
    inference(superposition,[],[f96,f35])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f14266,plain,(
    ! [X47,X48,X49] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X47,X49),k4_xboole_0(k5_xboole_0(X47,k4_xboole_0(X48,X47)),X49)) ),
    inference(superposition,[],[f357,f1209])).

fof(f357,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f278,f36])).

fof(f278,plain,(
    ! [X14,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) ),
    inference(backward_demodulation,[],[f151,f265])).

fof(f265,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f257,f32])).

fof(f151,plain,(
    ! [X14,X13] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k5_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,X14))) ),
    inference(superposition,[],[f35,f37])).

fof(f30749,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),X0)) ),
    inference(unit_resulting_resolution,[],[f30384,f17956])).

fof(f17956,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 != k4_xboole_0(X8,X9)
      | k4_xboole_0(X8,k4_xboole_0(X8,X9)) = X8 ) ),
    inference(superposition,[],[f390,f37])).

fof(f390,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3))
      | k4_xboole_0(X2,X3) = X2 ) ),
    inference(superposition,[],[f28,f373])).

fof(f373,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f350,f145])).

fof(f350,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X2) ),
    inference(superposition,[],[f278,f36])).

fof(f30384,plain,(
    ! [X101,X100] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X100,k4_xboole_0(X101,X100)),X101),X100) ),
    inference(superposition,[],[f29824,f728])).

fof(f728,plain,(
    ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X9,X8)) = X8 ),
    inference(forward_demodulation,[],[f727,f114])).

fof(f727,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f695,f35])).

fof(f695,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k5_xboole_0(X8,k4_xboole_0(X9,X8)))) = k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X9,X8)) ),
    inference(superposition,[],[f36,f485])).

fof(f29824,plain,(
    ! [X19,X17,X18] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,k4_xboole_0(X18,X19))) ),
    inference(superposition,[],[f29400,f1627])).

fof(f1627,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19)) ),
    inference(superposition,[],[f1596,f1336])).

fof(f1336,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(forward_demodulation,[],[f1298,f40])).

fof(f1298,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f32,f1149])).

fof(f1149,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f38,f278])).

fof(f1596,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0 ),
    inference(forward_demodulation,[],[f1532,f40])).

fof(f1532,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) ),
    inference(superposition,[],[f32,f1340])).

fof(f1340,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X10,X9),X11))) ),
    inference(forward_demodulation,[],[f1300,f20])).

fof(f1300,plain,(
    ! [X10,X11,X9] : k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X10,X9),X11))) = k4_xboole_0(k1_xboole_0,X11) ),
    inference(superposition,[],[f38,f1149])).

fof(f29400,plain,(
    ! [X12,X10,X11] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12)) ),
    inference(superposition,[],[f14266,f287])).

fof(f287,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1 ),
    inference(superposition,[],[f266,f32])).

fof(f266,plain,(
    ! [X4,X3] : k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3 ),
    inference(superposition,[],[f257,f200])).

fof(f24814,plain,(
    ! [X76,X77] : k4_xboole_0(k5_xboole_0(X77,k4_xboole_0(X76,X77)),X76) = k5_xboole_0(X76,k5_xboole_0(X77,k4_xboole_0(X76,X77))) ),
    inference(forward_demodulation,[],[f24685,f114])).

fof(f24685,plain,(
    ! [X76,X77] : k4_xboole_0(k5_xboole_0(X77,k4_xboole_0(X76,X77)),X76) = k5_xboole_0(k4_xboole_0(X76,k1_xboole_0),k5_xboole_0(X77,k4_xboole_0(X76,X77))) ),
    inference(superposition,[],[f628,f24321])).

fof(f24321,plain,(
    ! [X78,X79] : k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78))) ),
    inference(superposition,[],[f9253,f267])).

fof(f9253,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2))) ),
    inference(forward_demodulation,[],[f9252,f273])).

fof(f273,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f200,f257])).

fof(f9252,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2)) ),
    inference(forward_demodulation,[],[f9068,f4696])).

fof(f4696,plain,(
    ! [X80,X81,X79] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80)))) ),
    inference(superposition,[],[f283,f473])).

fof(f473,plain,(
    ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10) ),
    inference(superposition,[],[f267,f96])).

fof(f283,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5))) ),
    inference(forward_demodulation,[],[f274,f29])).

fof(f274,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5)) ),
    inference(superposition,[],[f29,f257])).

fof(f9068,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2))))) ),
    inference(superposition,[],[f61,f149])).

fof(f61,plain,(
    ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,k5_xboole_0(X2,X3))))) ),
    inference(superposition,[],[f35,f29])).

fof(f628,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X15) ),
    inference(superposition,[],[f267,f157])).

fof(f157,plain,(
    ! [X4,X3] : k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k5_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f97,f145])).

fof(f97,plain,(
    ! [X4,X3] : k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k5_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3)))) ),
    inference(superposition,[],[f32,f36])).

fof(f291,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,X10)),X10) ),
    inference(superposition,[],[f266,f29])).

fof(f2450,plain,(
    ! [X30,X28,X29] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X29,X30),k5_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29))) ),
    inference(superposition,[],[f35,f1627])).

fof(f36890,plain,(
    ! [X114,X113] : k4_xboole_0(k5_xboole_0(X113,X114),k4_xboole_0(X114,X113)) = k5_xboole_0(k4_xboole_0(X113,X114),k4_xboole_0(k4_xboole_0(X114,X113),k5_xboole_0(X113,X114))) ),
    inference(superposition,[],[f33240,f33240])).

fof(f33240,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f205,f30935])).

fof(f205,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) = X10 ),
    inference(forward_demodulation,[],[f190,f196])).

fof(f190,plain,(
    ! [X10,X8,X9] : k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) ),
    inference(superposition,[],[f116,f29])).

fof(f63936,plain,(
    ! [X30,X31] : k4_xboole_0(X30,k5_xboole_0(X30,X31)) = k5_xboole_0(X30,k4_xboole_0(k5_xboole_0(X30,X31),k4_xboole_0(X31,X30))) ),
    inference(superposition,[],[f96,f63364])).

fof(f63364,plain,(
    ! [X28,X27] : k4_xboole_0(X28,X27) = k4_xboole_0(k5_xboole_0(X27,X28),X27) ),
    inference(forward_demodulation,[],[f63161,f40])).

fof(f63161,plain,(
    ! [X28,X27] : k4_xboole_0(k5_xboole_0(X27,X28),X27) = k5_xboole_0(k4_xboole_0(X28,X27),k1_xboole_0) ),
    inference(superposition,[],[f55695,f200])).

fof(f55695,plain,(
    ! [X94,X93] : k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X94,X93),X94),k1_xboole_0) ),
    inference(forward_demodulation,[],[f55694,f53619])).

fof(f53619,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f53258,f53617])).

fof(f53617,plain,(
    ! [X61,X62] : k4_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61)) = k4_xboole_0(X61,k5_xboole_0(X61,X62)) ),
    inference(forward_demodulation,[],[f53616,f31906])).

fof(f31906,plain,(
    ! [X15,X16] : k5_xboole_0(X16,k4_xboole_0(k5_xboole_0(X15,X16),X15)) = k4_xboole_0(X15,k5_xboole_0(X15,X16)) ),
    inference(superposition,[],[f30932,f766])).

fof(f766,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24)) ),
    inference(superposition,[],[f205,f257])).

fof(f30932,plain,(
    ! [X28,X29] : k4_xboole_0(X29,X28) = k5_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28) ),
    inference(backward_demodulation,[],[f24789,f30929])).

fof(f24789,plain,(
    ! [X28,X29] : k4_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28) = k5_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28) ),
    inference(forward_demodulation,[],[f24665,f114])).

fof(f24665,plain,(
    ! [X28,X29] : k4_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28) = k5_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),k4_xboole_0(X28,k1_xboole_0)) ),
    inference(superposition,[],[f96,f24321])).

fof(f53616,plain,(
    ! [X61,X62] : k4_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61)) = k5_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61)) ),
    inference(forward_demodulation,[],[f53384,f114])).

fof(f53384,plain,(
    ! [X61,X62] : k4_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61)) = k5_xboole_0(X62,k4_xboole_0(k4_xboole_0(k5_xboole_0(X61,X62),X61),k1_xboole_0)) ),
    inference(superposition,[],[f96,f52719])).

fof(f52719,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X2,X1),X2),X1) ),
    inference(superposition,[],[f52504,f273])).

fof(f52504,plain,(
    ! [X15,X16] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,X16),X16),X15) ),
    inference(superposition,[],[f2450,f44791])).

fof(f44791,plain,(
    ! [X41,X42] : k5_xboole_0(k4_xboole_0(k5_xboole_0(X41,X42),X42),k4_xboole_0(X42,k5_xboole_0(X41,X42))) = X41 ),
    inference(superposition,[],[f257,f24562])).

fof(f24562,plain,(
    ! [X28,X27] : k5_xboole_0(X27,k4_xboole_0(k5_xboole_0(X27,X28),X28)) = k4_xboole_0(X28,k5_xboole_0(X27,X28)) ),
    inference(backward_demodulation,[],[f24531,f24561])).

fof(f24561,plain,(
    ! [X76,X75] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k4_xboole_0(X76,k5_xboole_0(X75,X76)) ),
    inference(forward_demodulation,[],[f24560,f32])).

fof(f24560,plain,(
    ! [X76,X75] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k5_xboole_0(X76,k4_xboole_0(X76,k4_xboole_0(X76,k5_xboole_0(X75,X76)))) ),
    inference(forward_demodulation,[],[f24559,f1064])).

fof(f1064,plain,(
    ! [X12,X13,X11] : k5_xboole_0(X13,k4_xboole_0(X12,k4_xboole_0(X12,X11))) = k5_xboole_0(X11,k5_xboole_0(X13,k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f283,f96])).

fof(f24559,plain,(
    ! [X76,X75] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k5_xboole_0(k5_xboole_0(X75,X76),k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76))) ),
    inference(forward_demodulation,[],[f24390,f114])).

fof(f24390,plain,(
    ! [X76,X75] : k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X75,X76),k1_xboole_0),k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76))) ),
    inference(superposition,[],[f628,f9253])).

fof(f24531,plain,(
    ! [X28,X27] : k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28)) = k5_xboole_0(X27,k4_xboole_0(k5_xboole_0(X27,X28),X28)) ),
    inference(forward_demodulation,[],[f24530,f1008])).

fof(f1008,plain,(
    ! [X24,X23,X25] : k5_xboole_0(X25,X23) = k5_xboole_0(k5_xboole_0(X24,X23),k5_xboole_0(X25,X24)) ),
    inference(superposition,[],[f269,f257])).

fof(f269,plain,(
    ! [X10,X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X10,k5_xboole_0(X8,k5_xboole_0(X9,X10))) ),
    inference(superposition,[],[f257,f29])).

fof(f24530,plain,(
    ! [X28,X27] : k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28)) = k5_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f24370,f114])).

fof(f24370,plain,(
    ! [X28,X27] : k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28)) = k5_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k4_xboole_0(k5_xboole_0(X27,X28),k1_xboole_0)) ),
    inference(superposition,[],[f96,f9253])).

fof(f53258,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),X0))) ),
    inference(unit_resulting_resolution,[],[f52719,f18138])).

fof(f55694,plain,(
    ! [X94,X93] : k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(X93,k4_xboole_0(X94,k5_xboole_0(X94,X93))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f55693,f53617])).

fof(f55693,plain,(
    ! [X94,X93] : k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(X93,k4_xboole_0(X93,k4_xboole_0(k5_xboole_0(X94,X93),X94))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f55692,f34129])).

fof(f34129,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),X38)) = k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X38,X37))) ),
    inference(backward_demodulation,[],[f2666,f34122])).

fof(f34122,plain,(
    ! [X57,X58,X56] : k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,X57))) ),
    inference(forward_demodulation,[],[f34121,f1208])).

fof(f1208,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))) = k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X14,X16))))) ),
    inference(forward_demodulation,[],[f1207,f38])).

fof(f1207,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X16))) = k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))) ),
    inference(forward_demodulation,[],[f1131,f38])).

fof(f1131,plain,(
    ! [X14,X15,X16] : k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X16))) = k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X16) ),
    inference(superposition,[],[f38,f145])).

fof(f34121,plain,(
    ! [X57,X58,X56] : k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(X56,X57))))) ),
    inference(forward_demodulation,[],[f34108,f2778])).

fof(f2778,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,X10)))) ),
    inference(forward_demodulation,[],[f2777,f37])).

fof(f2777,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10)))))) ),
    inference(forward_demodulation,[],[f2559,f2487])).

fof(f2487,plain,(
    ! [X45,X46,X44] : k4_xboole_0(X45,X46) = k4_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(X44,X45)) ),
    inference(forward_demodulation,[],[f2486,f40])).

fof(f2486,plain,(
    ! [X45,X46,X44] : k4_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(X44,X45)) = k5_xboole_0(k4_xboole_0(X45,X46),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2455,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f42,f40])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f35,f20])).

fof(f2455,plain,(
    ! [X45,X46,X44] : k4_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(X44,X45)) = k5_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X45))) ),
    inference(superposition,[],[f96,f1627])).

fof(f2559,plain,(
    ! [X12,X10,X11] : k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10)))))) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X10,X10)) ),
    inference(superposition,[],[f41,f1375])).

fof(f1375,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X24)))) = X24 ),
    inference(superposition,[],[f1336,f38])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2)))) ),
    inference(forward_demodulation,[],[f39,f38])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f31,f25,f25,f25,f25])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f34108,plain,(
    ! [X57,X58,X56] : k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)))))) ),
    inference(backward_demodulation,[],[f30151,f34051])).

fof(f34051,plain,(
    ! [X35,X33,X34] : k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,X35))))) = k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X35))) ),
    inference(forward_demodulation,[],[f33700,f32])).

fof(f33700,plain,(
    ! [X35,X33,X34] : k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,X35))))) = k5_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X35))))) ),
    inference(superposition,[],[f32,f2582])).

fof(f2582,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))))) ),
    inference(superposition,[],[f41,f38])).

fof(f30151,plain,(
    ! [X57,X58,X56] : k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)))))))) ),
    inference(forward_demodulation,[],[f29925,f114])).

fof(f29925,plain,(
    ! [X57,X58,X56] : k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)),k1_xboole_0) ),
    inference(superposition,[],[f1242,f29400])).

fof(f1242,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) = k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,X18)))))) ),
    inference(forward_demodulation,[],[f1155,f38])).

fof(f1155,plain,(
    ! [X17,X18,X16] : k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) = k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),X18)))) ),
    inference(superposition,[],[f38,f36])).

fof(f2666,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,X38)) = k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),X38)) ),
    inference(forward_demodulation,[],[f2665,f1216])).

fof(f1216,plain,(
    ! [X26,X27,X25] : k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,X27))) = k4_xboole_0(k4_xboole_0(X25,X26),X27) ),
    inference(forward_demodulation,[],[f1135,f114])).

fof(f1135,plain,(
    ! [X26,X27,X25] : k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,X27))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X25,X26),k1_xboole_0),X27) ),
    inference(superposition,[],[f38,f373])).

fof(f2665,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),X38)) ),
    inference(forward_demodulation,[],[f2664,f114])).

fof(f2664,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(k4_xboole_0(X36,X37),X38)) ),
    inference(forward_demodulation,[],[f2663,f1204])).

fof(f1204,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(forward_demodulation,[],[f1203,f145])).

fof(f1203,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4) ),
    inference(forward_demodulation,[],[f1127,f149])).

fof(f1127,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2))),X4) ),
    inference(superposition,[],[f38,f157])).

fof(f2663,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(k4_xboole_0(X36,X37),X38)))) ),
    inference(forward_demodulation,[],[f2662,f38])).

fof(f2662,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X36,X37))),X38)) ),
    inference(forward_demodulation,[],[f2514,f1229])).

fof(f1229,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(forward_demodulation,[],[f1142,f149])).

fof(f1142,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f38,f157])).

fof(f2514,plain,(
    ! [X37,X38,X36] : k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,X38)))) ),
    inference(superposition,[],[f41,f373])).

fof(f55692,plain,(
    ! [X94,X93] : k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,X94),k4_xboole_0(k4_xboole_0(X93,X94),k5_xboole_0(X94,X93))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f55467,f36])).

fof(f55467,plain,(
    ! [X94,X93] : k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X94,X93),k4_xboole_0(k5_xboole_0(X94,X93),k4_xboole_0(X93,X94))),k1_xboole_0) ),
    inference(superposition,[],[f471,f52498])).

fof(f64025,plain,(
    ! [X287,X286] : k5_xboole_0(X286,X287) = k4_xboole_0(k5_xboole_0(X286,k4_xboole_0(X287,X286)),k4_xboole_0(X286,k5_xboole_0(X286,X287))) ),
    inference(superposition,[],[f30931,f63364])).

fof(f30931,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f24610,f30929])).

fof(f24610,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = X1 ),
    inference(unit_resulting_resolution,[],[f24321,f18138])).

fof(f407,plain,(
    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f33,f28])).

fof(f33,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f24,f25])).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).

fof(f17,plain,
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:21:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (13031)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (13042)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (13034)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (13030)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (13042)Refutation not found, incomplete strategy% (13042)------------------------------
% 0.21/0.52  % (13042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13042)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13042)Memory used [KB]: 10618
% 0.21/0.52  % (13042)Time elapsed: 0.061 s
% 0.21/0.52  % (13042)------------------------------
% 0.21/0.52  % (13042)------------------------------
% 0.21/0.52  % (13025)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (13039)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (13026)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (13047)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (13043)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (13038)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (13043)Refutation not found, incomplete strategy% (13043)------------------------------
% 0.21/0.53  % (13043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13043)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13043)Memory used [KB]: 1663
% 0.21/0.53  % (13043)Time elapsed: 0.120 s
% 0.21/0.53  % (13043)------------------------------
% 0.21/0.53  % (13043)------------------------------
% 0.21/0.53  % (13021)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (13022)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (13020)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (13023)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (13020)Refutation not found, incomplete strategy% (13020)------------------------------
% 0.21/0.54  % (13020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13020)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13020)Memory used [KB]: 1663
% 0.21/0.54  % (13020)Time elapsed: 0.125 s
% 0.21/0.54  % (13020)------------------------------
% 0.21/0.54  % (13020)------------------------------
% 0.21/0.54  % (13022)Refutation not found, incomplete strategy% (13022)------------------------------
% 0.21/0.54  % (13022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13022)Memory used [KB]: 10618
% 0.21/0.54  % (13022)Time elapsed: 0.124 s
% 0.21/0.54  % (13022)------------------------------
% 0.21/0.54  % (13022)------------------------------
% 0.21/0.54  % (13024)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (13044)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (13035)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (13032)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (13037)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (13041)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (13036)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (13041)Refutation not found, incomplete strategy% (13041)------------------------------
% 0.21/0.54  % (13041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13041)Memory used [KB]: 1663
% 0.21/0.54  % (13041)Time elapsed: 0.138 s
% 0.21/0.54  % (13041)------------------------------
% 0.21/0.54  % (13041)------------------------------
% 0.21/0.54  % (13029)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (13027)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (13045)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.55  % (13048)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.48/0.55  % (13046)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.55  % (13028)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.55  % (13049)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.55  % (13033)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.55  % (13028)Refutation not found, incomplete strategy% (13028)------------------------------
% 1.48/0.55  % (13028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (13028)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (13028)Memory used [KB]: 10618
% 1.48/0.55  % (13028)Time elapsed: 0.139 s
% 1.48/0.55  % (13028)------------------------------
% 1.48/0.55  % (13028)------------------------------
% 1.48/0.55  % (13037)Refutation not found, incomplete strategy% (13037)------------------------------
% 1.48/0.55  % (13037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (13037)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (13037)Memory used [KB]: 10618
% 1.48/0.55  % (13037)Time elapsed: 0.139 s
% 1.48/0.55  % (13037)------------------------------
% 1.48/0.55  % (13037)------------------------------
% 1.48/0.56  % (13040)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.56  % (13040)Refutation not found, incomplete strategy% (13040)------------------------------
% 1.48/0.56  % (13040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (13040)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (13040)Memory used [KB]: 10618
% 1.48/0.56  % (13040)Time elapsed: 0.150 s
% 1.48/0.56  % (13040)------------------------------
% 1.48/0.56  % (13040)------------------------------
% 2.03/0.66  % (13051)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.67  % (13050)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.19/0.67  % (13050)Refutation not found, incomplete strategy% (13050)------------------------------
% 2.19/0.67  % (13050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (13050)Termination reason: Refutation not found, incomplete strategy
% 2.19/0.67  
% 2.19/0.67  % (13050)Memory used [KB]: 6140
% 2.19/0.67  % (13050)Time elapsed: 0.109 s
% 2.19/0.67  % (13050)------------------------------
% 2.19/0.67  % (13050)------------------------------
% 2.19/0.67  % (13052)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.19/0.68  % (13053)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.19/0.68  % (13054)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.19/0.68  % (13056)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.19/0.69  % (13055)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.19/0.70  % (13057)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.72/0.81  % (13058)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.12/0.85  % (13025)Time limit reached!
% 3.12/0.85  % (13025)------------------------------
% 3.12/0.85  % (13025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.85  % (13025)Termination reason: Time limit
% 3.12/0.85  % (13025)Termination phase: Saturation
% 3.12/0.85  
% 3.12/0.85  % (13025)Memory used [KB]: 9466
% 3.12/0.85  % (13025)Time elapsed: 0.400 s
% 3.12/0.85  % (13025)------------------------------
% 3.12/0.85  % (13025)------------------------------
% 3.36/0.93  % (13021)Time limit reached!
% 3.36/0.93  % (13021)------------------------------
% 3.36/0.93  % (13021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.93  % (13021)Termination reason: Time limit
% 3.36/0.93  
% 3.36/0.93  % (13021)Memory used [KB]: 9083
% 3.36/0.93  % (13021)Time elapsed: 0.516 s
% 3.36/0.93  % (13021)------------------------------
% 3.36/0.93  % (13021)------------------------------
% 3.77/0.96  % (13032)Time limit reached!
% 3.77/0.96  % (13032)------------------------------
% 3.77/0.96  % (13032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.77/0.96  % (13032)Termination reason: Time limit
% 3.77/0.96  % (13032)Termination phase: Saturation
% 3.77/0.96  
% 3.77/0.96  % (13032)Memory used [KB]: 11001
% 3.77/0.96  % (13032)Time elapsed: 0.547 s
% 3.77/0.96  % (13032)------------------------------
% 3.77/0.96  % (13032)------------------------------
% 3.93/0.99  % (13053)Time limit reached!
% 3.93/0.99  % (13053)------------------------------
% 3.93/0.99  % (13053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/0.99  % (13053)Termination reason: Time limit
% 3.93/0.99  
% 3.93/0.99  % (13053)Memory used [KB]: 8187
% 3.93/0.99  % (13053)Time elapsed: 0.413 s
% 3.93/0.99  % (13053)------------------------------
% 3.93/0.99  % (13053)------------------------------
% 3.93/0.99  % (13059)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 3.93/1.01  % (13027)Time limit reached!
% 3.93/1.01  % (13027)------------------------------
% 3.93/1.01  % (13027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/1.01  % (13027)Termination reason: Time limit
% 3.93/1.01  
% 3.93/1.01  % (13027)Memory used [KB]: 12025
% 3.93/1.01  % (13027)Time elapsed: 0.601 s
% 3.93/1.01  % (13027)------------------------------
% 3.93/1.01  % (13027)------------------------------
% 3.93/1.02  % (13036)Time limit reached!
% 3.93/1.02  % (13036)------------------------------
% 3.93/1.02  % (13036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/1.02  % (13036)Termination reason: Time limit
% 3.93/1.02  
% 3.93/1.02  % (13036)Memory used [KB]: 16247
% 3.93/1.02  % (13036)Time elapsed: 0.609 s
% 3.93/1.02  % (13036)------------------------------
% 3.93/1.02  % (13036)------------------------------
% 3.93/1.02  % (13054)Time limit reached!
% 3.93/1.02  % (13054)------------------------------
% 3.93/1.02  % (13054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.93/1.02  % (13054)Termination reason: Time limit
% 3.93/1.02  
% 3.93/1.02  % (13054)Memory used [KB]: 16630
% 3.93/1.02  % (13054)Time elapsed: 0.409 s
% 3.93/1.02  % (13054)------------------------------
% 3.93/1.02  % (13054)------------------------------
% 4.60/1.05  % (13048)Time limit reached!
% 4.60/1.05  % (13048)------------------------------
% 4.60/1.05  % (13048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.05  % (13048)Termination reason: Time limit
% 4.60/1.05  
% 4.60/1.05  % (13048)Memory used [KB]: 11129
% 4.60/1.05  % (13048)Time elapsed: 0.642 s
% 4.60/1.05  % (13048)------------------------------
% 4.60/1.05  % (13048)------------------------------
% 4.60/1.07  % (13060)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.60/1.07  % (13060)Refutation not found, incomplete strategy% (13060)------------------------------
% 4.60/1.07  % (13060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.60/1.07  % (13060)Termination reason: Refutation not found, incomplete strategy
% 4.60/1.07  
% 4.60/1.07  % (13060)Memory used [KB]: 6140
% 4.60/1.07  % (13060)Time elapsed: 0.108 s
% 4.60/1.07  % (13060)------------------------------
% 4.60/1.07  % (13060)------------------------------
% 5.56/1.10  % (13061)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.56/1.10  % (13061)Refutation not found, incomplete strategy% (13061)------------------------------
% 5.56/1.10  % (13061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.56/1.10  % (13061)Termination reason: Refutation not found, incomplete strategy
% 5.56/1.10  
% 5.56/1.10  % (13061)Memory used [KB]: 1663
% 5.56/1.10  % (13061)Time elapsed: 0.109 s
% 5.56/1.10  % (13061)------------------------------
% 5.56/1.10  % (13061)------------------------------
% 5.56/1.11  % (13062)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.56/1.13  % (13063)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.56/1.13  % (13063)Refutation not found, incomplete strategy% (13063)------------------------------
% 5.56/1.13  % (13063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.56/1.13  % (13063)Termination reason: Refutation not found, incomplete strategy
% 5.56/1.13  
% 5.56/1.13  % (13063)Memory used [KB]: 1663
% 5.56/1.13  % (13063)Time elapsed: 0.073 s
% 5.56/1.13  % (13063)------------------------------
% 5.56/1.13  % (13063)------------------------------
% 5.56/1.14  % (13064)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.16/1.16  % (13065)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.16/1.16  % (13065)Refutation not found, incomplete strategy% (13065)------------------------------
% 6.16/1.16  % (13065)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.16/1.16  % (13065)Termination reason: Refutation not found, incomplete strategy
% 6.16/1.16  
% 6.16/1.16  % (13065)Memory used [KB]: 6140
% 6.16/1.16  % (13065)Time elapsed: 0.113 s
% 6.16/1.16  % (13065)------------------------------
% 6.16/1.16  % (13065)------------------------------
% 6.16/1.16  % (13030)Time limit reached!
% 6.16/1.16  % (13030)------------------------------
% 6.16/1.16  % (13030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.16/1.16  % (13030)Termination reason: Time limit
% 6.16/1.16  
% 6.16/1.16  % (13030)Memory used [KB]: 65244
% 6.16/1.16  % (13030)Time elapsed: 0.713 s
% 6.16/1.16  % (13030)------------------------------
% 6.16/1.16  % (13030)------------------------------
% 6.43/1.19  % (13066)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.43/1.19  % (13067)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.81/1.25  % (13068)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.81/1.27  % (13069)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.81/1.30  % (13071)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.22/1.32  % (13072)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.33/1.49  % (13066)Time limit reached!
% 8.33/1.49  % (13066)------------------------------
% 8.33/1.49  % (13066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.33/1.50  % (13066)Termination reason: Time limit
% 8.33/1.50  
% 8.33/1.50  % (13066)Memory used [KB]: 4093
% 8.33/1.50  % (13066)Time elapsed: 0.416 s
% 8.33/1.50  % (13066)------------------------------
% 8.33/1.50  % (13066)------------------------------
% 8.90/1.55  % (13062)Time limit reached!
% 8.90/1.55  % (13062)------------------------------
% 8.90/1.55  % (13062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.90/1.56  % (13062)Termination reason: Time limit
% 8.90/1.56  
% 8.90/1.56  % (13062)Memory used [KB]: 5884
% 8.90/1.56  % (13062)Time elapsed: 0.534 s
% 8.90/1.56  % (13062)------------------------------
% 8.90/1.56  % (13062)------------------------------
% 8.90/1.59  % (13069)Time limit reached!
% 8.90/1.59  % (13069)------------------------------
% 8.90/1.59  % (13069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.90/1.59  % (13069)Termination reason: Time limit
% 8.90/1.59  % (13069)Termination phase: Saturation
% 8.90/1.59  
% 8.90/1.59  % (13069)Memory used [KB]: 4093
% 8.90/1.59  % (13069)Time elapsed: 0.400 s
% 8.90/1.59  % (13069)------------------------------
% 8.90/1.59  % (13069)------------------------------
% 9.91/1.63  % (13073)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 10.30/1.69  % (13074)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.30/1.72  % (13075)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.24/1.80  % (13056)Time limit reached!
% 11.24/1.80  % (13056)------------------------------
% 11.24/1.80  % (13056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.24/1.81  % (13044)Time limit reached!
% 11.24/1.81  % (13044)------------------------------
% 11.24/1.81  % (13044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.24/1.81  % (13056)Termination reason: Time limit
% 11.24/1.81  
% 11.24/1.81  % (13056)Memory used [KB]: 13560
% 11.24/1.81  % (13056)Time elapsed: 1.221 s
% 11.24/1.81  % (13056)------------------------------
% 11.24/1.81  % (13056)------------------------------
% 11.24/1.82  % (13044)Termination reason: Time limit
% 11.24/1.82  
% 11.24/1.82  % (13044)Memory used [KB]: 23539
% 11.24/1.82  % (13044)Time elapsed: 1.371 s
% 11.24/1.82  % (13044)------------------------------
% 11.24/1.82  % (13044)------------------------------
% 12.12/1.94  % (13047)Time limit reached!
% 12.12/1.94  % (13047)------------------------------
% 12.12/1.94  % (13047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.95  % (13047)Termination reason: Time limit
% 12.12/1.95  
% 12.12/1.95  % (13047)Memory used [KB]: 18038
% 12.12/1.95  % (13047)Time elapsed: 1.527 s
% 12.12/1.95  % (13047)------------------------------
% 12.12/1.95  % (13047)------------------------------
% 12.12/1.95  % (13077)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 12.12/1.95  % (13076)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 12.12/1.95  % (13076)Refutation not found, incomplete strategy% (13076)------------------------------
% 12.12/1.95  % (13076)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.12/1.96  % (13076)Termination reason: Refutation not found, incomplete strategy
% 12.12/1.96  
% 12.12/1.96  % (13076)Memory used [KB]: 6140
% 12.12/1.96  % (13076)Time elapsed: 0.090 s
% 12.12/1.96  % (13076)------------------------------
% 12.12/1.96  % (13076)------------------------------
% 12.66/2.05  % (13075)Time limit reached!
% 12.66/2.05  % (13075)------------------------------
% 12.66/2.05  % (13075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.66/2.05  % (13075)Termination reason: Time limit
% 12.66/2.05  % (13075)Termination phase: Saturation
% 12.66/2.05  
% 12.66/2.05  % (13075)Memory used [KB]: 11129
% 12.66/2.05  % (13075)Time elapsed: 0.400 s
% 12.66/2.05  % (13075)------------------------------
% 12.66/2.05  % (13075)------------------------------
% 12.66/2.05  % (13031)Time limit reached!
% 12.66/2.05  % (13031)------------------------------
% 12.66/2.05  % (13031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.66/2.05  % (13031)Termination reason: Time limit
% 12.66/2.05  % (13031)Termination phase: Saturation
% 12.66/2.05  
% 12.66/2.05  % (13031)Memory used [KB]: 28272
% 12.66/2.05  % (13031)Time elapsed: 1.600 s
% 12.66/2.05  % (13031)------------------------------
% 12.66/2.05  % (13031)------------------------------
% 13.37/2.06  % (13046)Time limit reached!
% 13.37/2.06  % (13046)------------------------------
% 13.37/2.06  % (13046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.37/2.06  % (13046)Termination reason: Time limit
% 13.37/2.06  % (13046)Termination phase: Saturation
% 13.37/2.06  
% 13.37/2.06  % (13046)Memory used [KB]: 135733
% 13.37/2.06  % (13046)Time elapsed: 1.200 s
% 13.37/2.06  % (13046)------------------------------
% 13.37/2.06  % (13046)------------------------------
% 13.37/2.06  % (13078)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 13.37/2.07  % (13078)Refutation not found, incomplete strategy% (13078)------------------------------
% 13.37/2.07  % (13078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.37/2.07  % (13078)Termination reason: Refutation not found, incomplete strategy
% 13.37/2.07  
% 13.37/2.07  % (13078)Memory used [KB]: 10618
% 13.37/2.07  % (13078)Time elapsed: 0.007 s
% 13.37/2.07  % (13078)------------------------------
% 13.37/2.07  % (13078)------------------------------
% 13.60/2.10  % (13035)Time limit reached!
% 13.60/2.10  % (13035)------------------------------
% 13.60/2.10  % (13035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.60/2.10  % (13035)Termination reason: Time limit
% 13.60/2.10  % (13035)Termination phase: Saturation
% 13.60/2.10  
% 13.60/2.10  % (13035)Memory used [KB]: 190871
% 13.60/2.10  % (13035)Time elapsed: 1.300 s
% 13.60/2.10  % (13035)------------------------------
% 13.60/2.10  % (13035)------------------------------
% 14.77/2.25  % (13024)Time limit reached!
% 14.77/2.25  % (13024)------------------------------
% 14.77/2.25  % (13024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.77/2.25  % (13024)Termination reason: Time limit
% 14.77/2.25  
% 14.77/2.25  % (13024)Memory used [KB]: 143281
% 14.77/2.25  % (13024)Time elapsed: 1.775 s
% 14.77/2.25  % (13024)------------------------------
% 14.77/2.25  % (13024)------------------------------
% 14.77/2.27  % (13034)Time limit reached!
% 14.77/2.27  % (13034)------------------------------
% 14.77/2.27  % (13034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.77/2.27  % (13034)Termination reason: Time limit
% 14.77/2.27  % (13034)Termination phase: Saturation
% 14.77/2.27  
% 14.77/2.27  % (13034)Memory used [KB]: 21620
% 14.77/2.27  % (13034)Time elapsed: 1.800 s
% 14.77/2.27  % (13034)------------------------------
% 14.77/2.27  % (13034)------------------------------
% 14.77/2.28  % (13052)Time limit reached!
% 14.77/2.28  % (13052)------------------------------
% 14.77/2.28  % (13052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.77/2.28  % (13052)Termination reason: Time limit
% 14.77/2.28  
% 14.77/2.28  % (13052)Memory used [KB]: 24818
% 14.77/2.28  % (13052)Time elapsed: 1.711 s
% 14.77/2.28  % (13052)------------------------------
% 14.77/2.28  % (13052)------------------------------
% 14.77/2.28  % (13077)Time limit reached!
% 14.77/2.28  % (13077)------------------------------
% 14.77/2.28  % (13077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.77/2.28  % (13077)Termination reason: Time limit
% 14.77/2.28  
% 14.77/2.28  % (13077)Memory used [KB]: 37355
% 14.77/2.28  % (13077)Time elapsed: 0.409 s
% 14.77/2.28  % (13077)------------------------------
% 14.77/2.28  % (13077)------------------------------
% 16.44/2.44  % (13038)Time limit reached!
% 16.44/2.44  % (13038)------------------------------
% 16.44/2.44  % (13038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.44/2.44  % (13038)Termination reason: Time limit
% 16.44/2.44  
% 16.44/2.44  % (13038)Memory used [KB]: 35948
% 16.44/2.44  % (13038)Time elapsed: 2.017 s
% 16.44/2.44  % (13038)------------------------------
% 16.44/2.44  % (13038)------------------------------
% 16.44/2.47  % (13026)Time limit reached!
% 16.44/2.47  % (13026)------------------------------
% 16.44/2.47  % (13026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.44/2.47  % (13026)Termination reason: Time limit
% 16.44/2.47  % (13026)Termination phase: Saturation
% 16.44/2.47  
% 16.44/2.47  % (13026)Memory used [KB]: 38250
% 16.44/2.47  % (13026)Time elapsed: 2.0000 s
% 16.44/2.47  % (13026)------------------------------
% 16.44/2.47  % (13026)------------------------------
% 16.44/2.51  % (13058)Time limit reached!
% 16.44/2.51  % (13058)------------------------------
% 16.44/2.51  % (13058)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.44/2.51  % (13058)Termination reason: Time limit
% 16.44/2.51  
% 16.44/2.51  % (13058)Memory used [KB]: 149421
% 16.44/2.51  % (13058)Time elapsed: 1.791 s
% 16.44/2.51  % (13058)------------------------------
% 16.44/2.51  % (13058)------------------------------
% 17.28/2.55  % (13068)Time limit reached!
% 17.28/2.55  % (13068)------------------------------
% 17.28/2.55  % (13068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.28/2.55  % (13068)Termination reason: Time limit
% 17.28/2.55  
% 17.28/2.55  % (13068)Memory used [KB]: 23027
% 17.28/2.55  % (13068)Time elapsed: 1.338 s
% 17.28/2.55  % (13068)------------------------------
% 17.28/2.55  % (13068)------------------------------
% 21.37/3.06  % (13039)Time limit reached!
% 21.37/3.06  % (13039)------------------------------
% 21.37/3.06  % (13039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.37/3.06  % (13039)Termination reason: Time limit
% 21.37/3.06  
% 21.37/3.06  % (13039)Memory used [KB]: 50788
% 21.37/3.06  % (13039)Time elapsed: 2.640 s
% 21.37/3.06  % (13039)------------------------------
% 21.37/3.06  % (13039)------------------------------
% 23.84/3.40  % (13051)Time limit reached!
% 23.84/3.40  % (13051)------------------------------
% 23.84/3.40  % (13051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.84/3.40  % (13051)Termination reason: Time limit
% 23.84/3.40  % (13051)Termination phase: Saturation
% 23.84/3.40  
% 23.84/3.40  % (13051)Memory used [KB]: 44903
% 23.84/3.40  % (13051)Time elapsed: 2.831 s
% 23.84/3.40  % (13051)------------------------------
% 23.84/3.40  % (13051)------------------------------
% 23.84/3.40  % (13033)Time limit reached!
% 23.84/3.40  % (13033)------------------------------
% 23.84/3.40  % (13033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.84/3.40  % (13033)Termination reason: Time limit
% 23.84/3.40  % (13033)Termination phase: Saturation
% 23.84/3.40  
% 23.84/3.40  % (13033)Memory used [KB]: 15991
% 23.84/3.40  % (13033)Time elapsed: 3.0000 s
% 23.84/3.40  % (13033)------------------------------
% 23.84/3.40  % (13033)------------------------------
% 31.03/4.32  % (13049)Time limit reached!
% 31.03/4.32  % (13049)------------------------------
% 31.03/4.32  % (13049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.03/4.32  % (13049)Termination reason: Time limit
% 31.03/4.32  % (13049)Termination phase: Saturation
% 31.03/4.32  
% 31.03/4.32  % (13049)Memory used [KB]: 72791
% 31.03/4.32  % (13049)Time elapsed: 3.900 s
% 31.03/4.32  % (13049)------------------------------
% 31.03/4.32  % (13049)------------------------------
% 36.85/5.03  % (13064)Time limit reached!
% 36.85/5.03  % (13064)------------------------------
% 36.85/5.03  % (13064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.85/5.03  % (13064)Termination reason: Time limit
% 36.85/5.03  % (13064)Termination phase: Saturation
% 36.85/5.03  
% 36.85/5.03  % (13064)Memory used [KB]: 123196
% 36.85/5.03  % (13064)Time elapsed: 3.500 s
% 36.85/5.03  % (13064)------------------------------
% 36.85/5.03  % (13064)------------------------------
% 40.35/5.44  % (13057)Refutation found. Thanks to Tanya!
% 40.35/5.44  % SZS status Theorem for theBenchmark
% 40.35/5.44  % SZS output start Proof for theBenchmark
% 40.35/5.44  fof(f64261,plain,(
% 40.35/5.44    $false),
% 40.35/5.44    inference(trivial_inequality_removal,[],[f64260])).
% 40.35/5.44  fof(f64260,plain,(
% 40.35/5.44    k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 40.35/5.44    inference(backward_demodulation,[],[f407,f64259])).
% 40.35/5.44  fof(f64259,plain,(
% 40.35/5.44    ( ! [X287,X286] : (k5_xboole_0(X286,X287) = k4_xboole_0(k5_xboole_0(X286,k4_xboole_0(X287,X286)),k4_xboole_0(X286,k4_xboole_0(X286,X287)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f64025,f64134])).
% 40.35/5.44  fof(f64134,plain,(
% 40.35/5.44    ( ! [X30,X31] : (k4_xboole_0(X30,k4_xboole_0(X30,X31)) = k4_xboole_0(X30,k5_xboole_0(X30,X31))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f64133,f149])).
% 40.35/5.44  fof(f149,plain,(
% 40.35/5.44    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X6)) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 40.35/5.44    inference(superposition,[],[f32,f37])).
% 40.35/5.44  fof(f37,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 40.35/5.44    inference(definition_unfolding,[],[f27,f25])).
% 40.35/5.44  fof(f25,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 40.35/5.44    inference(cnf_transformation,[],[f8])).
% 40.35/5.44  fof(f8,axiom,(
% 40.35/5.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 40.35/5.44  fof(f27,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 40.35/5.44    inference(cnf_transformation,[],[f7])).
% 40.35/5.44  fof(f7,axiom,(
% 40.35/5.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 40.35/5.44  fof(f32,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 40.35/5.44    inference(definition_unfolding,[],[f26,f25])).
% 40.35/5.44  fof(f26,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 40.35/5.44    inference(cnf_transformation,[],[f2])).
% 40.35/5.44  fof(f2,axiom,(
% 40.35/5.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 40.35/5.44  fof(f64133,plain,(
% 40.35/5.44    ( ! [X30,X31] : (k5_xboole_0(X30,k4_xboole_0(X30,X31)) = k4_xboole_0(X30,k5_xboole_0(X30,X31))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f63936,f52632])).
% 40.35/5.44  fof(f52632,plain,(
% 40.35/5.44    ( ! [X114,X113] : (k4_xboole_0(X113,X114) = k4_xboole_0(k5_xboole_0(X113,X114),k4_xboole_0(X114,X113))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f52628,f40])).
% 40.35/5.44  fof(f40,plain,(
% 40.35/5.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 40.35/5.44    inference(forward_demodulation,[],[f34,f20])).
% 40.35/5.44  fof(f20,plain,(
% 40.35/5.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 40.35/5.44    inference(cnf_transformation,[],[f10])).
% 40.35/5.44  fof(f10,axiom,(
% 40.35/5.44    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 40.35/5.44  fof(f34,plain,(
% 40.35/5.44    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 40.35/5.44    inference(definition_unfolding,[],[f21,f24])).
% 40.35/5.44  fof(f24,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 40.35/5.44    inference(cnf_transformation,[],[f12])).
% 40.35/5.44  fof(f12,axiom,(
% 40.35/5.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 40.35/5.44  fof(f21,plain,(
% 40.35/5.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 40.35/5.44    inference(cnf_transformation,[],[f4])).
% 40.35/5.44  fof(f4,axiom,(
% 40.35/5.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 40.35/5.44  fof(f52628,plain,(
% 40.35/5.44    ( ! [X114,X113] : (k5_xboole_0(k4_xboole_0(X113,X114),k1_xboole_0) = k4_xboole_0(k5_xboole_0(X113,X114),k4_xboole_0(X114,X113))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f36890,f52498])).
% 40.35/5.44  fof(f52498,plain,(
% 40.35/5.44    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3))) )),
% 40.35/5.44    inference(superposition,[],[f2450,f33243])).
% 40.35/5.44  fof(f33243,plain,(
% 40.35/5.44    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8))) )),
% 40.35/5.44    inference(superposition,[],[f291,f30935])).
% 40.35/5.44  fof(f30935,plain,(
% 40.35/5.44    ( ! [X76,X77] : (k4_xboole_0(X77,X76) = k5_xboole_0(X76,k5_xboole_0(X77,k4_xboole_0(X76,X77)))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f24814,f30929])).
% 40.35/5.44  fof(f30929,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f30749,f29524])).
% 40.35/5.44  fof(f29524,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),X0))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f29305,f14262])).
% 40.35/5.44  fof(f14262,plain,(
% 40.35/5.44    ( ! [X33,X34,X32] : (k4_xboole_0(k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X34),X32) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X34),k4_xboole_0(X32,X34))) )),
% 40.35/5.44    inference(superposition,[],[f145,f1209])).
% 40.35/5.44  fof(f1209,plain,(
% 40.35/5.44    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(X17,X19)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1132,f114])).
% 40.35/5.44  fof(f114,plain,(
% 40.35/5.44    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 40.35/5.44    inference(forward_demodulation,[],[f111,f40])).
% 40.35/5.44  fof(f111,plain,(
% 40.35/5.44    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 40.35/5.44    inference(superposition,[],[f32,f103])).
% 40.35/5.44  fof(f103,plain,(
% 40.35/5.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f91,f20])).
% 40.35/5.44  fof(f91,plain,(
% 40.35/5.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 40.35/5.44    inference(superposition,[],[f36,f20])).
% 40.35/5.44  fof(f36,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 40.35/5.44    inference(definition_unfolding,[],[f23,f25,f25])).
% 40.35/5.44  fof(f23,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 40.35/5.44    inference(cnf_transformation,[],[f1])).
% 40.35/5.44  fof(f1,axiom,(
% 40.35/5.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 40.35/5.44  fof(f1132,plain,(
% 40.35/5.44    ( ! [X19,X17,X18] : (k4_xboole_0(X17,k4_xboole_0(X17,k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X19))) = k4_xboole_0(k4_xboole_0(X17,k1_xboole_0),X19)) )),
% 40.35/5.44    inference(superposition,[],[f38,f35])).
% 40.35/5.44  fof(f35,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 40.35/5.44    inference(definition_unfolding,[],[f22,f24])).
% 40.35/5.44  fof(f22,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 40.35/5.44    inference(cnf_transformation,[],[f6])).
% 40.35/5.44  fof(f6,axiom,(
% 40.35/5.44    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 40.35/5.44  fof(f38,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 40.35/5.44    inference(definition_unfolding,[],[f30,f25,f25])).
% 40.35/5.44  fof(f30,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 40.35/5.44    inference(cnf_transformation,[],[f9])).
% 40.35/5.44  fof(f9,axiom,(
% 40.35/5.44    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 40.35/5.44  fof(f145,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 40.35/5.44    inference(superposition,[],[f37,f36])).
% 40.35/5.44  fof(f29305,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1),k4_xboole_0(X0,X1)))) )),
% 40.35/5.44    inference(unit_resulting_resolution,[],[f14266,f18138])).
% 40.35/5.44  fof(f18138,plain,(
% 40.35/5.44    ( ! [X12,X11] : (k1_xboole_0 != k4_xboole_0(X11,X12) | k4_xboole_0(X12,k4_xboole_0(X12,X11)) = X11) )),
% 40.35/5.44    inference(forward_demodulation,[],[f18072,f471])).
% 40.35/5.44  fof(f471,plain,(
% 40.35/5.44    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) )),
% 40.35/5.44    inference(superposition,[],[f257,f96])).
% 40.35/5.44  fof(f96,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 40.35/5.44    inference(superposition,[],[f32,f36])).
% 40.35/5.44  fof(f257,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 40.35/5.44    inference(forward_demodulation,[],[f246,f40])).
% 40.35/5.44  fof(f246,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 40.35/5.44    inference(superposition,[],[f200,f118])).
% 40.35/5.44  fof(f118,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f86,f114])).
% 40.35/5.44  fof(f86,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X1,X2),k1_xboole_0)))) )),
% 40.35/5.44    inference(superposition,[],[f72,f29])).
% 40.35/5.44  fof(f29,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 40.35/5.44    inference(cnf_transformation,[],[f11])).
% 40.35/5.44  fof(f11,axiom,(
% 40.35/5.44    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 40.35/5.44  fof(f72,plain,(
% 40.35/5.44    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 40.35/5.44    inference(superposition,[],[f32,f35])).
% 40.35/5.44  fof(f200,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X1,X2)) = X2) )),
% 40.35/5.44    inference(forward_demodulation,[],[f197,f196])).
% 40.35/5.44  fof(f196,plain,(
% 40.35/5.44    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 40.35/5.44    inference(forward_demodulation,[],[f185,f40])).
% 40.35/5.44  fof(f185,plain,(
% 40.35/5.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 40.35/5.44    inference(superposition,[],[f116,f117])).
% 40.35/5.44  fof(f117,plain,(
% 40.35/5.44    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 40.35/5.44    inference(backward_demodulation,[],[f72,f114])).
% 40.35/5.44  fof(f116,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f88,f114])).
% 40.35/5.44  fof(f88,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1))) )),
% 40.35/5.44    inference(superposition,[],[f29,f72])).
% 40.35/5.44  fof(f197,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2)) = X2) )),
% 40.35/5.44    inference(backward_demodulation,[],[f166,f196])).
% 40.35/5.44  fof(f166,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),k5_xboole_0(X1,X2))) )),
% 40.35/5.44    inference(superposition,[],[f29,f121])).
% 40.35/5.44  fof(f121,plain,(
% 40.35/5.44    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X1),X1)) )),
% 40.35/5.44    inference(superposition,[],[f117,f57])).
% 40.35/5.44  fof(f57,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 40.35/5.44    inference(superposition,[],[f29,f40])).
% 40.35/5.44  fof(f18072,plain,(
% 40.35/5.44    ( ! [X12,X11] : (k1_xboole_0 != k4_xboole_0(X11,X12) | k4_xboole_0(X12,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),k4_xboole_0(X11,X12))) )),
% 40.35/5.44    inference(superposition,[],[f725,f145])).
% 40.35/5.44  fof(f725,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,X0) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 40.35/5.44    inference(forward_demodulation,[],[f691,f35])).
% 40.35/5.44  fof(f691,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X1,X0) != k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 40.35/5.44    inference(superposition,[],[f28,f485])).
% 40.35/5.44  fof(f485,plain,(
% 40.35/5.44    ( ! [X8,X9] : (k4_xboole_0(X9,X8) = k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f484,f267])).
% 40.35/5.44  fof(f267,plain,(
% 40.35/5.44    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X6,X5),X6) = X5) )),
% 40.35/5.44    inference(superposition,[],[f257,f257])).
% 40.35/5.44  fof(f484,plain,(
% 40.35/5.44    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8) = k5_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f458,f114])).
% 40.35/5.44  fof(f458,plain,(
% 40.35/5.44    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X8) = k5_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X8,k1_xboole_0))) )),
% 40.35/5.44    inference(superposition,[],[f96,f35])).
% 40.35/5.44  fof(f28,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 40.35/5.44    inference(cnf_transformation,[],[f16])).
% 40.35/5.44  fof(f16,plain,(
% 40.35/5.44    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 40.35/5.44    inference(ennf_transformation,[],[f5])).
% 40.35/5.44  fof(f5,axiom,(
% 40.35/5.44    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 40.35/5.44  fof(f14266,plain,(
% 40.35/5.44    ( ! [X47,X48,X49] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X47,X49),k4_xboole_0(k5_xboole_0(X47,k4_xboole_0(X48,X47)),X49))) )),
% 40.35/5.44    inference(superposition,[],[f357,f1209])).
% 40.35/5.44  fof(f357,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) )),
% 40.35/5.44    inference(superposition,[],[f278,f36])).
% 40.35/5.44  fof(f278,plain,(
% 40.35/5.44    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13)) )),
% 40.35/5.44    inference(backward_demodulation,[],[f151,f265])).
% 40.35/5.44  fof(f265,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X2)),k4_xboole_0(X1,X2)) = X1) )),
% 40.35/5.44    inference(superposition,[],[f257,f32])).
% 40.35/5.44  fof(f151,plain,(
% 40.35/5.44    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k5_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,X14)))) )),
% 40.35/5.44    inference(superposition,[],[f35,f37])).
% 40.35/5.44  fof(f30749,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),k4_xboole_0(k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1),X0))) )),
% 40.35/5.44    inference(unit_resulting_resolution,[],[f30384,f17956])).
% 40.35/5.44  fof(f17956,plain,(
% 40.35/5.44    ( ! [X8,X9] : (k1_xboole_0 != k4_xboole_0(X8,X9) | k4_xboole_0(X8,k4_xboole_0(X8,X9)) = X8) )),
% 40.35/5.44    inference(superposition,[],[f390,f37])).
% 40.35/5.44  fof(f390,plain,(
% 40.35/5.44    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k4_xboole_0(X2,X3)) | k4_xboole_0(X2,X3) = X2) )),
% 40.35/5.44    inference(superposition,[],[f28,f373])).
% 40.35/5.44  fof(f373,plain,(
% 40.35/5.44    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f350,f145])).
% 40.35/5.44  fof(f350,plain,(
% 40.35/5.44    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X2)) )),
% 40.35/5.44    inference(superposition,[],[f278,f36])).
% 40.35/5.44  fof(f30384,plain,(
% 40.35/5.44    ( ! [X101,X100] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X100,k4_xboole_0(X101,X100)),X101),X100)) )),
% 40.35/5.44    inference(superposition,[],[f29824,f728])).
% 40.35/5.44  fof(f728,plain,(
% 40.35/5.44    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X9,X8)) = X8) )),
% 40.35/5.44    inference(forward_demodulation,[],[f727,f114])).
% 40.35/5.44  fof(f727,plain,(
% 40.35/5.44    ( ! [X8,X9] : (k4_xboole_0(X8,k1_xboole_0) = k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X9,X8))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f695,f35])).
% 40.35/5.44  fof(f695,plain,(
% 40.35/5.44    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k5_xboole_0(X8,k4_xboole_0(X9,X8)))) = k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),k4_xboole_0(X9,X8))) )),
% 40.35/5.44    inference(superposition,[],[f36,f485])).
% 40.35/5.44  fof(f29824,plain,(
% 40.35/5.44    ( ! [X19,X17,X18] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X17,X18),k4_xboole_0(X17,k4_xboole_0(X18,X19)))) )),
% 40.35/5.44    inference(superposition,[],[f29400,f1627])).
% 40.35/5.44  fof(f1627,plain,(
% 40.35/5.44    ( ! [X19,X17,X18] : (k4_xboole_0(X18,X17) = k4_xboole_0(k4_xboole_0(X18,X17),k4_xboole_0(X17,X19))) )),
% 40.35/5.44    inference(superposition,[],[f1596,f1336])).
% 40.35/5.44  fof(f1336,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1298,f40])).
% 40.35/5.44  fof(f1298,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 40.35/5.44    inference(superposition,[],[f32,f1149])).
% 40.35/5.44  fof(f1149,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 40.35/5.44    inference(superposition,[],[f38,f278])).
% 40.35/5.44  fof(f1596,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2)) = X0) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1532,f40])).
% 40.35/5.44  fof(f1532,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X2))) )),
% 40.35/5.44    inference(superposition,[],[f32,f1340])).
% 40.35/5.44  fof(f1340,plain,(
% 40.35/5.44    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X10,X9),X11)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1300,f20])).
% 40.35/5.44  fof(f1300,plain,(
% 40.35/5.44    ( ! [X10,X11,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(k4_xboole_0(X10,X9),X11))) = k4_xboole_0(k1_xboole_0,X11)) )),
% 40.35/5.44    inference(superposition,[],[f38,f1149])).
% 40.35/5.44  fof(f29400,plain,(
% 40.35/5.44    ( ! [X12,X10,X11] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X10,X11),X12),k4_xboole_0(X10,X12))) )),
% 40.35/5.44    inference(superposition,[],[f14266,f287])).
% 40.35/5.44  fof(f287,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))) = X1) )),
% 40.35/5.44    inference(superposition,[],[f266,f32])).
% 40.35/5.44  fof(f266,plain,(
% 40.35/5.44    ( ! [X4,X3] : (k5_xboole_0(k5_xboole_0(X3,X4),X4) = X3) )),
% 40.35/5.44    inference(superposition,[],[f257,f200])).
% 40.35/5.44  fof(f24814,plain,(
% 40.35/5.44    ( ! [X76,X77] : (k4_xboole_0(k5_xboole_0(X77,k4_xboole_0(X76,X77)),X76) = k5_xboole_0(X76,k5_xboole_0(X77,k4_xboole_0(X76,X77)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f24685,f114])).
% 40.35/5.44  fof(f24685,plain,(
% 40.35/5.44    ( ! [X76,X77] : (k4_xboole_0(k5_xboole_0(X77,k4_xboole_0(X76,X77)),X76) = k5_xboole_0(k4_xboole_0(X76,k1_xboole_0),k5_xboole_0(X77,k4_xboole_0(X76,X77)))) )),
% 40.35/5.44    inference(superposition,[],[f628,f24321])).
% 40.35/5.44  fof(f24321,plain,(
% 40.35/5.44    ( ! [X78,X79] : (k1_xboole_0 = k4_xboole_0(X79,k5_xboole_0(X78,k4_xboole_0(X79,X78)))) )),
% 40.35/5.44    inference(superposition,[],[f9253,f267])).
% 40.35/5.44  fof(f9253,plain,(
% 40.35/5.44    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X2,k4_xboole_0(k5_xboole_0(X3,X2),X2)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f9252,f273])).
% 40.35/5.44  fof(f273,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 40.35/5.44    inference(superposition,[],[f200,f257])).
% 40.35/5.44  fof(f9252,plain,(
% 40.35/5.44    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(k4_xboole_0(k5_xboole_0(X3,X2),X2),X2))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f9068,f4696])).
% 40.35/5.44  fof(f4696,plain,(
% 40.35/5.44    ( ! [X80,X81,X79] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X79,X80),X81),X80) = k5_xboole_0(X79,k4_xboole_0(X81,k4_xboole_0(X81,k5_xboole_0(X79,X80))))) )),
% 40.35/5.44    inference(superposition,[],[f283,f473])).
% 40.35/5.44  fof(f473,plain,(
% 40.35/5.44    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) )),
% 40.35/5.44    inference(superposition,[],[f267,f96])).
% 40.35/5.44  fof(f283,plain,(
% 40.35/5.44    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X5)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f274,f29])).
% 40.35/5.44  fof(f274,plain,(
% 40.35/5.44    ( ! [X4,X5,X3] : (k5_xboole_0(X4,X5) = k5_xboole_0(X3,k5_xboole_0(k5_xboole_0(X4,X3),X5))) )),
% 40.35/5.44    inference(superposition,[],[f29,f257])).
% 40.35/5.44  fof(f9068,plain,(
% 40.35/5.44    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X3,X2),k5_xboole_0(X3,k4_xboole_0(X2,k4_xboole_0(X2,k5_xboole_0(X3,X2)))))) )),
% 40.35/5.44    inference(superposition,[],[f61,f149])).
% 40.35/5.44  fof(f61,plain,(
% 40.35/5.44    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(X2,X3),k5_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X4,k5_xboole_0(X2,X3)))))) )),
% 40.35/5.44    inference(superposition,[],[f35,f29])).
% 40.35/5.44  fof(f628,plain,(
% 40.35/5.44    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X15)),X15)) )),
% 40.35/5.44    inference(superposition,[],[f267,f157])).
% 40.35/5.44  fof(f157,plain,(
% 40.35/5.44    ( ! [X4,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k5_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f97,f145])).
% 40.35/5.44  fof(f97,plain,(
% 40.35/5.44    ( ! [X4,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,X3)) = k5_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3))))) )),
% 40.35/5.44    inference(superposition,[],[f32,f36])).
% 40.35/5.44  fof(f291,plain,(
% 40.35/5.44    ( ! [X10,X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X8,k5_xboole_0(X9,X10)),X10)) )),
% 40.35/5.44    inference(superposition,[],[f266,f29])).
% 40.35/5.44  fof(f2450,plain,(
% 40.35/5.44    ( ! [X30,X28,X29] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X29,X30),k5_xboole_0(k4_xboole_0(X29,X30),k4_xboole_0(X28,X29)))) )),
% 40.35/5.44    inference(superposition,[],[f35,f1627])).
% 40.35/5.44  fof(f36890,plain,(
% 40.35/5.44    ( ! [X114,X113] : (k4_xboole_0(k5_xboole_0(X113,X114),k4_xboole_0(X114,X113)) = k5_xboole_0(k4_xboole_0(X113,X114),k4_xboole_0(k4_xboole_0(X114,X113),k5_xboole_0(X113,X114)))) )),
% 40.35/5.44    inference(superposition,[],[f33240,f33240])).
% 40.35/5.44  fof(f33240,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))) )),
% 40.35/5.44    inference(superposition,[],[f205,f30935])).
% 40.35/5.44  fof(f205,plain,(
% 40.35/5.44    ( ! [X10,X8,X9] : (k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10))) = X10) )),
% 40.35/5.44    inference(forward_demodulation,[],[f190,f196])).
% 40.35/5.44  fof(f190,plain,(
% 40.35/5.44    ( ! [X10,X8,X9] : (k5_xboole_0(k1_xboole_0,X10) = k5_xboole_0(k5_xboole_0(X8,X9),k5_xboole_0(X8,k5_xboole_0(X9,X10)))) )),
% 40.35/5.44    inference(superposition,[],[f116,f29])).
% 40.35/5.44  fof(f63936,plain,(
% 40.35/5.44    ( ! [X30,X31] : (k4_xboole_0(X30,k5_xboole_0(X30,X31)) = k5_xboole_0(X30,k4_xboole_0(k5_xboole_0(X30,X31),k4_xboole_0(X31,X30)))) )),
% 40.35/5.44    inference(superposition,[],[f96,f63364])).
% 40.35/5.44  fof(f63364,plain,(
% 40.35/5.44    ( ! [X28,X27] : (k4_xboole_0(X28,X27) = k4_xboole_0(k5_xboole_0(X27,X28),X27)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f63161,f40])).
% 40.35/5.44  fof(f63161,plain,(
% 40.35/5.44    ( ! [X28,X27] : (k4_xboole_0(k5_xboole_0(X27,X28),X27) = k5_xboole_0(k4_xboole_0(X28,X27),k1_xboole_0)) )),
% 40.35/5.44    inference(superposition,[],[f55695,f200])).
% 40.35/5.44  fof(f55695,plain,(
% 40.35/5.44    ( ! [X94,X93] : (k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X94,X93),X94),k1_xboole_0)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f55694,f53619])).
% 40.35/5.44  fof(f53619,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k4_xboole_0(X0,k5_xboole_0(X0,X1)))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f53258,f53617])).
% 40.35/5.44  fof(f53617,plain,(
% 40.35/5.44    ( ! [X61,X62] : (k4_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61)) = k4_xboole_0(X61,k5_xboole_0(X61,X62))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f53616,f31906])).
% 40.35/5.44  fof(f31906,plain,(
% 40.35/5.44    ( ! [X15,X16] : (k5_xboole_0(X16,k4_xboole_0(k5_xboole_0(X15,X16),X15)) = k4_xboole_0(X15,k5_xboole_0(X15,X16))) )),
% 40.35/5.44    inference(superposition,[],[f30932,f766])).
% 40.35/5.44  fof(f766,plain,(
% 40.35/5.44    ( ! [X24,X23,X25] : (k5_xboole_0(X24,X23) = k5_xboole_0(k5_xboole_0(X25,X23),k5_xboole_0(X25,X24))) )),
% 40.35/5.44    inference(superposition,[],[f205,f257])).
% 40.35/5.44  fof(f30932,plain,(
% 40.35/5.44    ( ! [X28,X29] : (k4_xboole_0(X29,X28) = k5_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28)) )),
% 40.35/5.44    inference(backward_demodulation,[],[f24789,f30929])).
% 40.35/5.44  fof(f24789,plain,(
% 40.35/5.44    ( ! [X28,X29] : (k4_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28) = k5_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f24665,f114])).
% 40.35/5.44  fof(f24665,plain,(
% 40.35/5.44    ( ! [X28,X29] : (k4_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),X28) = k5_xboole_0(k5_xboole_0(X29,k4_xboole_0(X28,X29)),k4_xboole_0(X28,k1_xboole_0))) )),
% 40.35/5.44    inference(superposition,[],[f96,f24321])).
% 40.35/5.44  fof(f53616,plain,(
% 40.35/5.44    ( ! [X61,X62] : (k4_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61)) = k5_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f53384,f114])).
% 40.35/5.44  fof(f53384,plain,(
% 40.35/5.44    ( ! [X61,X62] : (k4_xboole_0(X62,k4_xboole_0(k5_xboole_0(X61,X62),X61)) = k5_xboole_0(X62,k4_xboole_0(k4_xboole_0(k5_xboole_0(X61,X62),X61),k1_xboole_0))) )),
% 40.35/5.44    inference(superposition,[],[f96,f52719])).
% 40.35/5.44  fof(f52719,plain,(
% 40.35/5.44    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X2,X1),X2),X1)) )),
% 40.35/5.44    inference(superposition,[],[f52504,f273])).
% 40.35/5.44  fof(f52504,plain,(
% 40.35/5.44    ( ! [X15,X16] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X15,X16),X16),X15)) )),
% 40.35/5.44    inference(superposition,[],[f2450,f44791])).
% 40.35/5.44  fof(f44791,plain,(
% 40.35/5.44    ( ! [X41,X42] : (k5_xboole_0(k4_xboole_0(k5_xboole_0(X41,X42),X42),k4_xboole_0(X42,k5_xboole_0(X41,X42))) = X41) )),
% 40.35/5.44    inference(superposition,[],[f257,f24562])).
% 40.35/5.44  fof(f24562,plain,(
% 40.35/5.44    ( ! [X28,X27] : (k5_xboole_0(X27,k4_xboole_0(k5_xboole_0(X27,X28),X28)) = k4_xboole_0(X28,k5_xboole_0(X27,X28))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f24531,f24561])).
% 40.35/5.44  fof(f24561,plain,(
% 40.35/5.44    ( ! [X76,X75] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k4_xboole_0(X76,k5_xboole_0(X75,X76))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f24560,f32])).
% 40.35/5.44  fof(f24560,plain,(
% 40.35/5.44    ( ! [X76,X75] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k5_xboole_0(X76,k4_xboole_0(X76,k4_xboole_0(X76,k5_xboole_0(X75,X76))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f24559,f1064])).
% 40.35/5.44  fof(f1064,plain,(
% 40.35/5.44    ( ! [X12,X13,X11] : (k5_xboole_0(X13,k4_xboole_0(X12,k4_xboole_0(X12,X11))) = k5_xboole_0(X11,k5_xboole_0(X13,k4_xboole_0(X11,X12)))) )),
% 40.35/5.44    inference(superposition,[],[f283,f96])).
% 40.35/5.44  fof(f24559,plain,(
% 40.35/5.44    ( ! [X76,X75] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k5_xboole_0(k5_xboole_0(X75,X76),k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f24390,f114])).
% 40.35/5.44  fof(f24390,plain,(
% 40.35/5.44    ( ! [X76,X75] : (k4_xboole_0(k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)),k5_xboole_0(X75,X76)) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X75,X76),k1_xboole_0),k5_xboole_0(X76,k4_xboole_0(k5_xboole_0(X75,X76),X76)))) )),
% 40.35/5.44    inference(superposition,[],[f628,f9253])).
% 40.35/5.44  fof(f24531,plain,(
% 40.35/5.44    ( ! [X28,X27] : (k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28)) = k5_xboole_0(X27,k4_xboole_0(k5_xboole_0(X27,X28),X28))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f24530,f1008])).
% 40.35/5.44  fof(f1008,plain,(
% 40.35/5.44    ( ! [X24,X23,X25] : (k5_xboole_0(X25,X23) = k5_xboole_0(k5_xboole_0(X24,X23),k5_xboole_0(X25,X24))) )),
% 40.35/5.44    inference(superposition,[],[f269,f257])).
% 40.35/5.44  fof(f269,plain,(
% 40.35/5.44    ( ! [X10,X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(X10,k5_xboole_0(X8,k5_xboole_0(X9,X10)))) )),
% 40.35/5.44    inference(superposition,[],[f257,f29])).
% 40.35/5.44  fof(f24530,plain,(
% 40.35/5.44    ( ! [X28,X27] : (k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28)) = k5_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f24370,f114])).
% 40.35/5.44  fof(f24370,plain,(
% 40.35/5.44    ( ! [X28,X27] : (k4_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k5_xboole_0(X27,X28)) = k5_xboole_0(k5_xboole_0(X28,k4_xboole_0(k5_xboole_0(X27,X28),X28)),k4_xboole_0(k5_xboole_0(X27,X28),k1_xboole_0))) )),
% 40.35/5.44    inference(superposition,[],[f96,f9253])).
% 40.35/5.44  fof(f53258,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X0) = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k5_xboole_0(X0,X1),X0)))) )),
% 40.35/5.44    inference(unit_resulting_resolution,[],[f52719,f18138])).
% 40.35/5.44  fof(f55694,plain,(
% 40.35/5.44    ( ! [X94,X93] : (k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(X93,k4_xboole_0(X94,k5_xboole_0(X94,X93))),k1_xboole_0)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f55693,f53617])).
% 40.35/5.44  fof(f55693,plain,(
% 40.35/5.44    ( ! [X94,X93] : (k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(X93,k4_xboole_0(X93,k4_xboole_0(k5_xboole_0(X94,X93),X94))),k1_xboole_0)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f55692,f34129])).
% 40.35/5.44  fof(f34129,plain,(
% 40.35/5.44    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),X38)) = k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X38,X37)))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f2666,f34122])).
% 40.35/5.44  fof(f34122,plain,(
% 40.35/5.44    ( ! [X57,X58,X56] : (k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,X57)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f34121,f1208])).
% 40.35/5.44  fof(f1208,plain,(
% 40.35/5.44    ( ! [X14,X15,X16] : (k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))) = k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,k4_xboole_0(X15,k4_xboole_0(X14,X16)))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1207,f38])).
% 40.35/5.44  fof(f1207,plain,(
% 40.35/5.44    ( ! [X14,X15,X16] : (k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X16))) = k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1131,f38])).
% 40.35/5.44  fof(f1131,plain,(
% 40.35/5.44    ( ! [X14,X15,X16] : (k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X16))) = k4_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,X15)),X16)) )),
% 40.35/5.44    inference(superposition,[],[f38,f145])).
% 40.35/5.44  fof(f34121,plain,(
% 40.35/5.44    ( ! [X57,X58,X56] : (k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(X56,X57)))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f34108,f2778])).
% 40.35/5.44  fof(f2778,plain,(
% 40.35/5.44    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X12,X10))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2777,f37])).
% 40.35/5.44  fof(f2777,plain,(
% 40.35/5.44    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,X11)) = k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10))))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2559,f2487])).
% 40.35/5.44  fof(f2487,plain,(
% 40.35/5.44    ( ! [X45,X46,X44] : (k4_xboole_0(X45,X46) = k4_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(X44,X45))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2486,f40])).
% 40.35/5.44  fof(f2486,plain,(
% 40.35/5.44    ( ! [X45,X46,X44] : (k4_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(X44,X45)) = k5_xboole_0(k4_xboole_0(X45,X46),k1_xboole_0)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2455,f44])).
% 40.35/5.44  fof(f44,plain,(
% 40.35/5.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f42,f40])).
% 40.35/5.44  fof(f42,plain,(
% 40.35/5.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) )),
% 40.35/5.44    inference(superposition,[],[f35,f20])).
% 40.35/5.44  fof(f2455,plain,(
% 40.35/5.44    ( ! [X45,X46,X44] : (k4_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(X44,X45)) = k5_xboole_0(k4_xboole_0(X45,X46),k4_xboole_0(k4_xboole_0(X44,X45),k4_xboole_0(X44,X45)))) )),
% 40.35/5.44    inference(superposition,[],[f96,f1627])).
% 40.35/5.44  fof(f2559,plain,(
% 40.35/5.44    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X10)))))) = k4_xboole_0(k4_xboole_0(X10,k4_xboole_0(X10,X11)),k4_xboole_0(X10,X10))) )),
% 40.35/5.44    inference(superposition,[],[f41,f1375])).
% 40.35/5.44  fof(f1375,plain,(
% 40.35/5.44    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k4_xboole_0(X22,k4_xboole_0(X22,k4_xboole_0(X23,X24)))) = X24) )),
% 40.35/5.44    inference(superposition,[],[f1336,f38])).
% 40.35/5.44  fof(f41,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f39,f38])).
% 40.35/5.44  fof(f39,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 40.35/5.44    inference(definition_unfolding,[],[f31,f25,f25,f25,f25])).
% 40.35/5.44  fof(f31,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 40.35/5.44    inference(cnf_transformation,[],[f3])).
% 40.35/5.44  fof(f3,axiom,(
% 40.35/5.44    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 40.35/5.44  fof(f34108,plain,(
% 40.35/5.44    ( ! [X57,X58,X56] : (k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58))))))) )),
% 40.35/5.44    inference(backward_demodulation,[],[f30151,f34051])).
% 40.35/5.44  fof(f34051,plain,(
% 40.35/5.44    ( ! [X35,X33,X34] : (k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,X35))))) = k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X35)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f33700,f32])).
% 40.35/5.44  fof(f33700,plain,(
% 40.35/5.44    ( ! [X35,X33,X34] : (k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,X35))))) = k5_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X33,k4_xboole_0(X34,k4_xboole_0(X34,X35)))))) )),
% 40.35/5.44    inference(superposition,[],[f32,f2582])).
% 40.35/5.44  fof(f2582,plain,(
% 40.35/5.44    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5))))))) )),
% 40.35/5.44    inference(superposition,[],[f41,f38])).
% 40.35/5.44  fof(f30151,plain,(
% 40.35/5.44    ( ! [X57,X58,X56] : (k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)) = k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58))))))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f29925,f114])).
% 40.35/5.44  fof(f29925,plain,(
% 40.35/5.44    ( ! [X57,X58,X56] : (k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(X56,k4_xboole_0(X56,k4_xboole_0(X58,k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)))))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X56,X58)),k1_xboole_0)) )),
% 40.35/5.44    inference(superposition,[],[f1242,f29400])).
% 40.35/5.44  fof(f1242,plain,(
% 40.35/5.44    ( ! [X17,X18,X16] : (k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) = k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,X18))))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1155,f38])).
% 40.35/5.44  fof(f1155,plain,(
% 40.35/5.44    ( ! [X17,X18,X16] : (k4_xboole_0(X18,k4_xboole_0(X18,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) = k4_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X17,k4_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),X18))))) )),
% 40.35/5.44    inference(superposition,[],[f38,f36])).
% 40.35/5.44  fof(f2666,plain,(
% 40.35/5.44    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,X38)) = k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),X38))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2665,f1216])).
% 40.35/5.44  fof(f1216,plain,(
% 40.35/5.44    ( ! [X26,X27,X25] : (k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,X27))) = k4_xboole_0(k4_xboole_0(X25,X26),X27)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1135,f114])).
% 40.35/5.44  fof(f1135,plain,(
% 40.35/5.44    ( ! [X26,X27,X25] : (k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(k4_xboole_0(X25,X26),k4_xboole_0(X25,X27))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X25,X26),k1_xboole_0),X27)) )),
% 40.35/5.44    inference(superposition,[],[f38,f373])).
% 40.35/5.44  fof(f2665,plain,(
% 40.35/5.44    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),X38))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2664,f114])).
% 40.35/5.44  fof(f2664,plain,(
% 40.35/5.44    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(k4_xboole_0(X36,X37),X38))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2663,f1204])).
% 40.35/5.44  fof(f1204,plain,(
% 40.35/5.44    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1203,f145])).
% 40.35/5.44  fof(f1203,plain,(
% 40.35/5.44    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1127,f149])).
% 40.35/5.44  fof(f1127,plain,(
% 40.35/5.44    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k5_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) )),
% 40.35/5.44    inference(superposition,[],[f38,f157])).
% 40.35/5.44  fof(f2663,plain,(
% 40.35/5.44    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(k4_xboole_0(X36,X37),X38))))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2662,f38])).
% 40.35/5.44  fof(f2662,plain,(
% 40.35/5.44    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X36,X37))),X38))) )),
% 40.35/5.44    inference(forward_demodulation,[],[f2514,f1229])).
% 40.35/5.44  fof(f1229,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f1142,f149])).
% 40.35/5.44  fof(f1142,plain,(
% 40.35/5.44    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 40.35/5.44    inference(superposition,[],[f38,f157])).
% 40.35/5.44  fof(f2514,plain,(
% 40.35/5.44    ( ! [X37,X38,X36] : (k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,k4_xboole_0(X36,X38)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X36,X37),k1_xboole_0),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(k4_xboole_0(X36,X37),k4_xboole_0(X36,X38))))) )),
% 40.35/5.44    inference(superposition,[],[f41,f373])).
% 40.35/5.44  fof(f55692,plain,(
% 40.35/5.44    ( ! [X94,X93] : (k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X93,X94),k4_xboole_0(k4_xboole_0(X93,X94),k5_xboole_0(X94,X93))),k1_xboole_0)) )),
% 40.35/5.44    inference(forward_demodulation,[],[f55467,f36])).
% 40.35/5.44  fof(f55467,plain,(
% 40.35/5.44    ( ! [X94,X93] : (k4_xboole_0(X93,X94) = k5_xboole_0(k4_xboole_0(k5_xboole_0(X94,X93),k4_xboole_0(k5_xboole_0(X94,X93),k4_xboole_0(X93,X94))),k1_xboole_0)) )),
% 40.35/5.44    inference(superposition,[],[f471,f52498])).
% 40.35/5.44  fof(f64025,plain,(
% 40.35/5.44    ( ! [X287,X286] : (k5_xboole_0(X286,X287) = k4_xboole_0(k5_xboole_0(X286,k4_xboole_0(X287,X286)),k4_xboole_0(X286,k5_xboole_0(X286,X287)))) )),
% 40.35/5.44    inference(superposition,[],[f30931,f63364])).
% 40.35/5.44  fof(f30931,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X1) )),
% 40.35/5.44    inference(backward_demodulation,[],[f24610,f30929])).
% 40.35/5.44  fof(f24610,plain,(
% 40.35/5.44    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) = X1) )),
% 40.35/5.44    inference(unit_resulting_resolution,[],[f24321,f18138])).
% 40.35/5.44  fof(f407,plain,(
% 40.35/5.44    k4_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))),
% 40.35/5.44    inference(unit_resulting_resolution,[],[f33,f28])).
% 40.35/5.44  fof(f33,plain,(
% 40.35/5.44    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 40.35/5.44    inference(definition_unfolding,[],[f19,f24,f25])).
% 40.35/5.44  fof(f19,plain,(
% 40.35/5.44    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 40.35/5.44    inference(cnf_transformation,[],[f18])).
% 40.35/5.44  fof(f18,plain,(
% 40.35/5.44    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 40.35/5.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f17])).
% 40.35/5.44  fof(f17,plain,(
% 40.35/5.44    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 40.35/5.44    introduced(choice_axiom,[])).
% 40.35/5.44  fof(f15,plain,(
% 40.35/5.44    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 40.35/5.44    inference(ennf_transformation,[],[f14])).
% 40.35/5.44  fof(f14,negated_conjecture,(
% 40.35/5.44    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 40.35/5.44    inference(negated_conjecture,[],[f13])).
% 40.35/5.44  fof(f13,conjecture,(
% 40.35/5.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 40.35/5.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 40.35/5.44  % SZS output end Proof for theBenchmark
% 40.35/5.44  % (13057)------------------------------
% 40.35/5.44  % (13057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 40.35/5.44  % (13057)Termination reason: Refutation
% 40.35/5.44  
% 40.35/5.44  % (13057)Memory used [KB]: 124347
% 40.35/5.44  % (13057)Time elapsed: 4.856 s
% 40.35/5.44  % (13057)------------------------------
% 40.35/5.44  % (13057)------------------------------
% 40.54/5.45  % (13019)Success in time 5.081 s
%------------------------------------------------------------------------------
