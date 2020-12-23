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
% DateTime   : Thu Dec  3 12:30:57 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  126 (1657 expanded)
%              Number of leaves         :   12 ( 494 expanded)
%              Depth                    :   35
%              Number of atoms          :  143 (2286 expanded)
%              Number of equality atoms :  127 (1799 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3425,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3424,f21])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f3424,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f608,f3423])).

fof(f3423,plain,(
    sK1 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f3422,f3353])).

fof(f3353,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f2336,f3199])).

fof(f3199,plain,(
    sK0 = sK3 ),
    inference(backward_demodulation,[],[f1266,f3198])).

fof(f3198,plain,(
    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f3189,f2281])).

fof(f2281,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f2220,f979])).

fof(f979,plain,(
    ! [X70] : sK2 = k4_xboole_0(sK2,k4_xboole_0(sK0,X70)) ),
    inference(forward_demodulation,[],[f860,f946])).

fof(f946,plain,(
    ! [X17,X16] : k2_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = X16 ),
    inference(forward_demodulation,[],[f945,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f945,plain,(
    ! [X17,X16] : k4_xboole_0(X16,k1_xboole_0) = k2_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17))) ),
    inference(forward_demodulation,[],[f836,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f836,plain,(
    ! [X17,X16] : k4_xboole_0(X16,k4_xboole_0(k1_xboole_0,X17)) = k2_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17))) ),
    inference(superposition,[],[f35,f23])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f860,plain,(
    ! [X70] : k4_xboole_0(sK2,k4_xboole_0(sK0,X70)) = k2_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X70))) ),
    inference(superposition,[],[f35,f608])).

fof(f2220,plain,(
    ! [X43] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK2,X43)) ),
    inference(superposition,[],[f1631,f630])).

fof(f630,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f31,f608])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1631,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = X2 ),
    inference(backward_demodulation,[],[f1014,f1546])).

fof(f1546,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f946,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f26])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1014,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f1013,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1013,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),X2) ),
    inference(forward_demodulation,[],[f880,f23])).

fof(f880,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f3189,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f28,f3116])).

fof(f3116,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f3115,f25])).

fof(f3115,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f3114,f25])).

fof(f3114,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f3104,f2907])).

fof(f2907,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f2836,f1666])).

fof(f1666,plain,(
    ! [X4,X5] : k2_xboole_0(X4,X5) = k2_xboole_0(X4,k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f30,f1581])).

fof(f1581,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f1485,f23])).

fof(f1485,plain,(
    ! [X0] : k2_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f946,f54])).

fof(f54,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(superposition,[],[f24,f47])).

fof(f47,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f45,f23])).

fof(f45,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f28,f23])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f2836,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(X7,k2_xboole_0(X6,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f74,f1581])).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f30,f25])).

fof(f3104,plain,(
    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f93,f3071])).

fof(f3071,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f3070,f23])).

fof(f3070,plain,(
    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3069,f723])).

fof(f723,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f684,f39])).

fof(f39,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f25])).

fof(f684,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f633,f25])).

fof(f633,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f31,f616])).

fof(f616,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f564,f23])).

fof(f564,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f33,f73])).

fof(f73,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f34,f20])).

fof(f20,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f26])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f3069,plain,(
    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(sK3,sK0)) ),
    inference(forward_demodulation,[],[f3062,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f28,f25])).

fof(f3062,plain,(
    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(k2_xboole_0(sK0,sK3),sK0)) ),
    inference(superposition,[],[f33,f3055])).

fof(f3055,plain,(
    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),sK1) ),
    inference(forward_demodulation,[],[f3054,f2971])).

fof(f2971,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f2809,f2336])).

fof(f2809,plain,(
    ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK3)) ),
    inference(forward_demodulation,[],[f2808,f1546])).

fof(f2808,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK3)) = k2_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f2807,f25])).

fof(f2807,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK0,X0),sK0) ),
    inference(forward_demodulation,[],[f2802,f23])).

fof(f2802,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f35,f2791])).

fof(f2791,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f2770,f24])).

fof(f2770,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f2314,f18])).

fof(f2314,plain,(
    ! [X2] : k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(sK2,X2)) ),
    inference(superposition,[],[f31,f2281])).

fof(f3054,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK3),sK1) ),
    inference(forward_demodulation,[],[f3040,f28])).

fof(f3040,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK3),sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f43,f2834])).

fof(f2834,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(superposition,[],[f74,f1592])).

fof(f1592,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f1499,f1266])).

fof(f1499,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(superposition,[],[f946,f1165])).

fof(f1165,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f42,f1161])).

fof(f1161,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f1149,f23])).

fof(f1149,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f1068,f723])).

fof(f1068,plain,(
    ! [X70] : k4_xboole_0(sK2,X70) = k4_xboole_0(sK2,k4_xboole_0(X70,sK0)) ),
    inference(forward_demodulation,[],[f1067,f49])).

fof(f49,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f47,f25])).

fof(f1067,plain,(
    ! [X70] : k4_xboole_0(sK2,k4_xboole_0(X70,sK0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X70)) ),
    inference(forward_demodulation,[],[f1066,f25])).

fof(f1066,plain,(
    ! [X70] : k4_xboole_0(sK2,k4_xboole_0(X70,sK0)) = k2_xboole_0(k4_xboole_0(sK2,X70),k1_xboole_0) ),
    inference(forward_demodulation,[],[f908,f54])).

fof(f908,plain,(
    ! [X70] : k4_xboole_0(sK2,k4_xboole_0(X70,sK0)) = k2_xboole_0(k4_xboole_0(sK2,X70),k4_xboole_0(sK2,sK2)) ),
    inference(superposition,[],[f35,f608])).

fof(f42,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f28,f18])).

fof(f93,plain,(
    ! [X0] : k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f92,f25])).

fof(f92,plain,(
    ! [X14] : k2_xboole_0(sK2,k2_xboole_0(sK3,X14)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X14)) ),
    inference(forward_demodulation,[],[f79,f30])).

fof(f79,plain,(
    ! [X14] : k2_xboole_0(sK2,k2_xboole_0(sK3,X14)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X14) ),
    inference(superposition,[],[f30,f18])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f1266,plain,(
    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f63,f1260])).

fof(f1260,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f1247,f23])).

fof(f1247,plain,(
    k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f1101,f638])).

fof(f638,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f630,f36])).

fof(f36,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f24,f18])).

fof(f1101,plain,(
    ! [X108] : k4_xboole_0(sK3,X108) = k4_xboole_0(sK3,k4_xboole_0(X108,sK1)) ),
    inference(forward_demodulation,[],[f1100,f49])).

fof(f1100,plain,(
    ! [X108] : k4_xboole_0(sK3,k4_xboole_0(X108,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,X108)) ),
    inference(forward_demodulation,[],[f1099,f25])).

fof(f1099,plain,(
    ! [X108] : k4_xboole_0(sK3,k4_xboole_0(X108,sK1)) = k2_xboole_0(k4_xboole_0(sK3,X108),k1_xboole_0) ),
    inference(forward_demodulation,[],[f925,f54])).

fof(f925,plain,(
    ! [X108] : k4_xboole_0(sK3,k4_xboole_0(X108,sK1)) = k2_xboole_0(k4_xboole_0(sK3,X108),k4_xboole_0(sK3,sK3)) ),
    inference(superposition,[],[f35,f616])).

fof(f63,plain,(
    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f43,f18])).

fof(f2336,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f2238,f1009])).

fof(f1009,plain,(
    ! [X108] : sK3 = k4_xboole_0(sK3,k4_xboole_0(sK1,X108)) ),
    inference(forward_demodulation,[],[f877,f946])).

fof(f877,plain,(
    ! [X108] : k4_xboole_0(sK3,k4_xboole_0(sK1,X108)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X108))) ),
    inference(superposition,[],[f35,f616])).

fof(f2238,plain,(
    ! [X67] : sK1 = k4_xboole_0(sK1,k4_xboole_0(sK3,X67)) ),
    inference(superposition,[],[f1631,f633])).

fof(f3422,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f3192,f43])).

fof(f3192,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f43,f3116])).

fof(f608,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f563,f23])).

fof(f563,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f33,f72])).

fof(f72,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.10  % Command    : run_vampire %s %d
% 0.09/0.30  % Computer   : n022.cluster.edu
% 0.09/0.30  % Model      : x86_64 x86_64
% 0.09/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.30  % Memory     : 8042.1875MB
% 0.09/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.30  % CPULimit   : 60
% 0.09/0.30  % WCLimit    : 600
% 0.09/0.30  % DateTime   : Tue Dec  1 17:34:10 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.15/0.40  % (5700)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.15/0.42  % (5701)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.15/0.43  % (5720)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.15/0.43  % (5703)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.15/0.43  % (5711)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.15/0.43  % (5697)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.15/0.43  % (5711)Refutation not found, incomplete strategy% (5711)------------------------------
% 0.15/0.43  % (5711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.43  % (5711)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.43  
% 0.15/0.43  % (5711)Memory used [KB]: 6140
% 0.15/0.43  % (5711)Time elapsed: 0.003 s
% 0.15/0.43  % (5711)------------------------------
% 0.15/0.43  % (5711)------------------------------
% 0.15/0.44  % (5718)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.15/0.44  % (5714)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.15/0.44  % (5721)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.15/0.45  % (5709)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.15/0.45  % (5726)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.15/0.45  % (5710)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.15/0.45  % (5702)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.15/0.45  % (5723)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.15/0.46  % (5719)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.15/0.46  % (5695)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.15/0.46  % (5712)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.15/0.47  % (5696)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.15/0.47  % (5699)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.15/0.48  % (5698)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.15/0.48  % (5717)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.15/0.48  % (5705)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.15/0.48  % (5715)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.15/0.48  % (5704)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.15/0.48  % (5707)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.15/0.49  % (5706)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.15/0.49  % (5713)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.15/0.49  % (5713)Refutation not found, incomplete strategy% (5713)------------------------------
% 0.15/0.49  % (5713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.49  % (5713)Termination reason: Refutation not found, incomplete strategy
% 0.15/0.49  
% 0.15/0.49  % (5713)Memory used [KB]: 10618
% 0.15/0.49  % (5713)Time elapsed: 0.131 s
% 0.15/0.49  % (5713)------------------------------
% 0.15/0.49  % (5713)------------------------------
% 0.15/0.49  % (5722)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.15/0.49  % (5724)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.15/0.49  % (5725)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.67/0.58  % (5793)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.67/0.62  % (5701)Refutation found. Thanks to Tanya!
% 1.67/0.62  % SZS status Theorem for theBenchmark
% 2.37/0.63  % SZS output start Proof for theBenchmark
% 2.37/0.63  fof(f3425,plain,(
% 2.37/0.63    $false),
% 2.37/0.63    inference(subsumption_resolution,[],[f3424,f21])).
% 2.37/0.63  fof(f21,plain,(
% 2.37/0.63    sK1 != sK2),
% 2.37/0.63    inference(cnf_transformation,[],[f16])).
% 2.37/0.63  fof(f16,plain,(
% 2.37/0.63    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.37/0.63    inference(flattening,[],[f15])).
% 2.37/0.63  fof(f15,plain,(
% 2.37/0.63    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.37/0.63    inference(ennf_transformation,[],[f13])).
% 2.37/0.63  fof(f13,negated_conjecture,(
% 2.37/0.63    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.37/0.63    inference(negated_conjecture,[],[f12])).
% 2.37/0.63  fof(f12,conjecture,(
% 2.37/0.63    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.37/0.63  fof(f3424,plain,(
% 2.37/0.63    sK1 = sK2),
% 2.37/0.63    inference(backward_demodulation,[],[f608,f3423])).
% 2.37/0.63  fof(f3423,plain,(
% 2.37/0.63    sK1 = k4_xboole_0(sK2,sK0)),
% 2.37/0.63    inference(forward_demodulation,[],[f3422,f3353])).
% 2.37/0.63  fof(f3353,plain,(
% 2.37/0.63    sK1 = k4_xboole_0(sK1,sK0)),
% 2.37/0.63    inference(backward_demodulation,[],[f2336,f3199])).
% 2.37/0.63  fof(f3199,plain,(
% 2.37/0.63    sK0 = sK3),
% 2.37/0.63    inference(backward_demodulation,[],[f1266,f3198])).
% 2.37/0.63  fof(f3198,plain,(
% 2.37/0.63    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 2.37/0.63    inference(forward_demodulation,[],[f3189,f2281])).
% 2.37/0.63  fof(f2281,plain,(
% 2.37/0.63    sK0 = k4_xboole_0(sK0,sK2)),
% 2.37/0.63    inference(superposition,[],[f2220,f979])).
% 2.37/0.63  fof(f979,plain,(
% 2.37/0.63    ( ! [X70] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(sK0,X70))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f860,f946])).
% 2.37/0.63  fof(f946,plain,(
% 2.37/0.63    ( ! [X17,X16] : (k2_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17))) = X16) )),
% 2.37/0.63    inference(forward_demodulation,[],[f945,f23])).
% 2.37/0.63  fof(f23,plain,(
% 2.37/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.37/0.63    inference(cnf_transformation,[],[f3])).
% 2.37/0.63  fof(f3,axiom,(
% 2.37/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.37/0.63  fof(f945,plain,(
% 2.37/0.63    ( ! [X17,X16] : (k4_xboole_0(X16,k1_xboole_0) = k2_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f836,f22])).
% 2.37/0.63  fof(f22,plain,(
% 2.37/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.37/0.63    inference(cnf_transformation,[],[f9])).
% 2.37/0.63  fof(f9,axiom,(
% 2.37/0.63    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 2.37/0.63  fof(f836,plain,(
% 2.37/0.63    ( ! [X17,X16] : (k4_xboole_0(X16,k4_xboole_0(k1_xboole_0,X17)) = k2_xboole_0(X16,k4_xboole_0(X16,k4_xboole_0(X16,X17)))) )),
% 2.37/0.63    inference(superposition,[],[f35,f23])).
% 2.37/0.63  fof(f35,plain,(
% 2.37/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.37/0.63    inference(definition_unfolding,[],[f32,f26])).
% 2.37/0.63  fof(f26,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.37/0.63    inference(cnf_transformation,[],[f8])).
% 2.37/0.63  fof(f8,axiom,(
% 2.37/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.37/0.63  fof(f32,plain,(
% 2.37/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.37/0.63    inference(cnf_transformation,[],[f11])).
% 2.37/0.63  fof(f11,axiom,(
% 2.37/0.63    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.37/0.63  fof(f860,plain,(
% 2.37/0.63    ( ! [X70] : (k4_xboole_0(sK2,k4_xboole_0(sK0,X70)) = k2_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,X70)))) )),
% 2.37/0.63    inference(superposition,[],[f35,f608])).
% 2.37/0.63  fof(f2220,plain,(
% 2.37/0.63    ( ! [X43] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK2,X43))) )),
% 2.37/0.63    inference(superposition,[],[f1631,f630])).
% 2.37/0.63  fof(f630,plain,(
% 2.37/0.63    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 2.37/0.63    inference(superposition,[],[f31,f608])).
% 2.37/0.63  fof(f31,plain,(
% 2.37/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.37/0.63    inference(cnf_transformation,[],[f5])).
% 2.37/0.63  fof(f5,axiom,(
% 2.37/0.63    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.37/0.63  fof(f1631,plain,(
% 2.37/0.63    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = X2) )),
% 2.37/0.63    inference(backward_demodulation,[],[f1014,f1546])).
% 2.37/0.63  fof(f1546,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.37/0.63    inference(superposition,[],[f946,f33])).
% 2.37/0.63  fof(f33,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.37/0.63    inference(definition_unfolding,[],[f27,f26])).
% 2.37/0.63  fof(f27,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.37/0.63    inference(cnf_transformation,[],[f7])).
% 2.37/0.63  fof(f7,axiom,(
% 2.37/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.37/0.63  fof(f1014,plain,(
% 2.37/0.63    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k4_xboole_0(X2,X4))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f1013,f25])).
% 2.37/0.63  fof(f25,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.37/0.63    inference(cnf_transformation,[],[f1])).
% 2.37/0.63  fof(f1,axiom,(
% 2.37/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.37/0.63  fof(f1013,plain,(
% 2.37/0.63    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),X2)) )),
% 2.37/0.63    inference(forward_demodulation,[],[f880,f23])).
% 2.37/0.63  fof(f880,plain,(
% 2.37/0.63    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,k1_xboole_0))) )),
% 2.37/0.63    inference(superposition,[],[f35,f24])).
% 2.37/0.63  fof(f24,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.37/0.63    inference(cnf_transformation,[],[f6])).
% 2.37/0.63  fof(f6,axiom,(
% 2.37/0.63    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.37/0.63  fof(f3189,plain,(
% 2.37/0.63    k4_xboole_0(k2_xboole_0(sK0,sK1),sK2) = k4_xboole_0(sK0,sK2)),
% 2.37/0.63    inference(superposition,[],[f28,f3116])).
% 2.37/0.63  fof(f3116,plain,(
% 2.37/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 2.37/0.63    inference(forward_demodulation,[],[f3115,f25])).
% 2.37/0.63  fof(f3115,plain,(
% 2.37/0.63    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK0,sK2)),
% 2.37/0.63    inference(forward_demodulation,[],[f3114,f25])).
% 2.37/0.63  fof(f3114,plain,(
% 2.37/0.63    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK2,sK0)),
% 2.37/0.63    inference(forward_demodulation,[],[f3104,f2907])).
% 2.37/0.63  fof(f2907,plain,(
% 2.37/0.63    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(X7,k2_xboole_0(X6,X7))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f2836,f1666])).
% 2.37/0.63  fof(f1666,plain,(
% 2.37/0.63    ( ! [X4,X5] : (k2_xboole_0(X4,X5) = k2_xboole_0(X4,k2_xboole_0(X4,X5))) )),
% 2.37/0.63    inference(superposition,[],[f30,f1581])).
% 2.37/0.63  fof(f1581,plain,(
% 2.37/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.37/0.63    inference(forward_demodulation,[],[f1485,f23])).
% 2.37/0.63  fof(f1485,plain,(
% 2.37/0.63    ( ! [X0] : (k2_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.37/0.63    inference(superposition,[],[f946,f54])).
% 2.37/0.63  fof(f54,plain,(
% 2.37/0.63    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 2.37/0.63    inference(superposition,[],[f24,f47])).
% 2.37/0.63  fof(f47,plain,(
% 2.37/0.63    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.37/0.63    inference(forward_demodulation,[],[f45,f23])).
% 2.37/0.63  fof(f45,plain,(
% 2.37/0.63    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 2.37/0.63    inference(superposition,[],[f28,f23])).
% 2.37/0.63  fof(f30,plain,(
% 2.37/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.37/0.63    inference(cnf_transformation,[],[f10])).
% 2.37/0.63  fof(f10,axiom,(
% 2.37/0.63    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.37/0.63  fof(f2836,plain,(
% 2.37/0.63    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(X7,k2_xboole_0(X6,k2_xboole_0(X6,X7)))) )),
% 2.37/0.63    inference(superposition,[],[f74,f1581])).
% 2.37/0.63  fof(f74,plain,(
% 2.37/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X0),X2)) )),
% 2.37/0.63    inference(superposition,[],[f30,f25])).
% 2.37/0.63  fof(f3104,plain,(
% 2.37/0.63    k2_xboole_0(sK2,sK0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 2.37/0.63    inference(superposition,[],[f93,f3071])).
% 2.37/0.63  fof(f3071,plain,(
% 2.37/0.63    sK0 = k2_xboole_0(sK0,sK3)),
% 2.37/0.63    inference(superposition,[],[f3070,f23])).
% 2.37/0.63  fof(f3070,plain,(
% 2.37/0.63    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),k1_xboole_0)),
% 2.37/0.63    inference(forward_demodulation,[],[f3069,f723])).
% 2.37/0.63  fof(f723,plain,(
% 2.37/0.63    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 2.37/0.63    inference(superposition,[],[f684,f39])).
% 2.37/0.63  fof(f39,plain,(
% 2.37/0.63    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.37/0.63    inference(superposition,[],[f37,f18])).
% 2.37/0.63  fof(f18,plain,(
% 2.37/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.37/0.63    inference(cnf_transformation,[],[f16])).
% 2.37/0.63  fof(f37,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 2.37/0.63    inference(superposition,[],[f24,f25])).
% 2.37/0.63  fof(f684,plain,(
% 2.37/0.63    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 2.37/0.63    inference(superposition,[],[f633,f25])).
% 2.37/0.63  fof(f633,plain,(
% 2.37/0.63    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 2.37/0.63    inference(superposition,[],[f31,f616])).
% 2.37/0.63  fof(f616,plain,(
% 2.37/0.63    sK3 = k4_xboole_0(sK3,sK1)),
% 2.37/0.63    inference(forward_demodulation,[],[f564,f23])).
% 2.37/0.63  fof(f564,plain,(
% 2.37/0.63    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.37/0.63    inference(superposition,[],[f33,f73])).
% 2.37/0.63  fof(f73,plain,(
% 2.37/0.63    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.37/0.63    inference(resolution,[],[f34,f20])).
% 2.37/0.63  fof(f20,plain,(
% 2.37/0.63    r1_xboole_0(sK3,sK1)),
% 2.37/0.63    inference(cnf_transformation,[],[f16])).
% 2.37/0.63  fof(f34,plain,(
% 2.37/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.37/0.63    inference(definition_unfolding,[],[f29,f26])).
% 2.37/0.63  fof(f29,plain,(
% 2.37/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.37/0.63    inference(cnf_transformation,[],[f17])).
% 2.37/0.63  fof(f17,plain,(
% 2.37/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 2.37/0.63    inference(ennf_transformation,[],[f14])).
% 2.37/0.63  fof(f14,plain,(
% 2.37/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.37/0.63    inference(unused_predicate_definition_removal,[],[f2])).
% 2.37/0.63  fof(f2,axiom,(
% 2.37/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.37/0.63  fof(f3069,plain,(
% 2.37/0.63    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(sK3,sK0))),
% 2.37/0.63    inference(forward_demodulation,[],[f3062,f43])).
% 2.37/0.63  fof(f43,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 2.37/0.63    inference(superposition,[],[f28,f25])).
% 2.37/0.63  fof(f3062,plain,(
% 2.37/0.63    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),k4_xboole_0(k2_xboole_0(sK0,sK3),sK0))),
% 2.37/0.63    inference(superposition,[],[f33,f3055])).
% 2.37/0.63  fof(f3055,plain,(
% 2.37/0.63    sK0 = k4_xboole_0(k2_xboole_0(sK0,sK3),sK1)),
% 2.37/0.63    inference(forward_demodulation,[],[f3054,f2971])).
% 2.37/0.63  fof(f2971,plain,(
% 2.37/0.63    sK0 = k4_xboole_0(sK0,sK1)),
% 2.37/0.63    inference(superposition,[],[f2809,f2336])).
% 2.37/0.63  fof(f2809,plain,(
% 2.37/0.63    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X0,sK3))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f2808,f1546])).
% 2.37/0.63  fof(f2808,plain,(
% 2.37/0.63    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK3)) = k2_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f2807,f25])).
% 2.37/0.63  fof(f2807,plain,(
% 2.37/0.63    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK0,X0),sK0)) )),
% 2.37/0.63    inference(forward_demodulation,[],[f2802,f23])).
% 2.37/0.63  fof(f2802,plain,(
% 2.37/0.63    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK3)) = k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k1_xboole_0))) )),
% 2.37/0.63    inference(superposition,[],[f35,f2791])).
% 2.37/0.63  fof(f2791,plain,(
% 2.37/0.63    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 2.37/0.63    inference(forward_demodulation,[],[f2770,f24])).
% 2.37/0.63  fof(f2770,plain,(
% 2.37/0.63    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 2.37/0.63    inference(superposition,[],[f2314,f18])).
% 2.37/0.63  fof(f2314,plain,(
% 2.37/0.63    ( ! [X2] : (k4_xboole_0(sK0,X2) = k4_xboole_0(sK0,k2_xboole_0(sK2,X2))) )),
% 2.37/0.63    inference(superposition,[],[f31,f2281])).
% 2.37/0.63  fof(f3054,plain,(
% 2.37/0.63    k4_xboole_0(sK0,sK1) = k4_xboole_0(k2_xboole_0(sK0,sK3),sK1)),
% 2.37/0.63    inference(forward_demodulation,[],[f3040,f28])).
% 2.37/0.63  fof(f3040,plain,(
% 2.37/0.63    k4_xboole_0(k2_xboole_0(sK0,sK3),sK1) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 2.37/0.63    inference(superposition,[],[f43,f2834])).
% 2.37/0.63  fof(f2834,plain,(
% 2.37/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3))),
% 2.37/0.63    inference(superposition,[],[f74,f1592])).
% 2.37/0.63  fof(f1592,plain,(
% 2.37/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.37/0.63    inference(forward_demodulation,[],[f1499,f1266])).
% 2.37/0.63  fof(f1499,plain,(
% 2.37/0.63    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 2.37/0.63    inference(superposition,[],[f946,f1165])).
% 2.37/0.63  fof(f1165,plain,(
% 2.37/0.63    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.37/0.63    inference(backward_demodulation,[],[f42,f1161])).
% 2.37/0.63  fof(f1161,plain,(
% 2.37/0.63    sK2 = k4_xboole_0(sK2,sK3)),
% 2.37/0.63    inference(forward_demodulation,[],[f1149,f23])).
% 2.37/0.63  fof(f1149,plain,(
% 2.37/0.63    k4_xboole_0(sK2,sK3) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.37/0.63    inference(superposition,[],[f1068,f723])).
% 2.37/0.63  fof(f1068,plain,(
% 2.37/0.63    ( ! [X70] : (k4_xboole_0(sK2,X70) = k4_xboole_0(sK2,k4_xboole_0(X70,sK0))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f1067,f49])).
% 2.37/0.63  fof(f49,plain,(
% 2.37/0.63    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.37/0.63    inference(superposition,[],[f47,f25])).
% 2.37/0.63  fof(f1067,plain,(
% 2.37/0.63    ( ! [X70] : (k4_xboole_0(sK2,k4_xboole_0(X70,sK0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X70))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f1066,f25])).
% 2.37/0.63  fof(f1066,plain,(
% 2.37/0.63    ( ! [X70] : (k4_xboole_0(sK2,k4_xboole_0(X70,sK0)) = k2_xboole_0(k4_xboole_0(sK2,X70),k1_xboole_0)) )),
% 2.37/0.63    inference(forward_demodulation,[],[f908,f54])).
% 2.37/0.63  fof(f908,plain,(
% 2.37/0.63    ( ! [X70] : (k4_xboole_0(sK2,k4_xboole_0(X70,sK0)) = k2_xboole_0(k4_xboole_0(sK2,X70),k4_xboole_0(sK2,sK2))) )),
% 2.37/0.63    inference(superposition,[],[f35,f608])).
% 2.37/0.63  fof(f42,plain,(
% 2.37/0.63    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.37/0.63    inference(superposition,[],[f28,f18])).
% 2.37/0.63  fof(f93,plain,(
% 2.37/0.63    ( ! [X0] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) )),
% 2.37/0.63    inference(superposition,[],[f92,f25])).
% 2.37/0.63  fof(f92,plain,(
% 2.37/0.63    ( ! [X14] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X14)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X14))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f79,f30])).
% 2.37/0.63  fof(f79,plain,(
% 2.37/0.63    ( ! [X14] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X14)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X14)) )),
% 2.37/0.63    inference(superposition,[],[f30,f18])).
% 2.37/0.63  fof(f28,plain,(
% 2.37/0.63    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 2.37/0.63    inference(cnf_transformation,[],[f4])).
% 2.37/0.63  fof(f4,axiom,(
% 2.37/0.63    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.37/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.37/0.63  fof(f1266,plain,(
% 2.37/0.63    sK3 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 2.37/0.63    inference(backward_demodulation,[],[f63,f1260])).
% 2.37/0.63  fof(f1260,plain,(
% 2.37/0.63    sK3 = k4_xboole_0(sK3,sK2)),
% 2.37/0.63    inference(forward_demodulation,[],[f1247,f23])).
% 2.37/0.63  fof(f1247,plain,(
% 2.37/0.63    k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.37/0.63    inference(superposition,[],[f1101,f638])).
% 2.37/0.63  fof(f638,plain,(
% 2.37/0.63    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 2.37/0.63    inference(superposition,[],[f630,f36])).
% 2.37/0.63  fof(f36,plain,(
% 2.37/0.63    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.37/0.63    inference(superposition,[],[f24,f18])).
% 2.37/0.63  fof(f1101,plain,(
% 2.37/0.63    ( ! [X108] : (k4_xboole_0(sK3,X108) = k4_xboole_0(sK3,k4_xboole_0(X108,sK1))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f1100,f49])).
% 2.37/0.63  fof(f1100,plain,(
% 2.37/0.63    ( ! [X108] : (k4_xboole_0(sK3,k4_xboole_0(X108,sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,X108))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f1099,f25])).
% 2.37/0.63  fof(f1099,plain,(
% 2.37/0.63    ( ! [X108] : (k4_xboole_0(sK3,k4_xboole_0(X108,sK1)) = k2_xboole_0(k4_xboole_0(sK3,X108),k1_xboole_0)) )),
% 2.37/0.63    inference(forward_demodulation,[],[f925,f54])).
% 2.37/0.63  fof(f925,plain,(
% 2.37/0.63    ( ! [X108] : (k4_xboole_0(sK3,k4_xboole_0(X108,sK1)) = k2_xboole_0(k4_xboole_0(sK3,X108),k4_xboole_0(sK3,sK3))) )),
% 2.37/0.63    inference(superposition,[],[f35,f616])).
% 2.37/0.63  fof(f63,plain,(
% 2.37/0.63    k4_xboole_0(sK3,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 2.37/0.63    inference(superposition,[],[f43,f18])).
% 2.37/0.63  fof(f2336,plain,(
% 2.37/0.63    sK1 = k4_xboole_0(sK1,sK3)),
% 2.37/0.63    inference(superposition,[],[f2238,f1009])).
% 2.37/0.63  fof(f1009,plain,(
% 2.37/0.63    ( ! [X108] : (sK3 = k4_xboole_0(sK3,k4_xboole_0(sK1,X108))) )),
% 2.37/0.63    inference(forward_demodulation,[],[f877,f946])).
% 2.37/0.63  fof(f877,plain,(
% 2.37/0.63    ( ! [X108] : (k4_xboole_0(sK3,k4_xboole_0(sK1,X108)) = k2_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,X108)))) )),
% 2.37/0.63    inference(superposition,[],[f35,f616])).
% 2.37/0.63  fof(f2238,plain,(
% 2.37/0.63    ( ! [X67] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(sK3,X67))) )),
% 2.37/0.63    inference(superposition,[],[f1631,f633])).
% 2.37/0.63  fof(f3422,plain,(
% 2.37/0.63    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK1,sK0)),
% 2.37/0.63    inference(forward_demodulation,[],[f3192,f43])).
% 2.37/0.63  fof(f3192,plain,(
% 2.37/0.63    k4_xboole_0(sK2,sK0) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)),
% 2.37/0.63    inference(superposition,[],[f43,f3116])).
% 2.37/0.63  fof(f608,plain,(
% 2.37/0.63    sK2 = k4_xboole_0(sK2,sK0)),
% 2.37/0.63    inference(forward_demodulation,[],[f563,f23])).
% 2.37/0.63  fof(f563,plain,(
% 2.37/0.63    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.37/0.63    inference(superposition,[],[f33,f72])).
% 2.37/0.63  fof(f72,plain,(
% 2.37/0.63    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.37/0.63    inference(resolution,[],[f34,f19])).
% 2.37/0.63  fof(f19,plain,(
% 2.37/0.63    r1_xboole_0(sK2,sK0)),
% 2.37/0.63    inference(cnf_transformation,[],[f16])).
% 2.37/0.63  % SZS output end Proof for theBenchmark
% 2.37/0.63  % (5701)------------------------------
% 2.37/0.63  % (5701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.37/0.63  % (5701)Termination reason: Refutation
% 2.37/0.63  
% 2.37/0.63  % (5701)Memory used [KB]: 8315
% 2.37/0.63  % (5701)Time elapsed: 0.275 s
% 2.37/0.63  % (5701)------------------------------
% 2.37/0.63  % (5701)------------------------------
% 2.37/0.63  % (5691)Success in time 0.315 s
%------------------------------------------------------------------------------
