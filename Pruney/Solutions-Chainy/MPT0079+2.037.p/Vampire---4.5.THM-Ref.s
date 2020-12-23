%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:56 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  110 (1183 expanded)
%              Number of leaves         :   11 ( 326 expanded)
%              Depth                    :   27
%              Number of atoms          :  136 (2135 expanded)
%              Number of equality atoms :  114 (1341 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1071,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1070,f494])).

fof(f494,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f486,f21])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f486,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | sK1 = sK2 ),
    inference(superposition,[],[f30,f470])).

fof(f470,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f239,f46])).

fof(f46,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f24,f18])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f239,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f33,f226])).

fof(f226,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f218,f38])).

fof(f38,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f19,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f19,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f218,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | sK2 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f30,f195])).

fof(f195,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(superposition,[],[f24,f55])).

fof(f55,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f54,f48])).

fof(f48,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f35,f38])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f54,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f49,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f49,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f27,f38])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f1070,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1069,f176])).

fof(f176,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f24,f171])).

fof(f171,plain,(
    sK1 = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f165,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f165,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f35,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f41,f36])).

fof(f41,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f20,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f1069,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1059,f791])).

fof(f791,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f370,f773])).

fof(f773,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f772,f142])).

fof(f142,plain,(
    sK0 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f136,f23])).

fof(f136,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f35,f42])).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f39,f36])).

fof(f39,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f19,f29])).

fof(f772,plain,(
    sK3 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f763,f648])).

fof(f648,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f647,f73])).

fof(f73,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f72,f25])).

fof(f72,plain,(
    sK3 = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f67,f23])).

fof(f67,plain,(
    sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f35,f40])).

fof(f40,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f20,f36])).

fof(f647,plain,(
    k2_xboole_0(k1_xboole_0,sK3) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f646,f25])).

fof(f646,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f641,f25])).

fof(f641,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f27,f637])).

fof(f637,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f627,f24])).

fof(f627,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f328,f18])).

fof(f328,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f33,f316])).

fof(f316,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f306,f42])).

fof(f306,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f30,f207])).

fof(f207,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(superposition,[],[f24,f140])).

fof(f140,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f139,f133])).

fof(f133,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f35,f42])).

fof(f139,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f134,f25])).

fof(f134,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f27,f42])).

fof(f763,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f27,f744])).

fof(f744,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f544,f292])).

fof(f292,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f275,f18])).

fof(f275,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X0,sK3)) ),
    inference(backward_demodulation,[],[f245,f268])).

fof(f268,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f260,f40])).

fof(f260,plain,
    ( k1_xboole_0 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | sK3 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f30,f201])).

fof(f201,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(superposition,[],[f24,f71])).

fof(f71,plain,(
    sK3 = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(forward_demodulation,[],[f70,f64])).

fof(f64,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f35,f40])).

fof(f70,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(forward_demodulation,[],[f65,f25])).

fof(f65,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[],[f27,f40])).

fof(f245,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f88,f25])).

fof(f88,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) ),
    inference(backward_demodulation,[],[f66,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f81,f24])).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f33,f61])).

fof(f61,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f24,f56])).

fof(f56,plain,(
    sK2 = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f51,f23])).

fof(f51,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f35,f38])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) ),
    inference(superposition,[],[f33,f40])).

fof(f544,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f284,f25])).

fof(f284,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f33,f268])).

fof(f370,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f33,f358])).

fof(f358,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f348,f44])).

fof(f348,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f30,f213])).

fof(f213,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(superposition,[],[f24,f169])).

fof(f169,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f168,f162])).

fof(f162,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f35,f44])).

fof(f168,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f163,f25])).

fof(f163,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f27,f44])).

fof(f1059,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f791,f845])).

fof(f845,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f774,f25])).

fof(f774,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f18,f773])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.13/0.52  % (20951)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.13/0.53  % (20949)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.13/0.53  % (20954)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.13/0.53  % (20957)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.53  % (20971)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.30/0.54  % (20950)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.54  % (20968)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.54  % (20958)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.55  % (20943)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.55  % (20967)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.55  % (20966)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.56  % (20973)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.56  % (20959)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.56  % (20959)Refutation not found, incomplete strategy% (20959)------------------------------
% 1.30/0.56  % (20959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.56  % (20959)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.56  
% 1.30/0.56  % (20959)Memory used [KB]: 10618
% 1.30/0.56  % (20959)Time elapsed: 0.135 s
% 1.30/0.56  % (20959)------------------------------
% 1.30/0.56  % (20959)------------------------------
% 1.30/0.56  % (20953)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.30/0.56  % (20962)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.56  % (20947)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.30/0.56  % (20948)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.30/0.56  % (20946)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.30/0.56  % (20972)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.56  % (20960)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.56  % (20952)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.57  % (20945)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.57  % (20970)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.57  % (20956)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.57  % (20961)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.57  % (20965)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.57  % (20963)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.30/0.57  % (20969)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.58  % (20944)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.30/0.59  % (20955)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.61  % (20960)Refutation found. Thanks to Tanya!
% 1.30/0.61  % SZS status Theorem for theBenchmark
% 1.30/0.61  % SZS output start Proof for theBenchmark
% 1.30/0.61  fof(f1071,plain,(
% 1.30/0.61    $false),
% 1.30/0.61    inference(subsumption_resolution,[],[f1070,f494])).
% 1.30/0.61  fof(f494,plain,(
% 1.30/0.61    k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 1.30/0.61    inference(subsumption_resolution,[],[f486,f21])).
% 1.30/0.61  fof(f21,plain,(
% 1.30/0.61    sK1 != sK2),
% 1.30/0.61    inference(cnf_transformation,[],[f15])).
% 1.30/0.61  fof(f15,plain,(
% 1.30/0.61    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.30/0.61    inference(flattening,[],[f14])).
% 1.30/0.61  fof(f14,plain,(
% 1.30/0.61    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.30/0.61    inference(ennf_transformation,[],[f13])).
% 1.30/0.61  fof(f13,negated_conjecture,(
% 1.30/0.61    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.30/0.61    inference(negated_conjecture,[],[f12])).
% 1.30/0.61  fof(f12,conjecture,(
% 1.30/0.61    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.30/0.61  fof(f486,plain,(
% 1.30/0.61    k1_xboole_0 != k4_xboole_0(sK1,sK2) | sK1 = sK2),
% 1.30/0.61    inference(superposition,[],[f30,f470])).
% 1.30/0.61  fof(f470,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.30/0.61    inference(superposition,[],[f239,f46])).
% 1.30/0.61  fof(f46,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.30/0.61    inference(superposition,[],[f24,f18])).
% 1.30/0.61  fof(f18,plain,(
% 1.30/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.30/0.61    inference(cnf_transformation,[],[f15])).
% 1.30/0.61  fof(f24,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.30/0.61    inference(cnf_transformation,[],[f9])).
% 1.30/0.61  fof(f9,axiom,(
% 1.30/0.61    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.30/0.61  fof(f239,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.30/0.61    inference(superposition,[],[f33,f226])).
% 1.30/0.61  fof(f226,plain,(
% 1.30/0.61    sK2 = k4_xboole_0(sK2,sK0)),
% 1.30/0.61    inference(subsumption_resolution,[],[f218,f38])).
% 1.30/0.61  fof(f38,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.30/0.61    inference(resolution,[],[f19,f36])).
% 1.30/0.61  fof(f36,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.61    inference(definition_unfolding,[],[f32,f26])).
% 1.30/0.61  fof(f26,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.30/0.61    inference(cnf_transformation,[],[f10])).
% 1.30/0.61  fof(f10,axiom,(
% 1.30/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.30/0.61  fof(f32,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.30/0.61    inference(cnf_transformation,[],[f2])).
% 1.30/0.61  fof(f2,axiom,(
% 1.30/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.30/0.61  fof(f19,plain,(
% 1.30/0.61    r1_xboole_0(sK2,sK0)),
% 1.30/0.61    inference(cnf_transformation,[],[f15])).
% 1.30/0.61  fof(f218,plain,(
% 1.30/0.61    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | sK2 = k4_xboole_0(sK2,sK0)),
% 1.30/0.61    inference(superposition,[],[f30,f195])).
% 1.30/0.61  fof(f195,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 1.30/0.61    inference(superposition,[],[f24,f55])).
% 1.30/0.61  fof(f55,plain,(
% 1.30/0.61    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 1.30/0.61    inference(forward_demodulation,[],[f54,f48])).
% 1.30/0.61  fof(f48,plain,(
% 1.30/0.61    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.30/0.61    inference(superposition,[],[f35,f38])).
% 1.30/0.61  fof(f35,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.30/0.61    inference(definition_unfolding,[],[f28,f26])).
% 1.30/0.61  fof(f28,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.30/0.61    inference(cnf_transformation,[],[f11])).
% 1.30/0.61  fof(f11,axiom,(
% 1.30/0.61    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.30/0.61  fof(f54,plain,(
% 1.30/0.61    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 1.30/0.61    inference(forward_demodulation,[],[f49,f25])).
% 1.30/0.61  fof(f25,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.30/0.61    inference(cnf_transformation,[],[f1])).
% 1.30/0.61  fof(f1,axiom,(
% 1.30/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.30/0.61  fof(f49,plain,(
% 1.30/0.61    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f27,f38])).
% 1.30/0.61  fof(f27,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.30/0.61    inference(cnf_transformation,[],[f6])).
% 1.30/0.61  fof(f6,axiom,(
% 1.30/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.30/0.61  fof(f33,plain,(
% 1.30/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.30/0.61    inference(cnf_transformation,[],[f8])).
% 1.30/0.61  fof(f8,axiom,(
% 1.30/0.61    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.30/0.61  fof(f30,plain,(
% 1.30/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 1.30/0.61    inference(cnf_transformation,[],[f17])).
% 1.30/0.61  fof(f17,plain,(
% 1.30/0.61    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 1.30/0.61    inference(ennf_transformation,[],[f5])).
% 1.30/0.61  fof(f5,axiom,(
% 1.30/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 1.30/0.61  fof(f1070,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.30/0.61    inference(forward_demodulation,[],[f1069,f176])).
% 1.30/0.61  fof(f176,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.30/0.61    inference(superposition,[],[f24,f171])).
% 1.30/0.61  fof(f171,plain,(
% 1.30/0.61    sK1 = k2_xboole_0(sK1,k1_xboole_0)),
% 1.30/0.61    inference(forward_demodulation,[],[f165,f23])).
% 1.30/0.61  fof(f23,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.30/0.61    inference(cnf_transformation,[],[f7])).
% 1.30/0.61  fof(f7,axiom,(
% 1.30/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.30/0.61  fof(f165,plain,(
% 1.30/0.61    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f35,f44])).
% 1.30/0.61  fof(f44,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 1.30/0.61    inference(resolution,[],[f41,f36])).
% 1.30/0.61  fof(f41,plain,(
% 1.30/0.61    r1_xboole_0(sK1,sK3)),
% 1.30/0.61    inference(resolution,[],[f20,f29])).
% 1.30/0.61  fof(f29,plain,(
% 1.30/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.30/0.61    inference(cnf_transformation,[],[f16])).
% 1.30/0.61  fof(f16,plain,(
% 1.30/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.30/0.61    inference(ennf_transformation,[],[f3])).
% 1.30/0.61  fof(f3,axiom,(
% 1.30/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.30/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.30/0.61  fof(f20,plain,(
% 1.30/0.61    r1_xboole_0(sK3,sK1)),
% 1.30/0.61    inference(cnf_transformation,[],[f15])).
% 1.30/0.61  fof(f1069,plain,(
% 1.30/0.61    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK2)),
% 1.30/0.61    inference(forward_demodulation,[],[f1059,f791])).
% 1.30/0.61  fof(f791,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0))) )),
% 1.30/0.61    inference(backward_demodulation,[],[f370,f773])).
% 1.30/0.61  fof(f773,plain,(
% 1.30/0.61    sK0 = sK3),
% 1.30/0.61    inference(forward_demodulation,[],[f772,f142])).
% 1.30/0.61  fof(f142,plain,(
% 1.30/0.61    sK0 = k2_xboole_0(sK0,k1_xboole_0)),
% 1.30/0.61    inference(forward_demodulation,[],[f136,f23])).
% 1.30/0.61  fof(f136,plain,(
% 1.30/0.61    sK0 = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f35,f42])).
% 1.30/0.61  fof(f42,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.30/0.61    inference(resolution,[],[f39,f36])).
% 1.30/0.61  fof(f39,plain,(
% 1.30/0.61    r1_xboole_0(sK0,sK2)),
% 1.30/0.61    inference(resolution,[],[f19,f29])).
% 1.30/0.61  fof(f772,plain,(
% 1.30/0.61    sK3 = k2_xboole_0(sK0,k1_xboole_0)),
% 1.30/0.61    inference(forward_demodulation,[],[f763,f648])).
% 1.30/0.61  fof(f648,plain,(
% 1.30/0.61    sK3 = k2_xboole_0(sK0,sK3)),
% 1.30/0.61    inference(forward_demodulation,[],[f647,f73])).
% 1.30/0.61  fof(f73,plain,(
% 1.30/0.61    sK3 = k2_xboole_0(k1_xboole_0,sK3)),
% 1.30/0.61    inference(superposition,[],[f72,f25])).
% 1.30/0.61  fof(f72,plain,(
% 1.30/0.61    sK3 = k2_xboole_0(sK3,k1_xboole_0)),
% 1.30/0.61    inference(forward_demodulation,[],[f67,f23])).
% 1.30/0.61  fof(f67,plain,(
% 1.30/0.61    sK3 = k2_xboole_0(k4_xboole_0(sK3,k1_xboole_0),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f35,f40])).
% 1.30/0.61  fof(f40,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.30/0.61    inference(resolution,[],[f20,f36])).
% 1.30/0.61  fof(f647,plain,(
% 1.30/0.61    k2_xboole_0(k1_xboole_0,sK3) = k2_xboole_0(sK0,sK3)),
% 1.30/0.61    inference(forward_demodulation,[],[f646,f25])).
% 1.30/0.61  fof(f646,plain,(
% 1.30/0.61    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 1.30/0.61    inference(forward_demodulation,[],[f641,f25])).
% 1.30/0.61  fof(f641,plain,(
% 1.30/0.61    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0)),
% 1.30/0.61    inference(superposition,[],[f27,f637])).
% 1.30/0.61  fof(f637,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 1.30/0.61    inference(forward_demodulation,[],[f627,f24])).
% 1.30/0.61  fof(f627,plain,(
% 1.30/0.61    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 1.30/0.61    inference(superposition,[],[f328,f18])).
% 1.30/0.61  fof(f328,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 1.30/0.61    inference(superposition,[],[f33,f316])).
% 1.30/0.61  fof(f316,plain,(
% 1.30/0.61    sK0 = k4_xboole_0(sK0,sK2)),
% 1.30/0.61    inference(subsumption_resolution,[],[f306,f42])).
% 1.30/0.61  fof(f306,plain,(
% 1.30/0.61    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | sK0 = k4_xboole_0(sK0,sK2)),
% 1.30/0.61    inference(superposition,[],[f30,f207])).
% 1.30/0.61  fof(f207,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 1.30/0.61    inference(superposition,[],[f24,f140])).
% 1.30/0.61  fof(f140,plain,(
% 1.30/0.61    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 1.30/0.61    inference(forward_demodulation,[],[f139,f133])).
% 1.30/0.61  fof(f133,plain,(
% 1.30/0.61    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 1.30/0.61    inference(superposition,[],[f35,f42])).
% 1.30/0.61  fof(f139,plain,(
% 1.30/0.61    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 1.30/0.61    inference(forward_demodulation,[],[f134,f25])).
% 1.30/0.61  fof(f134,plain,(
% 1.30/0.61    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f27,f42])).
% 1.30/0.61  fof(f763,plain,(
% 1.30/0.61    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 1.30/0.61    inference(superposition,[],[f27,f744])).
% 1.30/0.61  fof(f744,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 1.30/0.61    inference(superposition,[],[f544,f292])).
% 1.30/0.61  fof(f292,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.30/0.61    inference(superposition,[],[f275,f18])).
% 1.30/0.61  fof(f275,plain,(
% 1.30/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X0,sK3))) )),
% 1.30/0.61    inference(backward_demodulation,[],[f245,f268])).
% 1.30/0.61  fof(f268,plain,(
% 1.30/0.61    sK3 = k4_xboole_0(sK3,sK1)),
% 1.30/0.61    inference(subsumption_resolution,[],[f260,f40])).
% 1.30/0.61  fof(f260,plain,(
% 1.30/0.61    k1_xboole_0 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) | sK3 = k4_xboole_0(sK3,sK1)),
% 1.30/0.61    inference(superposition,[],[f30,f201])).
% 1.30/0.61  fof(f201,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 1.30/0.61    inference(superposition,[],[f24,f71])).
% 1.30/0.61  fof(f71,plain,(
% 1.30/0.61    sK3 = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 1.30/0.61    inference(forward_demodulation,[],[f70,f64])).
% 1.30/0.61  fof(f64,plain,(
% 1.30/0.61    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 1.30/0.61    inference(superposition,[],[f35,f40])).
% 1.30/0.61  fof(f70,plain,(
% 1.30/0.61    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 1.30/0.61    inference(forward_demodulation,[],[f65,f25])).
% 1.30/0.61  fof(f65,plain,(
% 1.30/0.61    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f27,f40])).
% 1.30/0.61  fof(f245,plain,(
% 1.30/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X0,k4_xboole_0(sK3,sK1)))) )),
% 1.30/0.61    inference(superposition,[],[f88,f25])).
% 1.30/0.61  fof(f88,plain,(
% 1.30/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0))) )),
% 1.30/0.61    inference(backward_demodulation,[],[f66,f87])).
% 1.30/0.61  fof(f87,plain,(
% 1.30/0.61    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.30/0.61    inference(forward_demodulation,[],[f81,f24])).
% 1.30/0.61  fof(f81,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0))) )),
% 1.30/0.61    inference(superposition,[],[f33,f61])).
% 1.30/0.61  fof(f61,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 1.30/0.61    inference(superposition,[],[f24,f56])).
% 1.30/0.61  fof(f56,plain,(
% 1.30/0.61    sK2 = k2_xboole_0(sK2,k1_xboole_0)),
% 1.30/0.61    inference(forward_demodulation,[],[f51,f23])).
% 1.30/0.61  fof(f51,plain,(
% 1.30/0.61    sK2 = k2_xboole_0(k4_xboole_0(sK2,k1_xboole_0),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f35,f38])).
% 1.30/0.61  fof(f66,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0))) )),
% 1.30/0.61    inference(superposition,[],[f33,f40])).
% 1.30/0.61  fof(f544,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 1.30/0.61    inference(superposition,[],[f284,f25])).
% 1.30/0.61  fof(f284,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 1.30/0.61    inference(superposition,[],[f33,f268])).
% 1.30/0.61  fof(f370,plain,(
% 1.30/0.61    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 1.30/0.61    inference(superposition,[],[f33,f358])).
% 1.30/0.61  fof(f358,plain,(
% 1.30/0.61    sK1 = k4_xboole_0(sK1,sK3)),
% 1.30/0.61    inference(subsumption_resolution,[],[f348,f44])).
% 1.30/0.61  fof(f348,plain,(
% 1.30/0.61    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | sK1 = k4_xboole_0(sK1,sK3)),
% 1.30/0.61    inference(superposition,[],[f30,f213])).
% 1.30/0.61  fof(f213,plain,(
% 1.30/0.61    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 1.30/0.61    inference(superposition,[],[f24,f169])).
% 1.30/0.61  fof(f169,plain,(
% 1.30/0.61    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 1.30/0.61    inference(forward_demodulation,[],[f168,f162])).
% 1.30/0.61  fof(f162,plain,(
% 1.30/0.61    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 1.30/0.61    inference(superposition,[],[f35,f44])).
% 1.30/0.61  fof(f168,plain,(
% 1.30/0.61    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 1.30/0.61    inference(forward_demodulation,[],[f163,f25])).
% 1.30/0.61  fof(f163,plain,(
% 1.30/0.61    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)),
% 1.30/0.61    inference(superposition,[],[f27,f44])).
% 1.30/0.61  fof(f1059,plain,(
% 1.30/0.61    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 1.30/0.61    inference(superposition,[],[f791,f845])).
% 1.30/0.61  fof(f845,plain,(
% 1.30/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 1.30/0.61    inference(superposition,[],[f774,f25])).
% 1.30/0.61  fof(f774,plain,(
% 1.30/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 1.30/0.61    inference(backward_demodulation,[],[f18,f773])).
% 1.30/0.61  % SZS output end Proof for theBenchmark
% 1.30/0.61  % (20960)------------------------------
% 1.30/0.61  % (20960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.61  % (20960)Termination reason: Refutation
% 1.30/0.61  
% 1.30/0.61  % (20960)Memory used [KB]: 2302
% 1.30/0.61  % (20960)Time elapsed: 0.142 s
% 1.30/0.61  % (20960)------------------------------
% 1.30/0.61  % (20960)------------------------------
% 1.30/0.62  % (20942)Success in time 0.245 s
%------------------------------------------------------------------------------
