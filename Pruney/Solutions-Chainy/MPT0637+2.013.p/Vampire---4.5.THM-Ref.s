%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 (5046 expanded)
%              Number of leaves         :   16 (1471 expanded)
%              Depth                    :   22
%              Number of atoms          :  131 (7458 expanded)
%              Number of equality atoms :   87 (3422 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1517,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1514,f1512])).

fof(f1512,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) ),
    inference(backward_demodulation,[],[f1454,f1456])).

fof(f1456,plain,(
    ! [X4,X5] : k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) ),
    inference(backward_demodulation,[],[f847,f1453])).

fof(f1453,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f1442,f318])).

fof(f318,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(forward_demodulation,[],[f317,f114])).

fof(f114,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f65,f109])).

fof(f109,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f65,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f43,f33])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f317,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(superposition,[],[f215,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f55,f35])).

fof(f35,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f37,f33])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f215,plain,(
    ! [X6,X8,X7] : k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8) ),
    inference(forward_demodulation,[],[f209,f114])).

fof(f209,plain,(
    ! [X6,X8,X7] : k7_relat_1(k8_relat_1(X6,k6_relat_1(X7)),X8) = k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) ),
    inference(resolution,[],[f48,f33])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f1442,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f930,f914])).

fof(f914,plain,(
    ! [X206,X204,X205] : k7_relat_1(k7_relat_1(k6_relat_1(X206),X205),X204) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X205),X206),X205),X204) ),
    inference(backward_demodulation,[],[f831,f840])).

fof(f840,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f833,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f833,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4) ),
    inference(forward_demodulation,[],[f832,f318])).

fof(f832,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X3),X4) ),
    inference(backward_demodulation,[],[f782,f831])).

fof(f782,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4) ),
    inference(superposition,[],[f648,f56])).

fof(f648,plain,(
    ! [X45,X46,X44] : k7_relat_1(k7_relat_1(k6_relat_1(X44),X45),X46) = k7_relat_1(k6_relat_1(X44),k1_setfam_1(k2_enumset1(X45,X45,X45,X46))) ),
    inference(resolution,[],[f54,f33])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f49,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f50])).

fof(f42,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f831,plain,(
    ! [X206,X204,X205] : k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X205,X205,X205,X206))),X204) = k7_relat_1(k7_relat_1(k6_relat_1(X206),X205),X204) ),
    inference(forward_demodulation,[],[f818,f379])).

fof(f379,plain,(
    ! [X21,X19,X20] : k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X21) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X21),X19),X20)) ),
    inference(forward_demodulation,[],[f378,f216])).

fof(f216,plain,(
    ! [X4,X2,X3] : k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X4),X3) ),
    inference(backward_demodulation,[],[f118,f215])).

fof(f118,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k7_relat_1(k6_relat_1(X4),X3)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2)) ),
    inference(backward_demodulation,[],[f76,f114])).

fof(f76,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k5_relat_1(k8_relat_1(X4,k6_relat_1(X3)),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f66,f65])).

fof(f66,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) = k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X2)) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(resolution,[],[f57,f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f378,plain,(
    ! [X21,X19,X20] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X19),X20),k6_relat_1(X21))) = k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X21) ),
    inference(forward_demodulation,[],[f377,f142])).

fof(f142,plain,(
    ! [X4,X2,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(forward_demodulation,[],[f110,f114])).

fof(f110,plain,(
    ! [X4,X2,X3] : k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(resolution,[],[f44,f69])).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(backward_demodulation,[],[f58,f65])).

fof(f377,plain,(
    ! [X21,X19,X20] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X19),X20),k6_relat_1(X21))) = k5_relat_1(k6_relat_1(X21),k7_relat_1(k6_relat_1(X20),X19)) ),
    inference(forward_demodulation,[],[f364,f375])).

fof(f375,plain,(
    ! [X17,X18] : k7_relat_1(k6_relat_1(X17),X18) = k4_relat_1(k7_relat_1(k6_relat_1(X18),X17)) ),
    inference(forward_demodulation,[],[f374,f109])).

fof(f374,plain,(
    ! [X17,X18] : k7_relat_1(k6_relat_1(X17),X18) = k4_relat_1(k5_relat_1(k6_relat_1(X17),k6_relat_1(X18))) ),
    inference(forward_demodulation,[],[f373,f109])).

fof(f373,plain,(
    ! [X17,X18] : k4_relat_1(k5_relat_1(k6_relat_1(X17),k6_relat_1(X18))) = k5_relat_1(k6_relat_1(X18),k6_relat_1(X17)) ),
    inference(forward_demodulation,[],[f363,f34])).

fof(f34,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f363,plain,(
    ! [X17,X18] : k4_relat_1(k5_relat_1(k6_relat_1(X17),k6_relat_1(X18))) = k5_relat_1(k6_relat_1(X18),k4_relat_1(k6_relat_1(X17))) ),
    inference(resolution,[],[f359,f33])).

fof(f359,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X17)
      | k4_relat_1(k5_relat_1(X17,k6_relat_1(X18))) = k5_relat_1(k6_relat_1(X18),k4_relat_1(X17)) ) ),
    inference(forward_demodulation,[],[f352,f34])).

fof(f352,plain,(
    ! [X17,X18] :
      ( k4_relat_1(k5_relat_1(X17,k6_relat_1(X18))) = k5_relat_1(k4_relat_1(k6_relat_1(X18)),k4_relat_1(X17))
      | ~ v1_relat_1(X17) ) ),
    inference(resolution,[],[f38,f33])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f364,plain,(
    ! [X21,X19,X20] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X19),X20),k6_relat_1(X21))) = k5_relat_1(k6_relat_1(X21),k4_relat_1(k7_relat_1(k6_relat_1(X19),X20))) ),
    inference(resolution,[],[f359,f115])).

fof(f115,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(backward_demodulation,[],[f69,f114])).

fof(f818,plain,(
    ! [X206,X204,X205] : k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X205,X205,X205,X206))),X204) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X204),X205),X206)) ),
    inference(superposition,[],[f375,f648])).

fof(f930,plain,(
    ! [X206,X204,X205] : k7_relat_1(k7_relat_1(k6_relat_1(X204),X205),X206) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X204),X205),X206),X206) ),
    inference(forward_demodulation,[],[f885,f914])).

fof(f885,plain,(
    ! [X206,X204,X205] : k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X205),X204),X205),X206) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X205),X204),X205),X206),X206) ),
    inference(superposition,[],[f318,f833])).

fof(f847,plain,(
    ! [X4,X5] : k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X4),X5)) ),
    inference(superposition,[],[f35,f833])).

fof(f1454,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) ),
    inference(backward_demodulation,[],[f833,f1453])).

fof(f1514,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f137,f1456])).

fof(f137,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f68,f114])).

fof(f68,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f52,f65])).

fof(f52,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f32,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30])).

fof(f30,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.40  % (24831)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.45  % (24821)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (24826)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.46  % (24827)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (24828)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (24820)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (24831)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f1517,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f1514,f1512])).
% 0.21/0.47  fof(f1512,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f1454,f1456])).
% 0.21/0.47  fof(f1456,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) = k1_setfam_1(k2_enumset1(X4,X4,X4,X5))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f847,f1453])).
% 0.21/0.47  fof(f1453,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f1442,f318])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f317,f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f65,f109])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.47    inference(resolution,[],[f44,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.21/0.47    inference(resolution,[],[f43,f33])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 0.21/0.47    inference(superposition,[],[f215,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f55,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 0.21/0.47    inference(resolution,[],[f37,f33])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X7),X8)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f209,f114])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    ( ! [X6,X8,X7] : (k7_relat_1(k8_relat_1(X6,k6_relat_1(X7)),X8) = k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8))) )),
% 0.21/0.47    inference(resolution,[],[f48,f33])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.21/0.47  fof(f1442,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.21/0.47    inference(superposition,[],[f930,f914])).
% 0.21/0.47  fof(f914,plain,(
% 0.21/0.47    ( ! [X206,X204,X205] : (k7_relat_1(k7_relat_1(k6_relat_1(X206),X205),X204) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X205),X206),X205),X204)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f831,f840])).
% 0.21/0.47  fof(f840,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) )),
% 0.21/0.47    inference(superposition,[],[f833,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f40,f50,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.47    inference(definition_unfolding,[],[f41,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.47  fof(f833,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f832,f318])).
% 0.21/0.47  fof(f832,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X3),X4)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f782,f831])).
% 0.21/0.47  fof(f782,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4)) )),
% 0.21/0.47    inference(superposition,[],[f648,f56])).
% 0.21/0.47  fof(f648,plain,(
% 0.21/0.47    ( ! [X45,X46,X44] : (k7_relat_1(k7_relat_1(k6_relat_1(X44),X45),X46) = k7_relat_1(k6_relat_1(X44),k1_setfam_1(k2_enumset1(X45,X45,X45,X46)))) )),
% 0.21/0.47    inference(resolution,[],[f54,f33])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f49,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f42,f50])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.47  fof(f831,plain,(
% 0.21/0.47    ( ! [X206,X204,X205] : (k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X205,X205,X205,X206))),X204) = k7_relat_1(k7_relat_1(k6_relat_1(X206),X205),X204)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f818,f379])).
% 0.21/0.47  fof(f379,plain,(
% 0.21/0.47    ( ! [X21,X19,X20] : (k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X21) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X21),X19),X20))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f378,f216])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X4),X3)) )),
% 0.21/0.47    inference(backward_demodulation,[],[f118,f215])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (k8_relat_1(X2,k7_relat_1(k6_relat_1(X4),X3)) = k5_relat_1(k7_relat_1(k6_relat_1(X4),X3),k6_relat_1(X2))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f76,f114])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (k8_relat_1(X2,k8_relat_1(X4,k6_relat_1(X3))) = k5_relat_1(k8_relat_1(X4,k6_relat_1(X3)),k6_relat_1(X2))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f66,f65])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (k8_relat_1(X2,k5_relat_1(k6_relat_1(X3),k6_relat_1(X4))) = k5_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X4)),k6_relat_1(X2))) )),
% 0.21/0.47    inference(resolution,[],[f43,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.21/0.47    inference(resolution,[],[f57,f33])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))) )),
% 0.21/0.47    inference(resolution,[],[f46,f33])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.47  fof(f378,plain,(
% 0.21/0.47    ( ! [X21,X19,X20] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X19),X20),k6_relat_1(X21))) = k7_relat_1(k7_relat_1(k6_relat_1(X20),X19),X21)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f377,f142])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k5_relat_1(k6_relat_1(X4),k7_relat_1(k6_relat_1(X2),X3))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f110,f114])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X4,X2,X3] : (k7_relat_1(k8_relat_1(X2,k6_relat_1(X3)),X4) = k5_relat_1(k6_relat_1(X4),k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.21/0.47    inference(resolution,[],[f44,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f58,f65])).
% 0.21/0.47  fof(f377,plain,(
% 0.21/0.47    ( ! [X21,X19,X20] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X19),X20),k6_relat_1(X21))) = k5_relat_1(k6_relat_1(X21),k7_relat_1(k6_relat_1(X20),X19))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f364,f375])).
% 0.21/0.47  fof(f375,plain,(
% 0.21/0.47    ( ! [X17,X18] : (k7_relat_1(k6_relat_1(X17),X18) = k4_relat_1(k7_relat_1(k6_relat_1(X18),X17))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f374,f109])).
% 0.21/0.47  fof(f374,plain,(
% 0.21/0.47    ( ! [X17,X18] : (k7_relat_1(k6_relat_1(X17),X18) = k4_relat_1(k5_relat_1(k6_relat_1(X17),k6_relat_1(X18)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f373,f109])).
% 0.21/0.47  fof(f373,plain,(
% 0.21/0.47    ( ! [X17,X18] : (k4_relat_1(k5_relat_1(k6_relat_1(X17),k6_relat_1(X18))) = k5_relat_1(k6_relat_1(X18),k6_relat_1(X17))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f363,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.21/0.47  fof(f363,plain,(
% 0.21/0.47    ( ! [X17,X18] : (k4_relat_1(k5_relat_1(k6_relat_1(X17),k6_relat_1(X18))) = k5_relat_1(k6_relat_1(X18),k4_relat_1(k6_relat_1(X17)))) )),
% 0.21/0.47    inference(resolution,[],[f359,f33])).
% 0.21/0.47  fof(f359,plain,(
% 0.21/0.47    ( ! [X17,X18] : (~v1_relat_1(X17) | k4_relat_1(k5_relat_1(X17,k6_relat_1(X18))) = k5_relat_1(k6_relat_1(X18),k4_relat_1(X17))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f352,f34])).
% 0.21/0.47  fof(f352,plain,(
% 0.21/0.47    ( ! [X17,X18] : (k4_relat_1(k5_relat_1(X17,k6_relat_1(X18))) = k5_relat_1(k4_relat_1(k6_relat_1(X18)),k4_relat_1(X17)) | ~v1_relat_1(X17)) )),
% 0.21/0.47    inference(resolution,[],[f38,f33])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.47  fof(f364,plain,(
% 0.21/0.47    ( ! [X21,X19,X20] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X19),X20),k6_relat_1(X21))) = k5_relat_1(k6_relat_1(X21),k4_relat_1(k7_relat_1(k6_relat_1(X19),X20)))) )),
% 0.21/0.47    inference(resolution,[],[f359,f115])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f69,f114])).
% 0.21/0.47  fof(f818,plain,(
% 0.21/0.47    ( ! [X206,X204,X205] : (k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X205,X205,X205,X206))),X204) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X204),X205),X206))) )),
% 0.21/0.47    inference(superposition,[],[f375,f648])).
% 0.21/0.47  fof(f930,plain,(
% 0.21/0.47    ( ! [X206,X204,X205] : (k7_relat_1(k7_relat_1(k6_relat_1(X204),X205),X206) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X204),X205),X206),X206)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f885,f914])).
% 0.21/0.47  fof(f885,plain,(
% 0.21/0.47    ( ! [X206,X204,X205] : (k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X205),X204),X205),X206) = k7_relat_1(k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X205),X204),X205),X206),X206)) )),
% 0.21/0.47    inference(superposition,[],[f318,f833])).
% 0.21/0.47  fof(f847,plain,(
% 0.21/0.47    ( ! [X4,X5] : (k1_setfam_1(k2_enumset1(X4,X4,X4,X5)) = k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X5),X4),X5))) )),
% 0.21/0.47    inference(superposition,[],[f35,f833])).
% 0.21/0.47  fof(f1454,plain,(
% 0.21/0.47    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))) )),
% 0.21/0.47    inference(backward_demodulation,[],[f833,f1453])).
% 0.21/0.47  fof(f1514,plain,(
% 0.21/0.47    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 0.21/0.47    inference(backward_demodulation,[],[f137,f1456])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.47    inference(backward_demodulation,[],[f68,f114])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.21/0.47    inference(backward_demodulation,[],[f52,f65])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.21/0.47    inference(definition_unfolding,[],[f32,f51])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f17])).
% 0.21/0.47  fof(f17,conjecture,(
% 0.21/0.47    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (24831)------------------------------
% 0.21/0.47  % (24831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (24831)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (24831)Memory used [KB]: 3582
% 0.21/0.47  % (24831)Time elapsed: 0.067 s
% 0.21/0.47  % (24831)------------------------------
% 0.21/0.47  % (24831)------------------------------
% 0.21/0.47  % (24829)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (24817)Success in time 0.121 s
%------------------------------------------------------------------------------
