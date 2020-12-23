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
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 329 expanded)
%              Number of leaves         :   17 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          :  136 ( 425 expanded)
%              Number of equality atoms :   75 ( 287 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2752,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2609])).

fof(f2609,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f102,f2210])).

fof(f2210,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[],[f2112,f126])).

fof(f126,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(superposition,[],[f103,f94])).

fof(f94,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f91,f33])).

fof(f33,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f91,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f54,f32])).

fof(f32,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f103,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f94,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f48,f48])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f2112,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_demodulation,[],[f1985,f735])).

fof(f735,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(subsumption_resolution,[],[f105,f178])).

fof(f178,plain,(
    ! [X6,X7] : v1_relat_1(k7_relat_1(k6_relat_1(X7),X6)) ),
    inference(superposition,[],[f100,f175])).

fof(f175,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k2_zfmisc_1(X1,X0))) ),
    inference(forward_demodulation,[],[f174,f64])).

fof(f64,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f58,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f40,f32])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f174,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k2_zfmisc_1(X1,X0))) ),
    inference(forward_demodulation,[],[f167,f33])).

fof(f167,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0))) ),
    inference(resolution,[],[f99,f32])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(backward_demodulation,[],[f55,f94])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

fof(f100,plain,(
    ! [X0,X1] : v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),X1))) ),
    inference(backward_demodulation,[],[f57,f94])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f97,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(backward_demodulation,[],[f51,f94])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1985,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[],[f109,f328])).

fof(f328,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) ),
    inference(resolution,[],[f198,f32])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) ),
    inference(forward_demodulation,[],[f56,f94])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f109,plain,(
    ! [X2,X3] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(resolution,[],[f95,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f82,f59])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f44,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0) ),
    inference(backward_demodulation,[],[f69,f94])).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f51,f52])).

fof(f102,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f65,f94])).

fof(f65,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f63,f64])).

fof(f63,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f50,f58])).

fof(f50,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f31,f49])).

fof(f31,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f29])).

fof(f29,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (2993)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (2985)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (2994)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (2982)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (2979)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (2980)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.51  % (2987)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (2990)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (2990)Refutation not found, incomplete strategy% (2990)------------------------------
% 0.20/0.51  % (2990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (2990)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (2990)Memory used [KB]: 10490
% 0.20/0.51  % (2990)Time elapsed: 0.095 s
% 0.20/0.51  % (2990)------------------------------
% 0.20/0.51  % (2990)------------------------------
% 0.20/0.51  % (2988)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (2992)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.52  % (2996)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.52  % (2991)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.52  % (2983)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.52  % (2986)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.52  % (2989)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.52  % (2995)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.53  % (2981)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.53  % (2978)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 2.11/0.65  % (2991)Refutation found. Thanks to Tanya!
% 2.11/0.65  % SZS status Theorem for theBenchmark
% 2.11/0.66  % SZS output start Proof for theBenchmark
% 2.11/0.66  fof(f2752,plain,(
% 2.11/0.66    $false),
% 2.11/0.66    inference(trivial_inequality_removal,[],[f2609])).
% 2.11/0.66  fof(f2609,plain,(
% 2.11/0.66    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.11/0.66    inference(superposition,[],[f102,f2210])).
% 2.11/0.66  fof(f2210,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 2.11/0.66    inference(superposition,[],[f2112,f126])).
% 2.11/0.66  fof(f126,plain,(
% 2.11/0.66    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k1_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 2.11/0.66    inference(superposition,[],[f103,f94])).
% 2.11/0.66  fof(f94,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.11/0.66    inference(forward_demodulation,[],[f91,f33])).
% 2.11/0.66  fof(f33,plain,(
% 2.11/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.11/0.66    inference(cnf_transformation,[],[f11])).
% 2.11/0.66  fof(f11,axiom,(
% 2.11/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.11/0.66  fof(f91,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_enumset1(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)),X1))) )),
% 2.11/0.66    inference(resolution,[],[f54,f32])).
% 2.11/0.66  fof(f32,plain,(
% 2.11/0.66    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f6])).
% 2.11/0.66  fof(f6,axiom,(
% 2.11/0.66    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.11/0.66  fof(f54,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k2_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 2.11/0.66    inference(definition_unfolding,[],[f42,f49])).
% 2.11/0.66  fof(f49,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 2.11/0.66    inference(definition_unfolding,[],[f38,f48])).
% 2.11/0.66  fof(f48,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.11/0.66    inference(definition_unfolding,[],[f37,f46])).
% 2.11/0.66  fof(f46,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f4])).
% 2.11/0.66  fof(f4,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.11/0.66  fof(f37,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f3])).
% 2.11/0.66  fof(f3,axiom,(
% 2.11/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.11/0.66  fof(f38,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f5])).
% 2.11/0.66  fof(f5,axiom,(
% 2.11/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.11/0.66  fof(f42,plain,(
% 2.11/0.66    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f22])).
% 2.40/0.66  fof(f22,plain,(
% 2.40/0.66    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f13])).
% 2.40/0.66  fof(f13,axiom,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 2.40/0.66  fof(f103,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.40/0.66    inference(superposition,[],[f94,f52])).
% 2.40/0.66  fof(f52,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 2.40/0.66    inference(definition_unfolding,[],[f36,f48,f48])).
% 2.40/0.66  fof(f36,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f2])).
% 2.40/0.66  fof(f2,axiom,(
% 2.40/0.66    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.40/0.66  fof(f2112,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 2.40/0.66    inference(forward_demodulation,[],[f1985,f735])).
% 2.40/0.66  fof(f735,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.40/0.66    inference(subsumption_resolution,[],[f105,f178])).
% 2.40/0.66  fof(f178,plain,(
% 2.40/0.66    ( ! [X6,X7] : (v1_relat_1(k7_relat_1(k6_relat_1(X7),X6))) )),
% 2.40/0.66    inference(superposition,[],[f100,f175])).
% 2.40/0.66  fof(f175,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k2_zfmisc_1(X1,X0)))) )),
% 2.40/0.66    inference(forward_demodulation,[],[f174,f64])).
% 2.40/0.66  fof(f64,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.40/0.66    inference(backward_demodulation,[],[f58,f59])).
% 2.40/0.66  fof(f59,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.40/0.66    inference(resolution,[],[f41,f32])).
% 2.40/0.66  fof(f41,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f21])).
% 2.40/0.66  fof(f21,plain,(
% 2.40/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f14])).
% 2.40/0.66  fof(f14,axiom,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.40/0.66  fof(f58,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.40/0.66    inference(resolution,[],[f40,f32])).
% 2.40/0.66  fof(f40,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 2.40/0.66    inference(cnf_transformation,[],[f20])).
% 2.40/0.66  fof(f20,plain,(
% 2.40/0.66    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f9])).
% 2.40/0.66  fof(f9,axiom,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 2.40/0.66  fof(f174,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k2_zfmisc_1(X1,X0)))) )),
% 2.40/0.66    inference(forward_demodulation,[],[f167,f33])).
% 2.40/0.66  fof(f167,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X1)),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0)))) )),
% 2.40/0.66    inference(resolution,[],[f99,f32])).
% 2.40/0.66  fof(f99,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 2.40/0.66    inference(backward_demodulation,[],[f55,f94])).
% 2.40/0.66  fof(f55,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 2.40/0.66    inference(definition_unfolding,[],[f43,f49])).
% 2.40/0.66  fof(f43,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f23])).
% 2.40/0.66  fof(f23,plain,(
% 2.40/0.66    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f10])).
% 2.40/0.66  fof(f10,axiom,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).
% 2.40/0.66  fof(f100,plain,(
% 2.40/0.66    ( ! [X0,X1] : (v1_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k6_relat_1(X0)),X1)))) )),
% 2.40/0.66    inference(backward_demodulation,[],[f57,f94])).
% 2.40/0.66  fof(f57,plain,(
% 2.40/0.66    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1)))) )),
% 2.40/0.66    inference(resolution,[],[f53,f32])).
% 2.40/0.66  fof(f53,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 2.40/0.66    inference(definition_unfolding,[],[f39,f49])).
% 2.40/0.66  fof(f39,plain,(
% 2.40/0.66    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f19])).
% 2.40/0.66  fof(f19,plain,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.40/0.66    inference(ennf_transformation,[],[f7])).
% 2.40/0.66  fof(f7,axiom,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.40/0.66  fof(f105,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.40/0.66    inference(resolution,[],[f97,f45])).
% 2.40/0.66  fof(f45,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f27])).
% 2.40/0.66  fof(f27,plain,(
% 2.40/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(flattening,[],[f26])).
% 2.40/0.66  fof(f26,plain,(
% 2.40/0.66    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f15])).
% 2.40/0.66  fof(f15,axiom,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 2.40/0.66  fof(f97,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 2.40/0.66    inference(backward_demodulation,[],[f51,f94])).
% 2.40/0.66  fof(f51,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 2.40/0.66    inference(definition_unfolding,[],[f35,f49])).
% 2.40/0.66  fof(f35,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f1])).
% 2.40/0.66  fof(f1,axiom,(
% 2.40/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.40/0.66  fof(f1985,plain,(
% 2.40/0.66    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 2.40/0.66    inference(superposition,[],[f109,f328])).
% 2.40/0.66  fof(f328,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)))) )),
% 2.40/0.66    inference(resolution,[],[f198,f32])).
% 2.40/0.66  fof(f198,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) )),
% 2.40/0.66    inference(forward_demodulation,[],[f56,f94])).
% 2.40/0.66  fof(f56,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 2.40/0.66    inference(definition_unfolding,[],[f47,f49])).
% 2.40/0.66  fof(f47,plain,(
% 2.40/0.66    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f28])).
% 2.40/0.66  fof(f28,plain,(
% 2.40/0.66    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.40/0.66    inference(ennf_transformation,[],[f8])).
% 2.40/0.66  fof(f8,axiom,(
% 2.40/0.66    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 2.40/0.66  fof(f109,plain,(
% 2.40/0.66    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X3),k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 2.40/0.66    inference(resolution,[],[f95,f83])).
% 2.40/0.66  fof(f83,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 2.40/0.66    inference(forward_demodulation,[],[f82,f59])).
% 2.40/0.66  fof(f82,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 2.40/0.66    inference(subsumption_resolution,[],[f81,f32])).
% 2.40/0.66  fof(f81,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.40/0.66    inference(superposition,[],[f44,f34])).
% 2.40/0.66  fof(f34,plain,(
% 2.40/0.66    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.40/0.66    inference(cnf_transformation,[],[f11])).
% 2.40/0.66  fof(f44,plain,(
% 2.40/0.66    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 2.40/0.66    inference(cnf_transformation,[],[f25])).
% 2.40/0.66  fof(f25,plain,(
% 2.40/0.66    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(flattening,[],[f24])).
% 2.40/0.66  fof(f24,plain,(
% 2.40/0.66    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f12])).
% 2.40/0.66  fof(f12,axiom,(
% 2.40/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.40/0.66  fof(f95,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)),X0)) )),
% 2.40/0.66    inference(backward_demodulation,[],[f69,f94])).
% 2.40/0.66  fof(f69,plain,(
% 2.40/0.66    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 2.40/0.66    inference(superposition,[],[f51,f52])).
% 2.40/0.66  fof(f102,plain,(
% 2.40/0.66    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 2.40/0.66    inference(backward_demodulation,[],[f65,f94])).
% 2.40/0.66  fof(f65,plain,(
% 2.40/0.66    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.40/0.66    inference(backward_demodulation,[],[f63,f64])).
% 2.40/0.66  fof(f63,plain,(
% 2.40/0.66    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 2.40/0.66    inference(backward_demodulation,[],[f50,f58])).
% 2.40/0.66  fof(f50,plain,(
% 2.40/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 2.40/0.66    inference(definition_unfolding,[],[f31,f49])).
% 2.40/0.66  fof(f31,plain,(
% 2.40/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.40/0.66    inference(cnf_transformation,[],[f30])).
% 2.40/0.66  fof(f30,plain,(
% 2.40/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.40/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f29])).
% 2.40/0.66  fof(f29,plain,(
% 2.40/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.40/0.66    introduced(choice_axiom,[])).
% 2.40/0.66  fof(f18,plain,(
% 2.40/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.40/0.66    inference(ennf_transformation,[],[f17])).
% 2.40/0.66  fof(f17,negated_conjecture,(
% 2.40/0.66    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.40/0.66    inference(negated_conjecture,[],[f16])).
% 2.40/0.66  fof(f16,conjecture,(
% 2.40/0.66    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.40/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 2.40/0.66  % SZS output end Proof for theBenchmark
% 2.40/0.66  % (2991)------------------------------
% 2.40/0.66  % (2991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.40/0.66  % (2991)Termination reason: Refutation
% 2.40/0.66  
% 2.40/0.66  % (2991)Memory used [KB]: 3837
% 2.40/0.66  % (2991)Time elapsed: 0.222 s
% 2.40/0.66  % (2991)------------------------------
% 2.40/0.66  % (2991)------------------------------
% 2.40/0.66  % (2970)Success in time 0.299 s
%------------------------------------------------------------------------------
