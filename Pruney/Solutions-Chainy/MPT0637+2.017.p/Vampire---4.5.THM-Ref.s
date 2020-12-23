%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 533 expanded)
%              Number of leaves         :   22 ( 165 expanded)
%              Depth                    :   19
%              Number of atoms          :  180 ( 712 expanded)
%              Number of equality atoms :   94 ( 432 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1057,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1010])).

fof(f1010,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(superposition,[],[f166,f838])).

fof(f838,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2)))) ),
    inference(forward_demodulation,[],[f801,f570])).

fof(f570,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) ),
    inference(forward_demodulation,[],[f562,f118])).

fof(f118,plain,(
    ! [X2,X3] : k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) = k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) ),
    inference(resolution,[],[f116,f105])).

fof(f105,plain,(
    ! [X2,X1] : r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X1) ),
    inference(forward_demodulation,[],[f104,f44])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f104,plain,(
    ! [X2,X1] : r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k1_relat_1(k6_relat_1(X1))) ),
    inference(subsumption_resolution,[],[f103,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f103,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f98,f42])).

fof(f98,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f47,f82])).

fof(f82,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f53,f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f115,f82])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f114,f42])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f56,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f562,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3)))))) ),
    inference(superposition,[],[f132,f252])).

fof(f252,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0))) ),
    inference(backward_demodulation,[],[f93,f251])).

fof(f251,plain,(
    ! [X6,X4,X5] : k7_relat_1(k8_relat_1(X4,k6_relat_1(X6)),X5) = k8_relat_1(X4,k8_relat_1(X6,k6_relat_1(X5))) ),
    inference(forward_demodulation,[],[f250,f82])).

fof(f250,plain,(
    ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k8_relat_1(X4,k6_relat_1(X6)),X5) ),
    inference(forward_demodulation,[],[f246,f93])).

fof(f246,plain,(
    ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6))) ),
    inference(resolution,[],[f236,f42])).

fof(f236,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X5)
      | k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k8_relat_1(X4,k6_relat_1(X6))) ) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).

fof(f93,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X0) ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f92,plain,(
    ! [X2,X1] : v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f90,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f59,f82])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f132,plain,(
    ! [X4,X3] : k8_relat_1(X3,k6_relat_1(X4)) = k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X4)))),k8_relat_1(X3,k6_relat_1(X4))) ),
    inference(resolution,[],[f124,f92])).

fof(f124,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k5_relat_1(k6_relat_1(k1_relat_1(X6)),X6) = X6 ) ),
    inference(resolution,[],[f57,f102])).

fof(f102,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f101,f44])).

fof(f101,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0))) ),
    inference(subsumption_resolution,[],[f100,f42])).

fof(f100,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f47,f79])).

fof(f79,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f77,f45])).

fof(f77,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f46,f42])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f801,plain,(
    ! [X2,X3] : k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2)))) = k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) ),
    inference(superposition,[],[f118,f794])).

fof(f794,plain,(
    ! [X2,X3] : k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))) = k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))) ),
    inference(superposition,[],[f790,f164])).

fof(f164,plain,(
    ! [X0,X1] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(backward_demodulation,[],[f73,f163])).

fof(f163,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f162,f87])).

fof(f87,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f85,f82])).

fof(f85,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f54,f42])).

fof(f162,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f159,f44])).

fof(f159,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) ),
    inference(resolution,[],[f76,f42])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(forward_demodulation,[],[f74,f73])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f70])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f790,plain,(
    ! [X0,X1] : k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) ),
    inference(superposition,[],[f164,f72])).

fof(f72,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f49,f69,f69])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f166,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f84,f163])).

fof(f84,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f75,f82])).

fof(f75,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f71,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f41,f70])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).

fof(f39,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:26:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (32758)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (32749)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (32750)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (32748)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (32760)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.48  % (32756)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (32757)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (32756)Refutation not found, incomplete strategy% (32756)------------------------------
% 0.20/0.48  % (32756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (32756)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (32756)Memory used [KB]: 10618
% 0.20/0.48  % (32756)Time elapsed: 0.062 s
% 0.20/0.48  % (32756)------------------------------
% 0.20/0.48  % (32756)------------------------------
% 0.20/0.48  % (32752)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (32746)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (32747)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (32753)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (32745)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (32751)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (32755)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (32761)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (32759)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (32754)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (32762)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.56  % (32754)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f1057,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f1010])).
% 0.20/0.56  fof(f1010,plain,(
% 0.20/0.56    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.20/0.56    inference(superposition,[],[f166,f838])).
% 0.20/0.56  fof(f838,plain,(
% 0.20/0.56    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2))))) )),
% 0.20/0.56    inference(forward_demodulation,[],[f801,f570])).
% 0.20/0.56  fof(f570,plain,(
% 0.20/0.56    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3)))))) )),
% 0.20/0.56    inference(forward_demodulation,[],[f562,f118])).
% 0.20/0.56  fof(f118,plain,(
% 0.20/0.56    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) = k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3)))))) )),
% 0.20/0.56    inference(resolution,[],[f116,f105])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),X1)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f104,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,axiom,(
% 0.20/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k1_relat_1(k6_relat_1(X1)))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f103,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f98,f42])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k8_relat_1(X2,k6_relat_1(X1))),k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.56    inference(superposition,[],[f47,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.56    inference(resolution,[],[f53,f42])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,axiom,(
% 0.20/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 0.20/0.56  fof(f116,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.56    inference(forward_demodulation,[],[f115,f82])).
% 0.20/0.56  fof(f115,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f114,f42])).
% 0.20/0.56  fof(f114,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.56    inference(superposition,[],[f56,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f33])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(flattening,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.56  fof(f562,plain,(
% 0.20/0.56    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))))))) )),
% 0.20/0.56    inference(superposition,[],[f132,f252])).
% 0.20/0.56  fof(f252,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k8_relat_1(X1,k8_relat_1(X2,k6_relat_1(X0)))) )),
% 0.20/0.56    inference(backward_demodulation,[],[f93,f251])).
% 0.20/0.56  fof(f251,plain,(
% 0.20/0.56    ( ! [X6,X4,X5] : (k7_relat_1(k8_relat_1(X4,k6_relat_1(X6)),X5) = k8_relat_1(X4,k8_relat_1(X6,k6_relat_1(X5)))) )),
% 0.20/0.56    inference(forward_demodulation,[],[f250,f82])).
% 0.20/0.56  fof(f250,plain,(
% 0.20/0.56    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k8_relat_1(X4,k6_relat_1(X6)),X5)) )),
% 0.20/0.56    inference(forward_demodulation,[],[f246,f93])).
% 0.20/0.56  fof(f246,plain,(
% 0.20/0.56    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k8_relat_1(X4,k6_relat_1(X6)))) )),
% 0.20/0.56    inference(resolution,[],[f236,f42])).
% 0.20/0.56  fof(f236,plain,(
% 0.20/0.56    ( ! [X6,X4,X5] : (~v1_relat_1(X5) | k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k8_relat_1(X4,k6_relat_1(X6)))) )),
% 0.20/0.56    inference(resolution,[],[f58,f42])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_relat_1)).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k8_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k8_relat_1(X1,k6_relat_1(X2)),X0)) )),
% 0.20/0.56    inference(resolution,[],[f92,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,axiom,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ( ! [X2,X1] : (v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f91,f42])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    ( ! [X2,X1] : (v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f90,f42])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    ( ! [X2,X1] : (v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.20/0.56    inference(superposition,[],[f59,f82])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.56    inference(flattening,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.56  fof(f132,plain,(
% 0.20/0.56    ( ! [X4,X3] : (k8_relat_1(X3,k6_relat_1(X4)) = k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X4)))),k8_relat_1(X3,k6_relat_1(X4)))) )),
% 0.20/0.56    inference(resolution,[],[f124,f92])).
% 0.20/0.56  fof(f124,plain,(
% 0.20/0.56    ( ! [X6] : (~v1_relat_1(X6) | k5_relat_1(k6_relat_1(k1_relat_1(X6)),X6) = X6) )),
% 0.20/0.56    inference(resolution,[],[f57,f102])).
% 1.73/0.58  fof(f102,plain,(
% 1.73/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.73/0.58    inference(forward_demodulation,[],[f101,f44])).
% 1.73/0.58  fof(f101,plain,(
% 1.73/0.58    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0)))) )),
% 1.73/0.58    inference(subsumption_resolution,[],[f100,f42])).
% 1.73/0.58  fof(f100,plain,(
% 1.73/0.58    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.73/0.58    inference(duplicate_literal_removal,[],[f97])).
% 1.73/0.58  fof(f97,plain,(
% 1.73/0.58    ( ! [X0] : (r1_tarski(k1_relat_1(k6_relat_1(X0)),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.73/0.58    inference(superposition,[],[f47,f79])).
% 1.73/0.58  fof(f79,plain,(
% 1.73/0.58    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.73/0.58    inference(forward_demodulation,[],[f77,f45])).
% 1.73/0.58  fof(f77,plain,(
% 1.73/0.58    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 1.73/0.58    inference(resolution,[],[f46,f42])).
% 1.73/0.58  fof(f46,plain,(
% 1.73/0.58    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.73/0.58    inference(cnf_transformation,[],[f26])).
% 1.73/0.58  fof(f26,plain,(
% 1.73/0.58    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.73/0.58    inference(ennf_transformation,[],[f20])).
% 1.73/0.58  fof(f20,axiom,(
% 1.73/0.58    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 1.73/0.58  fof(f57,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f35])).
% 1.73/0.58  fof(f35,plain,(
% 1.73/0.58    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.73/0.58    inference(flattening,[],[f34])).
% 1.73/0.58  fof(f34,plain,(
% 1.73/0.58    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.73/0.58    inference(ennf_transformation,[],[f18])).
% 1.73/0.58  fof(f18,axiom,(
% 1.73/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 1.73/0.58  fof(f801,plain,(
% 1.73/0.58    ( ! [X2,X3] : (k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2)))) = k8_relat_1(X3,k6_relat_1(k1_relat_1(k8_relat_1(X3,k6_relat_1(X2)))))) )),
% 1.73/0.58    inference(superposition,[],[f118,f794])).
% 1.73/0.58  fof(f794,plain,(
% 1.73/0.58    ( ! [X2,X3] : (k1_relat_1(k8_relat_1(X2,k6_relat_1(X3))) = k1_relat_1(k8_relat_1(X3,k6_relat_1(X2)))) )),
% 1.73/0.58    inference(superposition,[],[f790,f164])).
% 1.73/0.58  fof(f164,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 1.73/0.58    inference(backward_demodulation,[],[f73,f163])).
% 1.73/0.58  fof(f163,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 1.73/0.58    inference(forward_demodulation,[],[f162,f87])).
% 1.73/0.58  fof(f87,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.73/0.58    inference(forward_demodulation,[],[f85,f82])).
% 1.73/0.58  fof(f85,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.73/0.58    inference(resolution,[],[f54,f42])).
% 1.73/0.58  fof(f162,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.73/0.58    inference(forward_demodulation,[],[f159,f44])).
% 1.73/0.58  fof(f159,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) )),
% 1.73/0.58    inference(resolution,[],[f76,f42])).
% 1.73/0.58  fof(f76,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 1.73/0.58    inference(forward_demodulation,[],[f74,f73])).
% 1.73/0.58  fof(f74,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f55,f70])).
% 1.73/0.58  fof(f70,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.73/0.58    inference(definition_unfolding,[],[f50,f69])).
% 1.73/0.58  fof(f69,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f51,f68])).
% 1.73/0.58  fof(f68,plain,(
% 1.73/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f60,f67])).
% 1.73/0.58  fof(f67,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f61,f66])).
% 1.73/0.58  fof(f66,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f62,f65])).
% 1.73/0.58  fof(f65,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f63,f64])).
% 1.73/0.58  fof(f64,plain,(
% 1.73/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f8])).
% 1.73/0.58  fof(f8,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.73/0.58  fof(f63,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f7])).
% 1.73/0.58  fof(f7,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.73/0.58  fof(f62,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f6])).
% 1.73/0.58  fof(f6,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.73/0.58  fof(f61,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f5])).
% 1.73/0.58  fof(f5,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.73/0.58  fof(f60,plain,(
% 1.73/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f4])).
% 1.73/0.58  fof(f4,axiom,(
% 1.73/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.73/0.58  fof(f51,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f3])).
% 1.73/0.58  fof(f3,axiom,(
% 1.73/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.58  fof(f50,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.73/0.58    inference(cnf_transformation,[],[f9])).
% 1.73/0.58  fof(f9,axiom,(
% 1.73/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.73/0.58  fof(f55,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f31])).
% 1.73/0.58  fof(f31,plain,(
% 1.73/0.58    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.73/0.58    inference(ennf_transformation,[],[f21])).
% 1.73/0.58  fof(f21,axiom,(
% 1.73/0.58    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 1.73/0.58  fof(f73,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.73/0.58    inference(definition_unfolding,[],[f52,f70])).
% 1.73/0.58  fof(f52,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f1])).
% 1.73/0.58  fof(f1,axiom,(
% 1.73/0.58    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.73/0.58  fof(f790,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) )),
% 1.73/0.58    inference(superposition,[],[f164,f72])).
% 1.73/0.58  fof(f72,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f49,f69,f69])).
% 1.73/0.58  fof(f49,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f2])).
% 1.73/0.58  fof(f2,axiom,(
% 1.73/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.73/0.58  fof(f166,plain,(
% 1.73/0.58    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k1_relat_1(k8_relat_1(sK0,k6_relat_1(sK1))))),
% 1.73/0.58    inference(backward_demodulation,[],[f84,f163])).
% 1.73/0.58  fof(f84,plain,(
% 1.73/0.58    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.73/0.58    inference(backward_demodulation,[],[f75,f82])).
% 1.73/0.58  fof(f75,plain,(
% 1.73/0.58    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.73/0.58    inference(backward_demodulation,[],[f71,f73])).
% 1.73/0.58  fof(f71,plain,(
% 1.73/0.58    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.73/0.58    inference(definition_unfolding,[],[f41,f70])).
% 1.73/0.58  fof(f41,plain,(
% 1.73/0.58    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.73/0.58    inference(cnf_transformation,[],[f40])).
% 1.73/0.58  fof(f40,plain,(
% 1.73/0.58    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.73/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).
% 1.73/0.58  fof(f39,plain,(
% 1.73/0.58    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.73/0.58    introduced(choice_axiom,[])).
% 1.73/0.58  fof(f25,plain,(
% 1.73/0.58    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.73/0.58    inference(ennf_transformation,[],[f24])).
% 1.73/0.58  fof(f24,negated_conjecture,(
% 1.73/0.58    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.73/0.58    inference(negated_conjecture,[],[f23])).
% 1.73/0.58  fof(f23,conjecture,(
% 1.73/0.58    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.73/0.58  % SZS output end Proof for theBenchmark
% 1.73/0.58  % (32754)------------------------------
% 1.73/0.58  % (32754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.58  % (32754)Termination reason: Refutation
% 1.73/0.58  
% 1.73/0.58  % (32754)Memory used [KB]: 11257
% 1.73/0.58  % (32754)Time elapsed: 0.147 s
% 1.73/0.58  % (32754)------------------------------
% 1.73/0.58  % (32754)------------------------------
% 1.73/0.58  % (32744)Success in time 0.218 s
%------------------------------------------------------------------------------
