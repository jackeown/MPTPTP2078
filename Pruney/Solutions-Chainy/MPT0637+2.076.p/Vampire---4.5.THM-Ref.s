%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 (1050 expanded)
%              Number of leaves         :   20 ( 312 expanded)
%              Depth                    :   22
%              Number of atoms          :  176 (1791 expanded)
%              Number of equality atoms :   88 ( 663 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f827,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f68,f121,f167,f774])).

fof(f774,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f758])).

fof(f758,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f166,f757])).

fof(f757,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) ),
    inference(backward_demodulation,[],[f189,f756])).

fof(f756,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) ),
    inference(forward_demodulation,[],[f755,f113])).

fof(f113,plain,(
    ! [X0,X1] : k6_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))))) ),
    inference(backward_demodulation,[],[f80,f112])).

fof(f112,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) ),
    inference(forward_demodulation,[],[f108,f34])).

fof(f34,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f108,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k2_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0)) ),
    inference(resolution,[],[f50,f31])).

fof(f31,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f80,plain,(
    ! [X0,X1] : k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ),
    inference(resolution,[],[f79,f49])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(global_subsumption,[],[f31,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f77,f61])).

fof(f61,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f40,f31])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f42,f34])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f755,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))))) ),
    inference(forward_demodulation,[],[f727,f160])).

fof(f160,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X3,k6_relat_1(X2)) ),
    inference(superposition,[],[f155,f90])).

fof(f90,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f89,f61])).

fof(f89,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f88,f61])).

fof(f88,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f85,f30])).

fof(f30,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f85,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f84,f31])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f81,f30])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f36,f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f155,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[],[f142,f127])).

fof(f127,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(global_subsumption,[],[f73,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k8_relat_1(X0,k6_relat_1(X1)))
      | ~ v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f123,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X0)) ),
    inference(resolution,[],[f73,f40])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X1))
      | ~ v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f114,f42])).

fof(f114,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0) ),
    inference(backward_demodulation,[],[f49,f112])).

fof(f73,plain,(
    ! [X2,X1] : v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(global_subsumption,[],[f31,f72])).

fof(f72,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(global_subsumption,[],[f31,f71])).

fof(f71,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f44,f61])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f142,plain,(
    ! [X6,X7,X5] : k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) = k4_relat_1(k8_relat_1(X6,k8_relat_1(X7,k6_relat_1(X5)))) ),
    inference(backward_demodulation,[],[f93,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(forward_demodulation,[],[f137,f61])).

fof(f137,plain,(
    ! [X2,X0,X1] : k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2))) ),
    inference(resolution,[],[f104,f31])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),X0)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f43,f31])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(f93,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) ),
    inference(forward_demodulation,[],[f92,f74])).

fof(f92,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X6)),k6_relat_1(X5)) ),
    inference(forward_demodulation,[],[f87,f90])).

fof(f87,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k4_relat_1(k8_relat_1(X6,k6_relat_1(X7))),k6_relat_1(X5)) ),
    inference(resolution,[],[f84,f73])).

fof(f727,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k6_relat_1(X3))) ),
    inference(superposition,[],[f712,f198])).

fof(f198,plain,(
    ! [X4,X5,X3] : k8_relat_1(X4,k8_relat_1(X5,k6_relat_1(X3))) = k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(X3))) ),
    inference(superposition,[],[f174,f141])).

fof(f174,plain,(
    ! [X14,X15,X16] : k8_relat_1(X14,k8_relat_1(X15,k6_relat_1(X16))) = k5_relat_1(k6_relat_1(X16),k8_relat_1(X15,k6_relat_1(X14))) ),
    inference(superposition,[],[f141,f160])).

fof(f712,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(superposition,[],[f75,f74])).

fof(f75,plain,(
    ! [X4,X3] : k8_relat_1(X3,k6_relat_1(X4)) = k5_relat_1(k8_relat_1(X3,k6_relat_1(X4)),k6_relat_1(k2_relat_1(k8_relat_1(X3,k6_relat_1(X4))))) ),
    inference(resolution,[],[f73,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f189,plain,(
    ! [X2,X3] : k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) = k8_relat_1(X2,k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) ),
    inference(resolution,[],[f172,f79])).

fof(f172,plain,(
    ! [X10,X11] : r1_tarski(k2_relat_1(k8_relat_1(X11,k6_relat_1(X10))),X11) ),
    inference(superposition,[],[f114,f160])).

fof(f166,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl2_4
  <=> k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f167,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f162,f118,f164])).

fof(f118,plain,
    ( spl2_3
  <=> k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f162,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1))))
    | spl2_3 ),
    inference(backward_demodulation,[],[f120,f160])).

fof(f120,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0))))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f121,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f116,f65,f118])).

fof(f65,plain,
    ( spl2_2
  <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k8_relat_1(sK0,k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f116,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0))))
    | spl2_2 ),
    inference(backward_demodulation,[],[f67,f112])).

fof(f67,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f68,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f63,f52,f65])).

fof(f52,plain,
    ( spl2_1
  <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))
    | spl2_1 ),
    inference(backward_demodulation,[],[f54,f61])).

fof(f54,plain,
    ( k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f55,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f48,f52])).

fof(f48,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f29,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).

fof(f27,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:48:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.40  % (24275)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.44  % (24275)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f827,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f55,f68,f121,f167,f774])).
% 0.22/0.44  fof(f774,plain,(
% 0.22/0.44    spl2_4),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f758])).
% 0.22/0.44  fof(f758,plain,(
% 0.22/0.44    $false | spl2_4),
% 0.22/0.44    inference(subsumption_resolution,[],[f166,f757])).
% 0.22/0.44  fof(f757,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))))) )),
% 0.22/0.44    inference(backward_demodulation,[],[f189,f756])).
% 0.22/0.44  fof(f756,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f755,f113])).
% 0.22/0.44  fof(f113,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) = k8_relat_1(X0,k6_relat_1(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))))) )),
% 0.22/0.44    inference(backward_demodulation,[],[f80,f112])).
% 0.22/0.44  fof(f112,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k2_enumset1(X1,X1,X1,X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f108,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.44  fof(f108,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k2_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0))) )),
% 0.22/0.44    inference(resolution,[],[f50,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,axiom,(
% 0.22/0.44    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f41,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f38,f46])).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f39,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.44  fof(f80,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k8_relat_1(X0,k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) )),
% 0.22/0.44    inference(resolution,[],[f79,f49])).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f37,f47])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.44  fof(f79,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 0.22/0.44    inference(global_subsumption,[],[f31,f78])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) | ~r1_tarski(X0,X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f77,f61])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.22/0.44    inference(resolution,[],[f40,f31])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f20])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.44  fof(f77,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.44    inference(superposition,[],[f42,f34])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f23])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.22/0.44  fof(f755,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))))))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f727,f160])).
% 0.22/0.44  fof(f160,plain,(
% 0.22/0.44    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X3,k6_relat_1(X2))) )),
% 0.22/0.44    inference(superposition,[],[f155,f90])).
% 0.22/0.44  fof(f90,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f89,f61])).
% 0.22/0.44  fof(f89,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.22/0.44    inference(forward_demodulation,[],[f88,f61])).
% 0.22/0.45  fof(f88,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f85,f30])).
% 0.22/0.45  fof(f30,plain,(
% 0.22/0.45    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,axiom,(
% 0.22/0.45    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 0.22/0.45  fof(f85,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 0.22/0.45    inference(resolution,[],[f84,f31])).
% 0.22/0.45  fof(f84,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f81,f30])).
% 0.22/0.45  fof(f81,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 0.22/0.45    inference(resolution,[],[f36,f31])).
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.22/0.45  fof(f155,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.22/0.45    inference(superposition,[],[f142,f127])).
% 0.22/0.45  fof(f127,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.22/0.45    inference(global_subsumption,[],[f73,f126])).
% 0.22/0.45  fof(f126,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,k8_relat_1(X0,k6_relat_1(X1))) | ~v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f123,f74])).
% 0.22/0.45  fof(f74,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X2)),k6_relat_1(X0))) )),
% 0.22/0.45    inference(resolution,[],[f73,f40])).
% 0.22/0.45  fof(f123,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X1)) | ~v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.22/0.45    inference(resolution,[],[f114,f42])).
% 0.22/0.45  fof(f114,plain,(
% 0.22/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0)) )),
% 0.22/0.45    inference(backward_demodulation,[],[f49,f112])).
% 0.22/0.45  fof(f73,plain,(
% 0.22/0.45    ( ! [X2,X1] : (v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))) )),
% 0.22/0.45    inference(global_subsumption,[],[f31,f72])).
% 0.22/0.45  fof(f72,plain,(
% 0.22/0.45    ( ! [X2,X1] : (v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.22/0.45    inference(global_subsumption,[],[f31,f71])).
% 0.22/0.45  fof(f71,plain,(
% 0.22/0.45    ( ! [X2,X1] : (v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 0.22/0.45    inference(superposition,[],[f44,f61])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.45    inference(flattening,[],[f25])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.45  fof(f142,plain,(
% 0.22/0.45    ( ! [X6,X7,X5] : (k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) = k4_relat_1(k8_relat_1(X6,k8_relat_1(X7,k6_relat_1(X5))))) )),
% 0.22/0.45    inference(backward_demodulation,[],[f93,f141])).
% 0.22/0.45  fof(f141,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k8_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f137,f61])).
% 0.22/0.45  fof(f137,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k8_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k5_relat_1(k6_relat_1(X1),k8_relat_1(X0,k6_relat_1(X2)))) )),
% 0.22/0.45    inference(resolution,[],[f104,f31])).
% 0.22/0.45  fof(f104,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k8_relat_1(X1,k5_relat_1(k6_relat_1(X2),X0)) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X1,X0))) )),
% 0.22/0.45    inference(resolution,[],[f43,f31])).
% 0.22/0.45  fof(f43,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).
% 0.22/0.45  fof(f93,plain,(
% 0.22/0.45    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6)))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f92,f74])).
% 0.22/0.45  fof(f92,plain,(
% 0.22/0.45    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X6)),k6_relat_1(X5))) )),
% 0.22/0.45    inference(forward_demodulation,[],[f87,f90])).
% 0.22/0.45  fof(f87,plain,(
% 0.22/0.45    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k4_relat_1(k8_relat_1(X6,k6_relat_1(X7))),k6_relat_1(X5))) )),
% 0.22/0.45    inference(resolution,[],[f84,f73])).
% 0.22/0.45  fof(f727,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k6_relat_1(X3)))) )),
% 0.22/0.45    inference(superposition,[],[f712,f198])).
% 0.22/0.45  fof(f198,plain,(
% 0.22/0.45    ( ! [X4,X5,X3] : (k8_relat_1(X4,k8_relat_1(X5,k6_relat_1(X3))) = k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(X3)))) )),
% 0.22/0.45    inference(superposition,[],[f174,f141])).
% 0.22/0.45  fof(f174,plain,(
% 0.22/0.45    ( ! [X14,X15,X16] : (k8_relat_1(X14,k8_relat_1(X15,k6_relat_1(X16))) = k5_relat_1(k6_relat_1(X16),k8_relat_1(X15,k6_relat_1(X14)))) )),
% 0.22/0.45    inference(superposition,[],[f141,f160])).
% 0.22/0.45  fof(f712,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.22/0.45    inference(superposition,[],[f75,f74])).
% 0.22/0.45  fof(f75,plain,(
% 0.22/0.45    ( ! [X4,X3] : (k8_relat_1(X3,k6_relat_1(X4)) = k5_relat_1(k8_relat_1(X3,k6_relat_1(X4)),k6_relat_1(k2_relat_1(k8_relat_1(X3,k6_relat_1(X4)))))) )),
% 0.22/0.45    inference(resolution,[],[f73,f35])).
% 0.22/0.45  fof(f35,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.22/0.45    inference(cnf_transformation,[],[f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,axiom,(
% 0.22/0.45    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.22/0.45  fof(f189,plain,(
% 0.22/0.45    ( ! [X2,X3] : (k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) = k8_relat_1(X2,k6_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))))) )),
% 0.22/0.45    inference(resolution,[],[f172,f79])).
% 0.22/0.45  fof(f172,plain,(
% 0.22/0.45    ( ! [X10,X11] : (r1_tarski(k2_relat_1(k8_relat_1(X11,k6_relat_1(X10))),X11)) )),
% 0.22/0.45    inference(superposition,[],[f114,f160])).
% 0.22/0.45  fof(f166,plain,(
% 0.22/0.45    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) | spl2_4),
% 0.22/0.45    inference(avatar_component_clause,[],[f164])).
% 0.22/0.45  fof(f164,plain,(
% 0.22/0.45    spl2_4 <=> k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.45  fof(f167,plain,(
% 0.22/0.45    ~spl2_4 | spl2_3),
% 0.22/0.45    inference(avatar_split_clause,[],[f162,f118,f164])).
% 0.22/0.45  fof(f118,plain,(
% 0.22/0.45    spl2_3 <=> k8_relat_1(sK0,k6_relat_1(sK1)) = k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0))))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.45  fof(f162,plain,(
% 0.22/0.45    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) | spl2_3),
% 0.22/0.45    inference(backward_demodulation,[],[f120,f160])).
% 0.22/0.45  fof(f120,plain,(
% 0.22/0.45    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) | spl2_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f118])).
% 0.22/0.45  fof(f121,plain,(
% 0.22/0.45    ~spl2_3 | spl2_2),
% 0.22/0.45    inference(avatar_split_clause,[],[f116,f65,f118])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    spl2_2 <=> k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) = k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.45  fof(f116,plain,(
% 0.22/0.45    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) | spl2_2),
% 0.22/0.45    inference(backward_demodulation,[],[f67,f112])).
% 0.22/0.45  fof(f67,plain,(
% 0.22/0.45    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f65])).
% 0.22/0.45  fof(f68,plain,(
% 0.22/0.45    ~spl2_2 | spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f63,f52,f65])).
% 0.22/0.45  fof(f52,plain,(
% 0.22/0.45    spl2_1 <=> k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) = k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) | spl2_1),
% 0.22/0.45    inference(backward_demodulation,[],[f54,f61])).
% 0.22/0.45  fof(f54,plain,(
% 0.22/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) | spl2_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f52])).
% 0.22/0.45  fof(f55,plain,(
% 0.22/0.45    ~spl2_1),
% 0.22/0.45    inference(avatar_split_clause,[],[f48,f52])).
% 0.22/0.45  fof(f48,plain,(
% 0.22/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.22/0.45    inference(definition_unfolding,[],[f29,f47])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f28])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.45    inference(negated_conjecture,[],[f15])).
% 0.22/0.45  fof(f15,conjecture,(
% 0.22/0.45    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (24275)------------------------------
% 0.22/0.45  % (24275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (24275)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (24275)Memory used [KB]: 6780
% 0.22/0.45  % (24275)Time elapsed: 0.049 s
% 0.22/0.45  % (24275)------------------------------
% 0.22/0.45  % (24275)------------------------------
% 0.22/0.45  % (24264)Success in time 0.088 s
%------------------------------------------------------------------------------
