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
% DateTime   : Thu Dec  3 12:52:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 (1282 expanded)
%              Number of leaves         :   17 ( 365 expanded)
%              Depth                    :   21
%              Number of atoms          :  202 (2188 expanded)
%              Number of equality atoms :   82 ( 919 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2193,f2056])).

fof(f2056,plain,(
    ! [X24,X23] : k6_relat_1(k3_xboole_0(X23,X24)) = k6_relat_1(k3_xboole_0(X24,X23)) ),
    inference(subsumption_resolution,[],[f2055,f1949])).

fof(f1949,plain,(
    ! [X17,X18] : r1_tarski(k6_relat_1(k3_xboole_0(X18,X17)),k6_relat_1(k3_xboole_0(X17,X18))) ),
    inference(backward_demodulation,[],[f287,f1941])).

fof(f1941,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k3_xboole_0(X1,X0)) ),
    inference(subsumption_resolution,[],[f1924,f503])).

fof(f503,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k3_xboole_0(X3,X2))) ),
    inference(superposition,[],[f287,f188])).

fof(f188,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f68,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1924,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k3_xboole_0(X1,X0))
      | ~ r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(X1,X0))) ) ),
    inference(resolution,[],[f1707,f409])).

fof(f409,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X7,X6)
      | X6 = X7
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f190,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f190,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f188,f61])).

fof(f1707,plain,(
    ! [X26,X25] : r1_tarski(k6_relat_1(k3_xboole_0(X25,X26)),k7_relat_1(k6_relat_1(X26),X25)) ),
    inference(forward_demodulation,[],[f1706,f1214])).

fof(f1214,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k6_relat_1(k3_xboole_0(X5,X6)),X5) ),
    inference(forward_demodulation,[],[f1213,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1213,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6)),X5) ),
    inference(forward_demodulation,[],[f1212,f401])).

fof(f401,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(backward_demodulation,[],[f303,f400])).

fof(f400,plain,(
    ! [X15,X16] : k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)) = k7_relat_1(k6_relat_1(X16),X15) ),
    inference(forward_demodulation,[],[f399,f122])).

fof(f122,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X5) ),
    inference(forward_demodulation,[],[f121,f90])).

fof(f90,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f89,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f81,f43])).

fof(f81,plain,(
    ! [X2,X3] :
      ( k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)
      | ~ v1_relat_1(k6_relat_1(X3))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f56,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f121,plain,(
    ! [X6,X5] : k8_relat_1(X6,k6_relat_1(X5)) = k7_relat_1(k8_relat_1(X6,k6_relat_1(X5)),X5) ),
    inference(subsumption_resolution,[],[f117,f43])).

fof(f117,plain,(
    ! [X6,X5] :
      ( k8_relat_1(X6,k6_relat_1(X5)) = k7_relat_1(k8_relat_1(X6,k6_relat_1(X5)),X5)
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f64,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(subsumption_resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f47,f45])).

fof(f47,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f399,plain,(
    ! [X15,X16] : k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)) = k7_relat_1(k7_relat_1(k6_relat_1(X16),X15),X15) ),
    inference(forward_demodulation,[],[f398,f90])).

fof(f398,plain,(
    ! [X15,X16] : k7_relat_1(k8_relat_1(X16,k6_relat_1(X15)),X15) = k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)) ),
    inference(subsumption_resolution,[],[f383,f43])).

fof(f383,plain,(
    ! [X15,X16] :
      ( k7_relat_1(k8_relat_1(X16,k6_relat_1(X15)),X15) = k5_relat_1(k6_relat_1(X15),k6_relat_1(X16))
      | ~ v1_relat_1(k6_relat_1(X15)) ) ),
    inference(superposition,[],[f168,f67])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f167,f43])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f60,f55])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f303,plain,(
    ! [X2,X3] : k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f302,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f302,plain,(
    ! [X2,X3] : k5_relat_1(k6_relat_1(X3),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(subsumption_resolution,[],[f301,f43])).

fof(f301,plain,(
    ! [X2,X3] :
      ( k5_relat_1(k6_relat_1(X3),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f297,f43])).

fof(f297,plain,(
    ! [X2,X3] :
      ( k5_relat_1(k6_relat_1(X3),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f153,f56])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f48,f44])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f1212,plain,(
    ! [X6,X5] : k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6)),X5) = k4_relat_1(k7_relat_1(k6_relat_1(X5),X6)) ),
    inference(subsumption_resolution,[],[f1197,f43])).

fof(f1197,plain,(
    ! [X6,X5] :
      ( k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6)),X5) = k4_relat_1(k7_relat_1(k6_relat_1(X5),X6))
      | ~ v1_relat_1(k6_relat_1(X5)) ) ),
    inference(superposition,[],[f401,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f65,f47])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1706,plain,(
    ! [X26,X25] : r1_tarski(k6_relat_1(k3_xboole_0(X25,X26)),k7_relat_1(k6_relat_1(k3_xboole_0(X25,X26)),X25)) ),
    inference(subsumption_resolution,[],[f1666,f43])).

fof(f1666,plain,(
    ! [X26,X25] :
      ( r1_tarski(k6_relat_1(k3_xboole_0(X25,X26)),k7_relat_1(k6_relat_1(k3_xboole_0(X25,X26)),X25))
      | ~ v1_relat_1(k6_relat_1(k3_xboole_0(X25,X26))) ) ),
    inference(superposition,[],[f149,f67])).

fof(f149,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k7_relat_1(X4,k3_xboole_0(X5,X6)),k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f146,f95])).

fof(f95,plain,(
    ! [X6,X7] :
      ( v1_relat_1(k7_relat_1(X7,X6))
      | ~ v1_relat_1(X7) ) ),
    inference(subsumption_resolution,[],[f87,f43])).

fof(f87,plain,(
    ! [X6,X7] :
      ( v1_relat_1(k7_relat_1(X7,X6))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X6,X7] :
      ( v1_relat_1(k7_relat_1(X7,X6))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(k6_relat_1(X6))
      | ~ v1_relat_1(X7) ) ),
    inference(superposition,[],[f62,f56])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f146,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(k7_relat_1(X4,k3_xboole_0(X5,X6)),k7_relat_1(X4,X5))
      | ~ v1_relat_1(k7_relat_1(X4,X5))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f88,f65])).

fof(f88,plain,(
    ! [X4,X5] :
      ( r1_tarski(k7_relat_1(X5,X4),X5)
      | ~ v1_relat_1(X5) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X4,X5] :
      ( r1_tarski(k7_relat_1(X5,X4),X5)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f58,f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f287,plain,(
    ! [X17,X18] : r1_tarski(k7_relat_1(k6_relat_1(X17),X18),k6_relat_1(k3_xboole_0(X17,X18))) ),
    inference(forward_demodulation,[],[f286,f45])).

fof(f286,plain,(
    ! [X17,X18] : r1_tarski(k7_relat_1(k6_relat_1(X17),X18),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X17)),X18))) ),
    inference(subsumption_resolution,[],[f274,f43])).

fof(f274,plain,(
    ! [X17,X18] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X17),X18),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X17)),X18)))
      | ~ v1_relat_1(k6_relat_1(X17)) ) ),
    inference(superposition,[],[f94,f137])).

fof(f94,plain,(
    ! [X2,X3] : r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) ),
    inference(subsumption_resolution,[],[f93,f43])).

fof(f93,plain,(
    ! [X2,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,(
    ! [X2,X3] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f57,f56])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2055,plain,(
    ! [X24,X23] :
      ( ~ r1_tarski(k6_relat_1(k3_xboole_0(X23,X24)),k6_relat_1(k3_xboole_0(X24,X23)))
      | k6_relat_1(k3_xboole_0(X23,X24)) = k6_relat_1(k3_xboole_0(X24,X23)) ) ),
    inference(forward_demodulation,[],[f1970,f1941])).

fof(f1970,plain,(
    ! [X24,X23] :
      ( k6_relat_1(k3_xboole_0(X23,X24)) = k6_relat_1(k3_xboole_0(X24,X23))
      | ~ r1_tarski(k6_relat_1(k3_xboole_0(X23,X24)),k7_relat_1(k6_relat_1(X23),X24)) ) ),
    inference(backward_demodulation,[],[f1086,f1941])).

fof(f1086,plain,(
    ! [X24,X23] :
      ( k7_relat_1(k6_relat_1(X23),X24) = k6_relat_1(k3_xboole_0(X23,X24))
      | ~ r1_tarski(k6_relat_1(k3_xboole_0(X23,X24)),k7_relat_1(k6_relat_1(X23),X24)) ) ),
    inference(resolution,[],[f409,f287])).

fof(f2193,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f77,f1942])).

fof(f1942,plain,(
    ! [X2,X3] : k8_relat_1(X3,k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f90,f1941])).

fof(f77,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f71,f43])).

fof(f71,plain,
    ( k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))
    | ~ v1_relat_1(k6_relat_1(sK1)) ),
    inference(superposition,[],[f42,f55])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f40])).

fof(f40,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (17025)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (17022)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (17028)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (17025)Refutation not found, incomplete strategy% (17025)------------------------------
% 0.20/0.48  % (17025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17017)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (17025)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (17025)Memory used [KB]: 10618
% 0.20/0.48  % (17025)Time elapsed: 0.050 s
% 0.20/0.48  % (17025)------------------------------
% 0.20/0.48  % (17025)------------------------------
% 0.20/0.48  % (17020)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (17019)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (17014)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (17018)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (17030)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (17016)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (17015)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (17029)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (17027)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (17023)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (17031)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.52  % (17026)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.52  % (17021)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.54  % (17024)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.54  % (17017)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f2202,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f2193,f2056])).
% 0.20/0.54  fof(f2056,plain,(
% 0.20/0.54    ( ! [X24,X23] : (k6_relat_1(k3_xboole_0(X23,X24)) = k6_relat_1(k3_xboole_0(X24,X23))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f2055,f1949])).
% 0.20/0.54  fof(f1949,plain,(
% 0.20/0.54    ( ! [X17,X18] : (r1_tarski(k6_relat_1(k3_xboole_0(X18,X17)),k6_relat_1(k3_xboole_0(X17,X18)))) )),
% 0.20/0.54    inference(backward_demodulation,[],[f287,f1941])).
% 0.20/0.54  fof(f1941,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k3_xboole_0(X1,X0))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f1924,f503])).
% 0.20/0.54  fof(f503,plain,(
% 0.20/0.54    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X3),k6_relat_1(k3_xboole_0(X3,X2)))) )),
% 0.20/0.54    inference(superposition,[],[f287,f188])).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 0.20/0.54    inference(superposition,[],[f68,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 0.20/0.54    inference(superposition,[],[f53,f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.54  fof(f1924,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(k3_xboole_0(X1,X0)) | ~r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(k3_xboole_0(X1,X0)))) )),
% 0.20/0.54    inference(resolution,[],[f1707,f409])).
% 0.20/0.54  fof(f409,plain,(
% 0.20/0.54    ( ! [X6,X7] : (~r1_tarski(X7,X6) | X6 = X7 | ~r1_tarski(X6,X7)) )),
% 0.20/0.54    inference(superposition,[],[f190,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f35])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.54  fof(f190,plain,(
% 0.20/0.54    ( ! [X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~r1_tarski(X4,X5)) )),
% 0.20/0.54    inference(superposition,[],[f188,f61])).
% 0.20/0.54  fof(f1707,plain,(
% 0.20/0.54    ( ! [X26,X25] : (r1_tarski(k6_relat_1(k3_xboole_0(X25,X26)),k7_relat_1(k6_relat_1(X26),X25))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f1706,f1214])).
% 0.20/0.54  fof(f1214,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k6_relat_1(k3_xboole_0(X5,X6)),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f1213,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.54  fof(f1213,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6)),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f1212,f401])).
% 0.20/0.54  fof(f401,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 0.20/0.54    inference(backward_demodulation,[],[f303,f400])).
% 0.20/0.54  fof(f400,plain,(
% 0.20/0.54    ( ! [X15,X16] : (k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)) = k7_relat_1(k6_relat_1(X16),X15)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f399,f122])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(X6),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f121,f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f89,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f81,f43])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k7_relat_1(k6_relat_1(X3),X2) | ~v1_relat_1(k6_relat_1(X3)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 0.20/0.54    inference(superposition,[],[f56,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k8_relat_1(X6,k6_relat_1(X5)) = k7_relat_1(k8_relat_1(X6,k6_relat_1(X5)),X5)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f117,f43])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k8_relat_1(X6,k6_relat_1(X5)) = k7_relat_1(k8_relat_1(X6,k6_relat_1(X5)),X5) | ~v1_relat_1(k6_relat_1(X5))) )),
% 0.20/0.54    inference(superposition,[],[f64,f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f66,f43])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.54    inference(superposition,[],[f47,f45])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 0.20/0.54  fof(f399,plain,(
% 0.20/0.54    ( ! [X15,X16] : (k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)) = k7_relat_1(k7_relat_1(k6_relat_1(X16),X15),X15)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f398,f90])).
% 0.20/0.54  fof(f398,plain,(
% 0.20/0.54    ( ! [X15,X16] : (k7_relat_1(k8_relat_1(X16,k6_relat_1(X15)),X15) = k5_relat_1(k6_relat_1(X15),k6_relat_1(X16))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f383,f43])).
% 0.20/0.54  fof(f383,plain,(
% 0.20/0.54    ( ! [X15,X16] : (k7_relat_1(k8_relat_1(X16,k6_relat_1(X15)),X15) = k5_relat_1(k6_relat_1(X15),k6_relat_1(X16)) | ~v1_relat_1(k6_relat_1(X15))) )),
% 0.20/0.54    inference(superposition,[],[f168,f67])).
% 0.20/0.54  fof(f168,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f167,f43])).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f155])).
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_relat_1(k7_relat_1(X0,X2),k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X1,X0),X2) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(superposition,[],[f60,f55])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) = k5_relat_1(k6_relat_1(X3),k6_relat_1(X2))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f302,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,axiom,(
% 0.20/0.54    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k5_relat_1(k6_relat_1(X3),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f301,f43])).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k5_relat_1(k6_relat_1(X3),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f297,f43])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k5_relat_1(k6_relat_1(X3),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.20/0.54    inference(superposition,[],[f153,f56])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f150,f43])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X1,k6_relat_1(X0))) = k5_relat_1(k6_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(superposition,[],[f48,f44])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.54  fof(f1212,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6)),X5) = k4_relat_1(k7_relat_1(k6_relat_1(X5),X6))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f1197,f43])).
% 0.20/0.54  fof(f1197,plain,(
% 0.20/0.54    ( ! [X6,X5] : (k7_relat_1(k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X5)),X6)),X5) = k4_relat_1(k7_relat_1(k6_relat_1(X5),X6)) | ~v1_relat_1(k6_relat_1(X5))) )),
% 0.20/0.54    inference(superposition,[],[f401,f137])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f126])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k7_relat_1(X0,k3_xboole_0(k1_relat_1(X0),X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(superposition,[],[f65,f47])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 0.20/0.54  fof(f1706,plain,(
% 0.20/0.54    ( ! [X26,X25] : (r1_tarski(k6_relat_1(k3_xboole_0(X25,X26)),k7_relat_1(k6_relat_1(k3_xboole_0(X25,X26)),X25))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f1666,f43])).
% 0.20/0.54  fof(f1666,plain,(
% 0.20/0.54    ( ! [X26,X25] : (r1_tarski(k6_relat_1(k3_xboole_0(X25,X26)),k7_relat_1(k6_relat_1(k3_xboole_0(X25,X26)),X25)) | ~v1_relat_1(k6_relat_1(k3_xboole_0(X25,X26)))) )),
% 0.20/0.54    inference(superposition,[],[f149,f67])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(X4,k3_xboole_0(X5,X6)),k7_relat_1(X4,X5)) | ~v1_relat_1(X4)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f146,f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X6,X7] : (v1_relat_1(k7_relat_1(X7,X6)) | ~v1_relat_1(X7)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f87,f43])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    ( ! [X6,X7] : (v1_relat_1(k7_relat_1(X7,X6)) | ~v1_relat_1(X7) | ~v1_relat_1(k6_relat_1(X6))) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X6,X7] : (v1_relat_1(k7_relat_1(X7,X6)) | ~v1_relat_1(X7) | ~v1_relat_1(k6_relat_1(X6)) | ~v1_relat_1(X7)) )),
% 0.20/0.54    inference(superposition,[],[f62,f56])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.54    inference(flattening,[],[f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    ( ! [X6,X4,X5] : (r1_tarski(k7_relat_1(X4,k3_xboole_0(X5,X6)),k7_relat_1(X4,X5)) | ~v1_relat_1(k7_relat_1(X4,X5)) | ~v1_relat_1(X4)) )),
% 0.20/0.54    inference(superposition,[],[f88,f65])).
% 0.20/0.54  fof(f88,plain,(
% 0.20/0.54    ( ! [X4,X5] : (r1_tarski(k7_relat_1(X5,X4),X5) | ~v1_relat_1(X5)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    ( ! [X4,X5] : (r1_tarski(k7_relat_1(X5,X4),X5) | ~v1_relat_1(X5) | ~v1_relat_1(X5)) )),
% 0.20/0.54    inference(superposition,[],[f58,f56])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 0.20/0.54  fof(f287,plain,(
% 0.20/0.54    ( ! [X17,X18] : (r1_tarski(k7_relat_1(k6_relat_1(X17),X18),k6_relat_1(k3_xboole_0(X17,X18)))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f286,f45])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    ( ! [X17,X18] : (r1_tarski(k7_relat_1(k6_relat_1(X17),X18),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X17)),X18)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f274,f43])).
% 0.20/0.54  fof(f274,plain,(
% 0.20/0.54    ( ! [X17,X18] : (r1_tarski(k7_relat_1(k6_relat_1(X17),X18),k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(X17)),X18))) | ~v1_relat_1(k6_relat_1(X17))) )),
% 0.20/0.54    inference(superposition,[],[f94,f137])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f93,f43])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f84,f43])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    ( ! [X2,X3] : (r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 0.20/0.54    inference(superposition,[],[f57,f56])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f2055,plain,(
% 0.20/0.54    ( ! [X24,X23] : (~r1_tarski(k6_relat_1(k3_xboole_0(X23,X24)),k6_relat_1(k3_xboole_0(X24,X23))) | k6_relat_1(k3_xboole_0(X23,X24)) = k6_relat_1(k3_xboole_0(X24,X23))) )),
% 0.20/0.54    inference(forward_demodulation,[],[f1970,f1941])).
% 0.20/0.54  fof(f1970,plain,(
% 0.20/0.54    ( ! [X24,X23] : (k6_relat_1(k3_xboole_0(X23,X24)) = k6_relat_1(k3_xboole_0(X24,X23)) | ~r1_tarski(k6_relat_1(k3_xboole_0(X23,X24)),k7_relat_1(k6_relat_1(X23),X24))) )),
% 0.20/0.54    inference(backward_demodulation,[],[f1086,f1941])).
% 0.20/0.54  fof(f1086,plain,(
% 0.20/0.54    ( ! [X24,X23] : (k7_relat_1(k6_relat_1(X23),X24) = k6_relat_1(k3_xboole_0(X23,X24)) | ~r1_tarski(k6_relat_1(k3_xboole_0(X23,X24)),k7_relat_1(k6_relat_1(X23),X24))) )),
% 0.20/0.54    inference(resolution,[],[f409,f287])).
% 0.20/0.54  fof(f2193,plain,(
% 0.20/0.54    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK1,sK0))),
% 0.20/0.54    inference(superposition,[],[f77,f1942])).
% 0.20/0.54  fof(f1942,plain,(
% 0.20/0.54    ( ! [X2,X3] : (k8_relat_1(X3,k6_relat_1(X2)) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 0.20/0.54    inference(backward_demodulation,[],[f90,f1941])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.20/0.54    inference(subsumption_resolution,[],[f71,f43])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) | ~v1_relat_1(k6_relat_1(sK1))),
% 0.20/0.54    inference(superposition,[],[f42,f55])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.54    inference(negated_conjecture,[],[f21])).
% 0.20/0.54  fof(f21,conjecture,(
% 0.20/0.54    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (17017)------------------------------
% 0.20/0.54  % (17017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17017)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (17017)Memory used [KB]: 3198
% 0.20/0.54  % (17017)Time elapsed: 0.118 s
% 0.20/0.54  % (17017)------------------------------
% 0.20/0.54  % (17017)------------------------------
% 0.20/0.55  % (17011)Success in time 0.181 s
%------------------------------------------------------------------------------
