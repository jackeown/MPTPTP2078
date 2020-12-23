%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 999 expanded)
%              Number of leaves         :   18 ( 270 expanded)
%              Depth                    :   19
%              Number of atoms          :  158 (1536 expanded)
%              Number of equality atoms :   92 ( 640 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f636,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f635])).

fof(f635,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(superposition,[],[f523,f590])).

fof(f590,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X3,k6_relat_1(X2)) ),
    inference(superposition,[],[f524,f102])).

fof(f102,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f101,f62])).

fof(f62,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f44,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f101,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(forward_demodulation,[],[f100,f62])).

fof(f100,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f97,f34])).

fof(f34,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f97,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f96,f35])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f93,f34])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f39,f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f524,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[],[f34,f465])).

fof(f465,plain,(
    ! [X10,X11] : k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))) = k8_relat_1(X11,k6_relat_1(X10)) ),
    inference(backward_demodulation,[],[f179,f462])).

fof(f462,plain,(
    ! [X4,X5] : k8_relat_1(X5,k6_relat_1(X4)) = k8_relat_1(X5,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5))))) ),
    inference(forward_demodulation,[],[f461,f207])).

fof(f207,plain,(
    ! [X12,X11] : k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12)))) = k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12))))) ),
    inference(forward_demodulation,[],[f194,f34])).

fof(f194,plain,(
    ! [X12,X11] : k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12))))) = k4_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12))))) ),
    inference(superposition,[],[f102,f137])).

fof(f137,plain,(
    ! [X0,X1] : k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0)) ),
    inference(resolution,[],[f126,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1)) ) ),
    inference(resolution,[],[f72,f35])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f64,f62])).

fof(f64,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f45,f35])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f47,f36])).

fof(f36,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f47,plain,(
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

fof(f126,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0) ),
    inference(backward_demodulation,[],[f73,f125])).

fof(f125,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f121,f37])).

fof(f37,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f121,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k2_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0)) ),
    inference(resolution,[],[f56,f35])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f46,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0) ),
    inference(superposition,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f41,f51,f51])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f461,plain,(
    ! [X4,X5] : k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k8_relat_1(X5,k6_relat_1(X4)) ),
    inference(forward_demodulation,[],[f452,f102])).

fof(f452,plain,(
    ! [X4,X5] : k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k4_relat_1(k8_relat_1(X4,k6_relat_1(X5))) ),
    inference(superposition,[],[f444,f342])).

fof(f342,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(superposition,[],[f81,f80])).

fof(f80,plain,(
    ! [X4,X5,X3] : k8_relat_1(X3,k8_relat_1(X4,k6_relat_1(X5))) = k5_relat_1(k8_relat_1(X4,k6_relat_1(X5)),k6_relat_1(X3)) ),
    inference(resolution,[],[f78,f44])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(resolution,[],[f77,f35])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f69,f35])).

fof(f69,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | v1_relat_1(k8_relat_1(X2,k6_relat_1(X1))) ) ),
    inference(superposition,[],[f48,f62])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f81,plain,(
    ! [X6,X7] : k8_relat_1(X6,k6_relat_1(X7)) = k5_relat_1(k8_relat_1(X6,k6_relat_1(X7)),k6_relat_1(k2_relat_1(k8_relat_1(X6,k6_relat_1(X7))))) ),
    inference(resolution,[],[f78,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f444,plain,(
    ! [X6,X7,X5] : k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) = k4_relat_1(k8_relat_1(X6,k8_relat_1(X7,k6_relat_1(X5)))) ),
    inference(forward_demodulation,[],[f443,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(forward_demodulation,[],[f79,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2))) ),
    inference(forward_demodulation,[],[f83,f70])).

fof(f83,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(resolution,[],[f78,f45])).

fof(f443,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) ),
    inference(forward_demodulation,[],[f442,f80])).

fof(f442,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X6)),k6_relat_1(X5)) ),
    inference(forward_demodulation,[],[f99,f102])).

fof(f99,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k4_relat_1(k8_relat_1(X6,k6_relat_1(X7))),k6_relat_1(X5)) ),
    inference(resolution,[],[f96,f78])).

fof(f179,plain,(
    ! [X10,X11] : k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))) = k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) ),
    inference(forward_demodulation,[],[f168,f34])).

fof(f168,plain,(
    ! [X10,X11] : k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) = k4_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) ),
    inference(superposition,[],[f102,f132])).

fof(f132,plain,(
    ! [X0,X1] : k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1)) ),
    inference(resolution,[],[f127,f87])).

fof(f127,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0) ),
    inference(backward_demodulation,[],[f54,f125])).

fof(f523,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK1,k6_relat_1(sK0)) ),
    inference(superposition,[],[f151,f465])).

fof(f151,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1)))) ),
    inference(backward_demodulation,[],[f128,f149])).

fof(f149,plain,(
    ! [X2,X3] : k2_relat_1(k8_relat_1(X3,k6_relat_1(X2))) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))) ),
    inference(superposition,[],[f130,f125])).

fof(f130,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(superposition,[],[f125,f55])).

fof(f128,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0)))) ),
    inference(backward_demodulation,[],[f66,f125])).

fof(f66,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f53,f62])).

fof(f53,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f33,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).

fof(f31,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (9834)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (9829)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (9839)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (9824)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (9832)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (9837)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (9833)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (9825)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (9841)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (9836)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (9827)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (9835)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (9826)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (9835)Refutation not found, incomplete strategy% (9835)------------------------------
% 0.20/0.47  % (9835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (9835)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (9835)Memory used [KB]: 10618
% 0.20/0.47  % (9835)Time elapsed: 0.063 s
% 0.20/0.47  % (9835)------------------------------
% 0.20/0.47  % (9835)------------------------------
% 0.20/0.47  % (9830)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (9828)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (9838)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (9826)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f636,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f635])).
% 0.20/0.49  fof(f635,plain,(
% 0.20/0.49    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.20/0.49    inference(superposition,[],[f523,f590])).
% 0.20/0.49  fof(f590,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X3,k6_relat_1(X2))) )),
% 0.20/0.49    inference(superposition,[],[f524,f102])).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f101,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.49    inference(resolution,[],[f44,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f16])).
% 0.20/0.49  fof(f16,axiom,(
% 0.20/0.49    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f100,f62])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f97,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 0.20/0.49    inference(resolution,[],[f96,f35])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f93,f34])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f39,f35])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 0.20/0.49  fof(f524,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k4_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.49    inference(superposition,[],[f34,f465])).
% 0.20/0.49  fof(f465,plain,(
% 0.20/0.49    ( ! [X10,X11] : (k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))) = k8_relat_1(X11,k6_relat_1(X10))) )),
% 0.20/0.49    inference(backward_demodulation,[],[f179,f462])).
% 0.20/0.49  fof(f462,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k8_relat_1(X5,k6_relat_1(X4)) = k8_relat_1(X5,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f461,f207])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    ( ! [X12,X11] : (k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12)))) = k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12)))))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f194,f34])).
% 0.20/0.49  fof(f194,plain,(
% 0.20/0.49    ( ! [X12,X11] : (k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12))))) = k4_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X11,k6_relat_1(X12)))))) )),
% 0.20/0.49    inference(superposition,[],[f102,f137])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X0))) )),
% 0.20/0.49    inference(resolution,[],[f126,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.49    inference(resolution,[],[f72,f35])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f71,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f64,f62])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(resolution,[],[f45,f35])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.49    inference(superposition,[],[f47,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),X0)) )),
% 0.20/0.49    inference(backward_demodulation,[],[f73,f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f121,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k2_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0))) )),
% 0.20/0.49    inference(resolution,[],[f56,f35])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k2_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f46,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f42,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f43,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X1,X1,X1,X0)),X0)) )),
% 0.20/0.49    inference(superposition,[],[f54,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f41,f51,f51])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)),X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f40,f52])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.49  fof(f461,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k8_relat_1(X5,k6_relat_1(X4))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f452,f102])).
% 0.20/0.49  fof(f452,plain,(
% 0.20/0.49    ( ! [X4,X5] : (k8_relat_1(X5,k8_relat_1(X4,k6_relat_1(k2_relat_1(k8_relat_1(X4,k6_relat_1(X5)))))) = k4_relat_1(k8_relat_1(X4,k6_relat_1(X5)))) )),
% 0.20/0.49    inference(superposition,[],[f444,f342])).
% 0.20/0.49  fof(f342,plain,(
% 0.20/0.49    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(k2_relat_1(k8_relat_1(X2,k6_relat_1(X3))),k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.20/0.49    inference(superposition,[],[f81,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X4,X5,X3] : (k8_relat_1(X3,k8_relat_1(X4,k6_relat_1(X5))) = k5_relat_1(k8_relat_1(X4,k6_relat_1(X5)),k6_relat_1(X3))) )),
% 0.20/0.49    inference(resolution,[],[f78,f44])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f77,f35])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | v1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(resolution,[],[f69,f35])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X2)) | v1_relat_1(k8_relat_1(X2,k6_relat_1(X1)))) )),
% 0.20/0.49    inference(superposition,[],[f48,f62])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ( ! [X6,X7] : (k8_relat_1(X6,k6_relat_1(X7)) = k5_relat_1(k8_relat_1(X6,k6_relat_1(X7)),k6_relat_1(k2_relat_1(k8_relat_1(X6,k6_relat_1(X7)))))) )),
% 0.20/0.49    inference(resolution,[],[f78,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.50  fof(f444,plain,(
% 0.20/0.50    ( ! [X6,X7,X5] : (k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6))) = k4_relat_1(k8_relat_1(X6,k8_relat_1(X7,k6_relat_1(X5))))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f443,f104])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1))) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f79,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(X2)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f83,f70])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) )),
% 0.20/0.50    inference(resolution,[],[f50,f35])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k5_relat_1(k6_relat_1(X2),k8_relat_1(X0,k6_relat_1(X1)))) )),
% 0.20/0.50    inference(resolution,[],[f78,f45])).
% 0.20/0.50  fof(f443,plain,(
% 0.20/0.50    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k8_relat_1(X5,k8_relat_1(X7,k6_relat_1(X6)))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f442,f80])).
% 0.20/0.50  fof(f442,plain,(
% 0.20/0.50    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X6)),k6_relat_1(X5))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f99,f102])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k6_relat_1(X5),k8_relat_1(X6,k6_relat_1(X7)))) = k5_relat_1(k4_relat_1(k8_relat_1(X6,k6_relat_1(X7))),k6_relat_1(X5))) )),
% 0.20/0.50    inference(resolution,[],[f96,f78])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ( ! [X10,X11] : (k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))) = k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f168,f34])).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    ( ! [X10,X11] : (k8_relat_1(X11,k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11))))) = k4_relat_1(k6_relat_1(k2_relat_1(k8_relat_1(X10,k6_relat_1(X11)))))) )),
% 0.20/0.50    inference(superposition,[],[f102,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k6_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) = k8_relat_1(k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))),k6_relat_1(X1))) )),
% 0.20/0.50    inference(resolution,[],[f127,f87])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0)) )),
% 0.20/0.50    inference(backward_demodulation,[],[f54,f125])).
% 0.20/0.50  fof(f523,plain,(
% 0.20/0.50    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK1,k6_relat_1(sK0))),
% 0.20/0.50    inference(superposition,[],[f151,f465])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK0,k6_relat_1(sK1))))),
% 0.20/0.50    inference(backward_demodulation,[],[f128,f149])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X2,X3] : (k2_relat_1(k8_relat_1(X3,k6_relat_1(X2))) = k2_relat_1(k8_relat_1(X2,k6_relat_1(X3)))) )),
% 0.20/0.50    inference(superposition,[],[f130,f125])).
% 0.20/0.50  fof(f130,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X0)) = k2_relat_1(k8_relat_1(X1,k6_relat_1(X0)))) )),
% 0.20/0.50    inference(superposition,[],[f125,f55])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    k8_relat_1(sK0,k6_relat_1(sK1)) != k6_relat_1(k2_relat_1(k8_relat_1(sK1,k6_relat_1(sK0))))),
% 0.20/0.50    inference(backward_demodulation,[],[f66,f125])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 0.20/0.50    inference(backward_demodulation,[],[f53,f62])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 0.20/0.50    inference(definition_unfolding,[],[f33,f52])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.50    inference(negated_conjecture,[],[f17])).
% 0.20/0.50  fof(f17,conjecture,(
% 0.20/0.50    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (9826)------------------------------
% 0.20/0.50  % (9826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9826)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (9826)Memory used [KB]: 6524
% 0.20/0.50  % (9826)Time elapsed: 0.075 s
% 0.20/0.50  % (9826)------------------------------
% 0.20/0.50  % (9826)------------------------------
% 0.20/0.50  % (9823)Success in time 0.146 s
%------------------------------------------------------------------------------
