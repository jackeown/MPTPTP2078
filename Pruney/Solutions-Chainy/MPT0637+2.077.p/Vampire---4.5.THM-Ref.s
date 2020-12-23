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
% DateTime   : Thu Dec  3 12:52:33 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 950 expanded)
%              Number of leaves         :   19 ( 284 expanded)
%              Depth                    :   17
%              Number of atoms          :  171 (1408 expanded)
%              Number of equality atoms :   82 ( 714 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1350,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1349,f1123])).

fof(f1123,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X4),X3) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X3))) ),
    inference(backward_demodulation,[],[f823,f1029])).

fof(f1029,plain,(
    ! [X4,X5] : k1_setfam_1(k3_enumset1(X4,X4,X4,X4,X5)) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) ),
    inference(superposition,[],[f44,f823])).

fof(f44,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f823,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X4),X3) = k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) ),
    inference(backward_demodulation,[],[f589,f800])).

fof(f800,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(resolution,[],[f799,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f122,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f122,plain,(
    ! [X2,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X1),X2)) ) ),
    inference(resolution,[],[f109,f92])).

fof(f92,plain,(
    ! [X2,X1] : r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2)) ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f90,plain,(
    ! [X2,X1] :
      ( r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f59,f81])).

fof(f81,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f56,f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k6_relat_1(X0))
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f106,f42])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ r1_tarski(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f49,f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f799,plain,(
    ! [X4,X3] : v1_relat_1(k7_relat_1(k6_relat_1(X4),X3)) ),
    inference(subsumption_resolution,[],[f798,f42])).

fof(f798,plain,(
    ! [X4,X3] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X4),X3))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f69,f450])).

fof(f450,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k3_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0))) ),
    inference(forward_demodulation,[],[f449,f82])).

fof(f82,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f79,f81])).

fof(f79,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f55,f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f449,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k3_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0))) ),
    inference(forward_demodulation,[],[f447,f44])).

fof(f447,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k3_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0))) ),
    inference(resolution,[],[f70,f42])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f57,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f62,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f589,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4) ),
    inference(forward_demodulation,[],[f588,f208])).

fof(f208,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f207,f81])).

fof(f207,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f206,f81])).

fof(f206,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f204,f43])).

fof(f43,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f204,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f203,f42])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f201,f43])).

fof(f201,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f588,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4) ),
    inference(forward_demodulation,[],[f587,f88])).

fof(f88,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(superposition,[],[f81,f75])).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(forward_demodulation,[],[f74,f45])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0)))) ),
    inference(resolution,[],[f47,f42])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f587,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4)),X4) ),
    inference(backward_demodulation,[],[f559,f570])).

fof(f570,plain,(
    ! [X30,X31,X29] : k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X30,X30,X30,X30,X31))),X29) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X29),X30),X31)) ),
    inference(superposition,[],[f208,f533])).

fof(f533,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2))) ),
    inference(resolution,[],[f71,f42])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f63,f67])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f559,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))),X3),X4) ),
    inference(superposition,[],[f533,f88])).

fof(f1349,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f1128,f1341])).

fof(f1341,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f1028,f208])).

fof(f1028,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2)) ),
    inference(superposition,[],[f43,f823])).

fof(f1128,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) ),
    inference(backward_demodulation,[],[f83,f1029])).

fof(f83,plain,(
    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f80,f82])).

fof(f80,plain,(
    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f68,f79])).

fof(f68,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f41,f67])).

fof(f41,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f39])).

fof(f39,plain,
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:07:47 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (7509)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (7497)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (7498)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (7500)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (7501)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (7505)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (7506)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (7499)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (7508)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (7505)Refutation not found, incomplete strategy% (7505)------------------------------
% 0.22/0.49  % (7505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7505)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (7505)Memory used [KB]: 10618
% 0.22/0.49  % (7505)Time elapsed: 0.069 s
% 0.22/0.49  % (7505)------------------------------
% 0.22/0.49  % (7505)------------------------------
% 0.22/0.50  % (7507)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (7503)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (7511)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (7502)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (7494)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (7504)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (7496)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (7510)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (7495)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.64/0.57  % (7503)Refutation found. Thanks to Tanya!
% 1.64/0.57  % SZS status Theorem for theBenchmark
% 1.64/0.57  % SZS output start Proof for theBenchmark
% 1.64/0.57  fof(f1350,plain,(
% 1.64/0.57    $false),
% 1.64/0.57    inference(subsumption_resolution,[],[f1349,f1123])).
% 1.64/0.57  fof(f1123,plain,(
% 1.64/0.57    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X4),X3) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X4),X3)))) )),
% 1.64/0.57    inference(backward_demodulation,[],[f823,f1029])).
% 1.64/0.57  fof(f1029,plain,(
% 1.64/0.57    ( ! [X4,X5] : (k1_setfam_1(k3_enumset1(X4,X4,X4,X4,X5)) = k1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) )),
% 1.64/0.57    inference(superposition,[],[f44,f823])).
% 1.64/0.57  fof(f44,plain,(
% 1.64/0.57    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.64/0.57    inference(cnf_transformation,[],[f15])).
% 1.64/0.57  fof(f15,axiom,(
% 1.64/0.57    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.64/0.57  fof(f823,plain,(
% 1.64/0.57    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X4),X3) = k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4)))) )),
% 1.64/0.57    inference(backward_demodulation,[],[f589,f800])).
% 1.64/0.57  fof(f800,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.64/0.57    inference(resolution,[],[f799,f160])).
% 1.64/0.57  fof(f160,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f155])).
% 1.64/0.57  fof(f155,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.64/0.57    inference(resolution,[],[f122,f60])).
% 1.64/0.57  fof(f60,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f36])).
% 1.64/0.57  fof(f36,plain,(
% 1.64/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(flattening,[],[f35])).
% 1.64/0.57  fof(f35,plain,(
% 1.64/0.57    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f20])).
% 1.64/0.57  fof(f20,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.64/0.57  fof(f122,plain,(
% 1.64/0.57    ( ! [X2,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X1),X2)),X1) | ~v1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.64/0.57    inference(resolution,[],[f109,f92])).
% 1.64/0.57  fof(f92,plain,(
% 1.64/0.57    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2))) )),
% 1.64/0.57    inference(subsumption_resolution,[],[f90,f42])).
% 1.64/0.57  fof(f42,plain,(
% 1.64/0.57    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f5])).
% 1.64/0.57  fof(f5,axiom,(
% 1.64/0.57    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.64/0.57  fof(f90,plain,(
% 1.64/0.57    ( ! [X2,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X2),X1),k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.64/0.57    inference(superposition,[],[f59,f81])).
% 1.64/0.57  fof(f81,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.64/0.57    inference(resolution,[],[f56,f42])).
% 1.64/0.57  fof(f56,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f32])).
% 1.64/0.57  fof(f32,plain,(
% 1.64/0.57    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f19])).
% 1.64/0.57  fof(f19,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.64/0.57  fof(f59,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f34])).
% 1.64/0.57  fof(f34,plain,(
% 1.64/0.57    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f17])).
% 1.64/0.57  fof(f17,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.64/0.57  fof(f109,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(subsumption_resolution,[],[f106,f42])).
% 1.64/0.57  fof(f106,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~r1_tarski(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(superposition,[],[f49,f44])).
% 1.64/0.57  fof(f49,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f28])).
% 1.64/0.57  fof(f28,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(flattening,[],[f27])).
% 1.64/0.57  fof(f27,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f12])).
% 1.64/0.57  fof(f12,axiom,(
% 1.64/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.64/0.57  fof(f799,plain,(
% 1.64/0.57    ( ! [X4,X3] : (v1_relat_1(k7_relat_1(k6_relat_1(X4),X3))) )),
% 1.64/0.57    inference(subsumption_resolution,[],[f798,f42])).
% 1.64/0.57  fof(f798,plain,(
% 1.64/0.57    ( ! [X4,X3] : (v1_relat_1(k7_relat_1(k6_relat_1(X4),X3)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.64/0.57    inference(superposition,[],[f69,f450])).
% 1.64/0.57  fof(f450,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k3_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0)))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f449,f82])).
% 1.64/0.57  fof(f82,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.64/0.57    inference(backward_demodulation,[],[f79,f81])).
% 1.64/0.57  fof(f79,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 1.64/0.57    inference(resolution,[],[f55,f42])).
% 1.64/0.57  fof(f55,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f31])).
% 1.64/0.57  fof(f31,plain,(
% 1.64/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f10])).
% 1.64/0.57  fof(f10,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.64/0.57  fof(f449,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k3_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(X1,X0)))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f447,f44])).
% 1.64/0.57  fof(f447,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k1_setfam_1(k3_enumset1(k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0)))) )),
% 1.64/0.57    inference(resolution,[],[f70,f42])).
% 1.64/0.57  fof(f70,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k1_setfam_1(k3_enumset1(X1,X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0)))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f57,f67])).
% 1.64/0.57  fof(f67,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f52,f66])).
% 1.64/0.57  fof(f66,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f53,f65])).
% 1.64/0.57  fof(f65,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f62,f64])).
% 1.64/0.57  fof(f64,plain,(
% 1.64/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f3])).
% 1.64/0.57  fof(f3,axiom,(
% 1.64/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.64/0.57  fof(f62,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f2])).
% 1.64/0.57  fof(f2,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.64/0.57  fof(f53,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f1])).
% 1.64/0.57  fof(f1,axiom,(
% 1.64/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.64/0.57  fof(f52,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f4])).
% 1.64/0.57  fof(f4,axiom,(
% 1.64/0.57    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.64/0.57  fof(f57,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f33])).
% 1.64/0.57  fof(f33,plain,(
% 1.64/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f11])).
% 1.64/0.57  fof(f11,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).
% 1.64/0.57  fof(f69,plain,(
% 1.64/0.57    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f54,f67])).
% 1.64/0.57  fof(f54,plain,(
% 1.64/0.57    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f30])).
% 1.64/0.57  fof(f30,plain,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f6])).
% 1.64/0.57  fof(f6,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.64/0.57  fof(f589,plain,(
% 1.64/0.57    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X3),X4)) )),
% 1.64/0.57    inference(forward_demodulation,[],[f588,f208])).
% 1.64/0.57  fof(f208,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f207,f81])).
% 1.64/0.57  fof(f207,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f206,f81])).
% 1.64/0.57  fof(f206,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f204,f43])).
% 1.64/0.57  fof(f43,plain,(
% 1.64/0.57    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f16])).
% 1.64/0.57  fof(f16,axiom,(
% 1.64/0.57    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 1.64/0.57  fof(f204,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0)))) )),
% 1.64/0.57    inference(resolution,[],[f203,f42])).
% 1.64/0.57  fof(f203,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f201,f43])).
% 1.64/0.57  fof(f201,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(resolution,[],[f48,f42])).
% 1.64/0.57  fof(f48,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f26,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f13])).
% 1.64/0.57  fof(f13,axiom,(
% 1.64/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 1.64/0.57  fof(f588,plain,(
% 1.64/0.57    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4)) )),
% 1.64/0.57    inference(forward_demodulation,[],[f587,f88])).
% 1.64/0.57  fof(f88,plain,(
% 1.64/0.57    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.64/0.57    inference(superposition,[],[f81,f75])).
% 1.64/0.57  fof(f75,plain,(
% 1.64/0.57    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.64/0.57    inference(forward_demodulation,[],[f74,f45])).
% 1.64/0.57  fof(f45,plain,(
% 1.64/0.57    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.64/0.57    inference(cnf_transformation,[],[f15])).
% 1.64/0.57  fof(f74,plain,(
% 1.64/0.57    ( ! [X0] : (k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(k2_relat_1(k6_relat_1(X0))))) )),
% 1.64/0.57    inference(resolution,[],[f47,f42])).
% 1.64/0.57  fof(f47,plain,(
% 1.64/0.57    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 1.64/0.57    inference(cnf_transformation,[],[f25])).
% 1.64/0.57  fof(f25,plain,(
% 1.64/0.57    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f18])).
% 1.64/0.57  fof(f18,axiom,(
% 1.64/0.57    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 1.64/0.57  fof(f587,plain,(
% 1.64/0.57    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4)),X4)) )),
% 1.64/0.57    inference(backward_demodulation,[],[f559,f570])).
% 1.64/0.57  fof(f570,plain,(
% 1.64/0.57    ( ! [X30,X31,X29] : (k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X30,X30,X30,X30,X31))),X29) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X29),X30),X31))) )),
% 1.64/0.57    inference(superposition,[],[f208,f533])).
% 1.64/0.57  fof(f533,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k3_enumset1(X1,X1,X1,X1,X2)))) )),
% 1.64/0.57    inference(resolution,[],[f71,f42])).
% 1.64/0.57  fof(f71,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.64/0.57    inference(definition_unfolding,[],[f63,f67])).
% 1.64/0.57  fof(f63,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f38])).
% 1.64/0.57  fof(f38,plain,(
% 1.64/0.57    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.64/0.57    inference(ennf_transformation,[],[f8])).
% 1.64/0.57  fof(f8,axiom,(
% 1.64/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.64/0.57  fof(f559,plain,(
% 1.64/0.57    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k3_enumset1(X3,X3,X3,X3,X4))),X3),X4)) )),
% 1.64/0.57    inference(superposition,[],[f533,f88])).
% 1.64/0.57  fof(f1349,plain,(
% 1.64/0.57    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.64/0.57    inference(backward_demodulation,[],[f1128,f1341])).
% 1.64/0.57  fof(f1341,plain,(
% 1.64/0.57    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 1.64/0.57    inference(superposition,[],[f1028,f208])).
% 1.64/0.57  fof(f1028,plain,(
% 1.64/0.57    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k4_relat_1(k7_relat_1(k6_relat_1(X3),X2))) )),
% 1.64/0.57    inference(superposition,[],[f43,f823])).
% 1.64/0.57  fof(f1128,plain,(
% 1.64/0.57    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))),
% 1.64/0.57    inference(backward_demodulation,[],[f83,f1029])).
% 1.64/0.57  fof(f83,plain,(
% 1.64/0.57    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.64/0.57    inference(backward_demodulation,[],[f80,f82])).
% 1.64/0.57  fof(f80,plain,(
% 1.64/0.57    k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.64/0.57    inference(backward_demodulation,[],[f68,f79])).
% 1.64/0.57  fof(f68,plain,(
% 1.64/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 1.64/0.57    inference(definition_unfolding,[],[f41,f67])).
% 1.64/0.57  fof(f41,plain,(
% 1.64/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.64/0.57    inference(cnf_transformation,[],[f40])).
% 1.64/0.57  fof(f40,plain,(
% 1.64/0.57    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f39])).
% 1.64/0.57  fof(f39,plain,(
% 1.64/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f23,plain,(
% 1.64/0.57    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f22])).
% 1.64/0.57  fof(f22,negated_conjecture,(
% 1.64/0.57    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.64/0.57    inference(negated_conjecture,[],[f21])).
% 1.64/0.57  fof(f21,conjecture,(
% 1.64/0.57    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.64/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.64/0.57  % SZS output end Proof for theBenchmark
% 1.64/0.57  % (7503)------------------------------
% 1.64/0.57  % (7503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (7503)Termination reason: Refutation
% 1.64/0.57  
% 1.64/0.57  % (7503)Memory used [KB]: 11897
% 1.64/0.57  % (7503)Time elapsed: 0.138 s
% 1.64/0.57  % (7503)------------------------------
% 1.64/0.57  % (7503)------------------------------
% 1.64/0.58  % (7493)Success in time 0.214 s
%------------------------------------------------------------------------------
