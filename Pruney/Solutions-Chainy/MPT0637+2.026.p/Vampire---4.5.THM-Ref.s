%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 455 expanded)
%              Number of leaves         :   18 ( 138 expanded)
%              Depth                    :   18
%              Number of atoms          :  193 ( 671 expanded)
%              Number of equality atoms :   74 ( 311 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3545,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3335])).

fof(f3335,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f75,f3070])).

fof(f3070,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) ),
    inference(forward_demodulation,[],[f3069,f388])).

fof(f388,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0) ),
    inference(superposition,[],[f383,f103])).

fof(f103,plain,(
    ! [X1] : k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(resolution,[],[f99,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f99,plain,(
    ! [X2] : r1_tarski(X2,X2) ),
    inference(forward_demodulation,[],[f98,f37])).

fof(f37,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f98,plain,(
    ! [X2] : r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2))) ),
    inference(subsumption_resolution,[],[f95,f36])).

fof(f36,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f95,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X2] :
      ( r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f40,f76])).

fof(f76,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(superposition,[],[f73,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f62,f37])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f39,f36])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f65,f67])).

fof(f67,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1)) ),
    inference(resolution,[],[f49,f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f383,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) ),
    inference(resolution,[],[f61,f36])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

fof(f3069,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4) ),
    inference(forward_demodulation,[],[f3068,f63])).

fof(f3068,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4) ),
    inference(forward_demodulation,[],[f3067,f383])).

fof(f3067,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X4) ),
    inference(forward_demodulation,[],[f389,f2593])).

fof(f2593,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k7_relat_1(k6_relat_1(X4),X3) ),
    inference(superposition,[],[f2479,f2143])).

fof(f2143,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(subsumption_resolution,[],[f2130,f2038])).

fof(f2038,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f66,f90])).

fof(f90,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(forward_demodulation,[],[f87,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f43,f55,f55])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f87,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_enumset1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0))) ),
    inference(resolution,[],[f60,f73])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f59,f36])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f46,f56])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f2130,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f2049,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f2049,plain,(
    ! [X6,X7] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)),X6) ),
    inference(resolution,[],[f2038,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))
      | r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ) ),
    inference(forward_demodulation,[],[f96,f37])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0)))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f40,f73])).

fof(f2479,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f2084,f1971])).

fof(f1971,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f1968,f67])).

fof(f1968,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(resolution,[],[f1069,f36])).

fof(f1069,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f1066,f67])).

fof(f1066,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f741,f36])).

fof(f741,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f36])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f2084,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) ),
    inference(subsumption_resolution,[],[f2071,f2038])).

fof(f2071,plain,(
    ! [X0,X1] :
      ( k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f2046,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f2046,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(resolution,[],[f2038,f116])).

fof(f116,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))
      | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4) ) ),
    inference(forward_demodulation,[],[f115,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f115,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(subsumption_resolution,[],[f109,f36])).

fof(f109,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4)))
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f41,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0)) ),
    inference(backward_demodulation,[],[f64,f67])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f48,f36])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f389,plain,(
    ! [X4,X3] : k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4) ),
    inference(superposition,[],[f383,f63])).

fof(f75,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f57,f67])).

fof(f57,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f35,f56])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f33])).

fof(f33,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:29:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (4428)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.45  % (4415)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (4416)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (4430)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (4427)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (4422)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (4413)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (4418)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (4419)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (4423)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (4417)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (4414)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (4429)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (4421)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (4424)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (4424)Refutation not found, incomplete strategy% (4424)------------------------------
% 0.21/0.49  % (4424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (4424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (4424)Memory used [KB]: 10618
% 0.21/0.49  % (4424)Time elapsed: 0.082 s
% 0.21/0.49  % (4424)------------------------------
% 0.21/0.49  % (4424)------------------------------
% 0.21/0.50  % (4426)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (4420)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (4431)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.58  % (4426)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 1.93/0.60  % SZS output start Proof for theBenchmark
% 1.93/0.60  fof(f3545,plain,(
% 1.93/0.60    $false),
% 1.93/0.60    inference(trivial_inequality_removal,[],[f3335])).
% 1.93/0.60  fof(f3335,plain,(
% 1.93/0.60    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.93/0.60    inference(superposition,[],[f75,f3070])).
% 1.93/0.60  fof(f3070,plain,(
% 1.93/0.60    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4)))) )),
% 1.93/0.60    inference(forward_demodulation,[],[f3069,f388])).
% 1.93/0.60  fof(f388,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),X0)) )),
% 1.93/0.60    inference(superposition,[],[f383,f103])).
% 1.93/0.60  fof(f103,plain,(
% 1.93/0.60    ( ! [X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,X1)) = X1) )),
% 1.93/0.60    inference(resolution,[],[f99,f60])).
% 1.93/0.60  fof(f60,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = X0) )),
% 1.93/0.60    inference(definition_unfolding,[],[f52,f56])).
% 1.93/0.60  fof(f56,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 1.93/0.60    inference(definition_unfolding,[],[f45,f55])).
% 1.93/0.60  fof(f55,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.93/0.60    inference(definition_unfolding,[],[f44,f53])).
% 1.93/0.60  fof(f53,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f4])).
% 1.93/0.60  fof(f4,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.93/0.60  fof(f44,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f3])).
% 1.93/0.60  fof(f3,axiom,(
% 1.93/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.93/0.60  fof(f45,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.93/0.60    inference(cnf_transformation,[],[f5])).
% 1.93/0.60  fof(f5,axiom,(
% 1.93/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.93/0.60  fof(f52,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f31])).
% 1.93/0.60  fof(f31,plain,(
% 1.93/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f1])).
% 1.93/0.60  fof(f1,axiom,(
% 1.93/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.93/0.60  fof(f99,plain,(
% 1.93/0.60    ( ! [X2] : (r1_tarski(X2,X2)) )),
% 1.93/0.60    inference(forward_demodulation,[],[f98,f37])).
% 1.93/0.60  fof(f37,plain,(
% 1.93/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.93/0.60    inference(cnf_transformation,[],[f11])).
% 1.93/0.60  fof(f11,axiom,(
% 1.93/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.93/0.60  fof(f98,plain,(
% 1.93/0.60    ( ! [X2] : (r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2)))) )),
% 1.93/0.60    inference(subsumption_resolution,[],[f95,f36])).
% 1.93/0.60  fof(f36,plain,(
% 1.93/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.93/0.60    inference(cnf_transformation,[],[f6])).
% 1.93/0.60  fof(f6,axiom,(
% 1.93/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.93/0.60  fof(f95,plain,(
% 1.93/0.60    ( ! [X2] : (r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.93/0.60    inference(duplicate_literal_removal,[],[f93])).
% 1.93/0.60  fof(f93,plain,(
% 1.93/0.60    ( ! [X2] : (r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 1.93/0.60    inference(resolution,[],[f40,f76])).
% 1.93/0.60  fof(f76,plain,(
% 1.93/0.60    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.93/0.60    inference(superposition,[],[f73,f63])).
% 1.93/0.60  fof(f63,plain,(
% 1.93/0.60    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.93/0.60    inference(forward_demodulation,[],[f62,f37])).
% 1.93/0.60  fof(f62,plain,(
% 1.93/0.60    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 1.93/0.60    inference(resolution,[],[f39,f36])).
% 1.93/0.60  fof(f39,plain,(
% 1.93/0.60    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 1.93/0.60    inference(cnf_transformation,[],[f20])).
% 1.93/0.60  fof(f20,plain,(
% 1.93/0.60    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.93/0.60    inference(ennf_transformation,[],[f16])).
% 1.93/0.60  fof(f16,axiom,(
% 1.93/0.60    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 1.93/0.60  fof(f73,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1))) )),
% 1.93/0.60    inference(backward_demodulation,[],[f65,f67])).
% 1.93/0.60  fof(f67,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.93/0.60    inference(resolution,[],[f47,f36])).
% 1.93/0.60  fof(f47,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f25])).
% 1.93/0.60  fof(f25,plain,(
% 1.93/0.60    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f15])).
% 1.93/0.60  fof(f15,axiom,(
% 1.93/0.60    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.93/0.60  fof(f65,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1))) )),
% 1.93/0.60    inference(resolution,[],[f49,f36])).
% 1.93/0.60  fof(f49,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f26])).
% 1.93/0.60  fof(f26,plain,(
% 1.93/0.60    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f12])).
% 1.93/0.60  fof(f12,axiom,(
% 1.93/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.93/0.60  fof(f40,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f22])).
% 1.93/0.60  fof(f22,plain,(
% 1.93/0.60    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.93/0.60    inference(flattening,[],[f21])).
% 1.93/0.60  fof(f21,plain,(
% 1.93/0.60    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.93/0.60    inference(ennf_transformation,[],[f9])).
% 1.93/0.60  fof(f9,axiom,(
% 1.93/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 1.93/0.60  fof(f383,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2)))) )),
% 1.93/0.60    inference(resolution,[],[f61,f36])).
% 1.93/0.60  fof(f61,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.93/0.60    inference(definition_unfolding,[],[f54,f56])).
% 1.93/0.60  fof(f54,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f32])).
% 1.93/0.60  fof(f32,plain,(
% 1.93/0.60    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.93/0.60    inference(ennf_transformation,[],[f8])).
% 1.93/0.60  fof(f8,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).
% 1.93/0.60  fof(f3069,plain,(
% 1.93/0.60    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X4)) )),
% 1.93/0.60    inference(forward_demodulation,[],[f3068,f63])).
% 1.93/0.60  fof(f3068,plain,(
% 1.93/0.60    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X3),X4),X4)) )),
% 1.93/0.60    inference(forward_demodulation,[],[f3067,f383])).
% 1.93/0.60  fof(f3067,plain,(
% 1.93/0.60    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(X3),k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X4)) )),
% 1.93/0.60    inference(forward_demodulation,[],[f389,f2593])).
% 1.93/0.60  fof(f2593,plain,(
% 1.93/0.60    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k7_relat_1(k6_relat_1(X4),X3)) )),
% 1.93/0.60    inference(superposition,[],[f2479,f2143])).
% 1.93/0.60  fof(f2143,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.93/0.60    inference(subsumption_resolution,[],[f2130,f2038])).
% 1.93/0.60  fof(f2038,plain,(
% 1.93/0.60    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.93/0.60    inference(superposition,[],[f66,f90])).
% 1.93/0.60  fof(f90,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)))) )),
% 1.93/0.60    inference(forward_demodulation,[],[f87,f58])).
% 1.93/0.60  fof(f58,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.93/0.60    inference(definition_unfolding,[],[f43,f55,f55])).
% 1.93/0.60  fof(f43,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f2])).
% 1.93/0.60  fof(f2,axiom,(
% 1.93/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.93/0.60  fof(f87,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k1_setfam_1(k2_enumset1(k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)))) )),
% 1.93/0.60    inference(resolution,[],[f60,f73])).
% 1.93/0.60  fof(f66,plain,(
% 1.93/0.60    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),X1)))) )),
% 1.93/0.60    inference(resolution,[],[f59,f36])).
% 1.93/0.60  fof(f59,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.93/0.60    inference(definition_unfolding,[],[f46,f56])).
% 1.93/0.60  fof(f46,plain,(
% 1.93/0.60    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f24])).
% 1.93/0.60  fof(f24,plain,(
% 1.93/0.60    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 1.93/0.60    inference(ennf_transformation,[],[f7])).
% 1.93/0.60  fof(f7,axiom,(
% 1.93/0.60    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 1.93/0.60  fof(f2130,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X0),X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.93/0.60    inference(resolution,[],[f2049,f51])).
% 1.93/0.60  fof(f51,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1 | ~v1_relat_1(X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f30])).
% 1.93/0.60  fof(f30,plain,(
% 1.93/0.60    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.93/0.60    inference(flattening,[],[f29])).
% 1.93/0.60  fof(f29,plain,(
% 1.93/0.60    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f13])).
% 1.93/0.60  fof(f13,axiom,(
% 1.93/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.93/0.60  fof(f2049,plain,(
% 1.93/0.60    ( ! [X6,X7] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X6),X7)),X6)) )),
% 1.93/0.60    inference(resolution,[],[f2038,f97])).
% 1.93/0.60  fof(f97,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) | r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 1.93/0.60    inference(forward_demodulation,[],[f96,f37])).
% 1.93/0.60  fof(f96,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.93/0.60    inference(subsumption_resolution,[],[f92,f36])).
% 1.93/0.60  fof(f92,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k1_relat_1(k6_relat_1(X0))) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.93/0.60    inference(resolution,[],[f40,f73])).
% 1.93/0.60  fof(f2479,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.93/0.60    inference(superposition,[],[f2084,f1971])).
% 1.93/0.60  fof(f1971,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 1.93/0.60    inference(forward_demodulation,[],[f1968,f67])).
% 1.93/0.60  fof(f1968,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.93/0.60    inference(resolution,[],[f1069,f36])).
% 1.93/0.60  fof(f1069,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 1.93/0.60    inference(forward_demodulation,[],[f1066,f67])).
% 1.93/0.60  fof(f1066,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.93/0.60    inference(resolution,[],[f741,f36])).
% 1.93/0.60  fof(f741,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 1.93/0.60    inference(resolution,[],[f42,f36])).
% 1.93/0.60  fof(f42,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f23])).
% 1.93/0.60  fof(f23,plain,(
% 1.93/0.60    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.93/0.60    inference(ennf_transformation,[],[f10])).
% 1.93/0.60  fof(f10,axiom,(
% 1.93/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 1.93/0.60  fof(f2084,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1))) )),
% 1.93/0.60    inference(subsumption_resolution,[],[f2071,f2038])).
% 1.93/0.60  fof(f2071,plain,(
% 1.93/0.60    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.93/0.60    inference(resolution,[],[f2046,f50])).
% 1.93/0.60  fof(f50,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~v1_relat_1(X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f28])).
% 1.93/0.60  fof(f28,plain,(
% 1.93/0.60    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.93/0.60    inference(flattening,[],[f27])).
% 1.93/0.60  fof(f27,plain,(
% 1.93/0.60    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f14])).
% 1.93/0.60  fof(f14,axiom,(
% 1.93/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.93/0.60  fof(f2046,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 1.93/0.60    inference(resolution,[],[f2038,f116])).
% 1.93/0.60  fof(f116,plain,(
% 1.93/0.60    ( ! [X4,X3] : (~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),X4)) )),
% 1.93/0.60    inference(forward_demodulation,[],[f115,f38])).
% 1.93/0.60  fof(f38,plain,(
% 1.93/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.93/0.60    inference(cnf_transformation,[],[f11])).
% 1.93/0.60  fof(f115,plain,(
% 1.93/0.60    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.93/0.60    inference(subsumption_resolution,[],[f109,f36])).
% 1.93/0.60  fof(f109,plain,(
% 1.93/0.60    ( ! [X4,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k2_relat_1(k6_relat_1(X4))) | ~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.93/0.60    inference(resolution,[],[f41,f74])).
% 1.93/0.60  fof(f74,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X0))) )),
% 1.93/0.60    inference(backward_demodulation,[],[f64,f67])).
% 1.93/0.60  fof(f64,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 1.93/0.60    inference(resolution,[],[f48,f36])).
% 1.93/0.60  fof(f48,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f26])).
% 1.93/0.60  fof(f41,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f22])).
% 1.93/0.60  fof(f389,plain,(
% 1.93/0.60    ( ! [X4,X3] : (k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))) = k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X3,X3,X3,X4))),X3),X4)) )),
% 1.93/0.60    inference(superposition,[],[f383,f63])).
% 1.93/0.60  fof(f75,plain,(
% 1.93/0.60    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.93/0.60    inference(backward_demodulation,[],[f57,f67])).
% 1.93/0.60  fof(f57,plain,(
% 1.93/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1)))),
% 1.93/0.60    inference(definition_unfolding,[],[f35,f56])).
% 1.93/0.60  fof(f35,plain,(
% 1.93/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.93/0.60    inference(cnf_transformation,[],[f34])).
% 1.93/0.60  fof(f34,plain,(
% 1.93/0.60    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.93/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f33])).
% 1.93/0.60  fof(f33,plain,(
% 1.93/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.93/0.60    introduced(choice_axiom,[])).
% 1.93/0.60  fof(f19,plain,(
% 1.93/0.60    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f18])).
% 1.93/0.60  fof(f18,negated_conjecture,(
% 1.93/0.60    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.93/0.60    inference(negated_conjecture,[],[f17])).
% 1.93/0.60  fof(f17,conjecture,(
% 1.93/0.60    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.93/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.93/0.60  % SZS output end Proof for theBenchmark
% 1.93/0.60  % (4426)------------------------------
% 1.93/0.60  % (4426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.60  % (4426)Termination reason: Refutation
% 1.93/0.60  
% 1.93/0.60  % (4426)Memory used [KB]: 3454
% 1.93/0.60  % (4426)Time elapsed: 0.158 s
% 1.93/0.60  % (4426)------------------------------
% 1.93/0.60  % (4426)------------------------------
% 1.93/0.60  % (4412)Success in time 0.243 s
%------------------------------------------------------------------------------
