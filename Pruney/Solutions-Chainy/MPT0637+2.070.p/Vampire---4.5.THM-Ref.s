%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 777 expanded)
%              Number of leaves         :   20 ( 199 expanded)
%              Depth                    :   19
%              Number of atoms          :  222 (1534 expanded)
%              Number of equality atoms :   89 ( 408 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2704,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2703])).

fof(f2703,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f2702,f911])).

fof(f911,plain,(
    ! [X23,X22] : k7_relat_1(k6_relat_1(X23),X22) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))) ),
    inference(backward_demodulation,[],[f573,f910])).

fof(f910,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3) ),
    inference(forward_demodulation,[],[f657,f463])).

fof(f463,plain,(
    ! [X21,X22] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22))),X21) ),
    inference(forward_demodulation,[],[f441,f44])).

fof(f44,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f441,plain,(
    ! [X21,X22] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22))),X21) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22)))) ),
    inference(superposition,[],[f177,f292])).

fof(f292,plain,(
    ! [X2,X3] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X2),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(resolution,[],[f283,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(resolution,[],[f100,f45])).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f99,f87])).

fof(f87,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f78,f80])).

fof(f80,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f78,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f60,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f283,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(resolution,[],[f163,f95])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X1))
      | r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1)) ) ),
    inference(superposition,[],[f59,f80])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f163,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))
      | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X5),X6)),X7) ) ),
    inference(resolution,[],[f160,f103])).

fof(f103,plain,(
    ! [X0,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f102,f45])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(resolution,[],[f90,f45])).

fof(f90,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(k6_relat_1(X4))
      | ~ v1_relat_1(k6_relat_1(X5))
      | v1_relat_1(k7_relat_1(k6_relat_1(X5),X4)) ) ),
    inference(superposition,[],[f61,f80])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X0),X1)
      | ~ r1_tarski(X0,k6_relat_1(X1)) ) ),
    inference(resolution,[],[f114,f45])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(X1,k6_relat_1(X0))
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f52,f48])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f177,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f176,f80])).

fof(f176,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f175,f80])).

fof(f175,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f172,f44])).

fof(f172,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f154,f45])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f151,f44])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1))) ) ),
    inference(resolution,[],[f50,f45])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f657,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3) ),
    inference(superposition,[],[f141,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(forward_demodulation,[],[f116,f87])).

fof(f116,plain,(
    ! [X2,X0,X1] : k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2)) ),
    inference(resolution,[],[f64,f45])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).

fof(f141,plain,(
    ! [X4,X3] : k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f135,f103])).

fof(f135,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(resolution,[],[f134,f60])).

fof(f134,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f133,f45])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,X0) ) ),
    inference(forward_demodulation,[],[f132,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f132,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(X0,k1_relat_1(k6_relat_1(X0))) ) ),
    inference(resolution,[],[f131,f96])).

fof(f96,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(superposition,[],[f95,f92])).

fof(f92,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ) ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(resolution,[],[f110,f45])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(X0,k1_relat_1(X1)) ) ),
    inference(superposition,[],[f51,f47])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f573,plain,(
    ! [X23,X22] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))),X22) ),
    inference(forward_demodulation,[],[f546,f44])).

fof(f546,plain,(
    ! [X23,X22] : k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))),X22) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22)))) ),
    inference(superposition,[],[f177,f301])).

fof(f301,plain,(
    ! [X2,X3] : k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X3),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) ),
    inference(resolution,[],[f284,f123])).

fof(f284,plain,(
    ! [X2,X3] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)),X3) ),
    inference(resolution,[],[f163,f97])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) ),
    inference(resolution,[],[f89,f45])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) ) ),
    inference(superposition,[],[f58,f80])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2702,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(forward_demodulation,[],[f2699,f1108])).

fof(f1108,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3) ),
    inference(superposition,[],[f992,f177])).

fof(f992,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f44,f911])).

fof(f2699,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0))) ),
    inference(backward_demodulation,[],[f91,f1491])).

fof(f1491,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(forward_demodulation,[],[f1490,f87])).

fof(f1490,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(forward_demodulation,[],[f1484,f48])).

fof(f1484,plain,(
    ! [X0,X1] : k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0)) ),
    inference(resolution,[],[f73,f45])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f57,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).

fof(f91,plain,(
    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f83,f87])).

fof(f83,plain,(
    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f72,f78])).

fof(f72,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f43,f71])).

fof(f43,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f41])).

fof(f41,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n004.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 09:35:53 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.41  % (23120)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (23116)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (23118)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (23118)Refutation not found, incomplete strategy% (23118)------------------------------
% 0.20/0.46  % (23118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (23118)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (23118)Memory used [KB]: 10618
% 0.20/0.46  % (23118)Time elapsed: 0.061 s
% 0.20/0.46  % (23118)------------------------------
% 0.20/0.46  % (23118)------------------------------
% 0.20/0.46  % (23124)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (23109)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (23108)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (23107)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (23111)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (23115)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (23114)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (23119)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (23117)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (23106)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (23112)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (23121)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (23122)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (23113)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (23123)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.53  % (23108)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 1.51/0.54  % SZS output start Proof for theBenchmark
% 1.51/0.54  fof(f2704,plain,(
% 1.51/0.54    $false),
% 1.51/0.54    inference(trivial_inequality_removal,[],[f2703])).
% 1.51/0.54  fof(f2703,plain,(
% 1.51/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.51/0.54    inference(superposition,[],[f2702,f911])).
% 1.51/0.54  fof(f911,plain,(
% 1.51/0.54    ( ! [X23,X22] : (k7_relat_1(k6_relat_1(X23),X22) = k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22)))) )),
% 1.51/0.54    inference(backward_demodulation,[],[f573,f910])).
% 1.51/0.54  fof(f910,plain,(
% 1.51/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X3)) )),
% 1.51/0.54    inference(forward_demodulation,[],[f657,f463])).
% 1.51/0.54  fof(f463,plain,(
% 1.51/0.54    ( ! [X21,X22] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22))),X21)) )),
% 1.51/0.54    inference(forward_demodulation,[],[f441,f44])).
% 1.51/0.54  fof(f44,plain,(
% 1.51/0.54    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.51/0.54    inference(cnf_transformation,[],[f17])).
% 1.51/0.54  fof(f17,axiom,(
% 1.51/0.54    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.51/0.54  fof(f441,plain,(
% 1.51/0.54    ( ! [X21,X22] : (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22))),X21) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X21),X22))))) )),
% 1.51/0.54    inference(superposition,[],[f177,f292])).
% 1.51/0.54  fof(f292,plain,(
% 1.51/0.54    ( ! [X2,X3] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X2),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 1.51/0.54    inference(resolution,[],[f283,f123])).
% 1.51/0.54  fof(f123,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.51/0.54    inference(resolution,[],[f100,f45])).
% 1.51/0.54  fof(f45,plain,(
% 1.51/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.54    inference(cnf_transformation,[],[f23])).
% 1.51/0.54  fof(f23,plain,(
% 1.51/0.54    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.51/0.54    inference(pure_predicate_removal,[],[f20])).
% 1.51/0.54  fof(f20,axiom,(
% 1.51/0.54    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).
% 1.51/0.54  fof(f100,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.51/0.54    inference(forward_demodulation,[],[f99,f87])).
% 1.51/0.54  fof(f87,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.51/0.54    inference(backward_demodulation,[],[f78,f80])).
% 1.51/0.54  fof(f80,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.51/0.54    inference(resolution,[],[f56,f45])).
% 1.51/0.54  fof(f56,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f30])).
% 1.51/0.54  fof(f30,plain,(
% 1.51/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.51/0.54    inference(ennf_transformation,[],[f19])).
% 1.51/0.54  fof(f19,axiom,(
% 1.51/0.54    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.51/0.54  fof(f78,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 1.51/0.54    inference(resolution,[],[f55,f45])).
% 1.51/0.54  fof(f55,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.51/0.54    inference(cnf_transformation,[],[f29])).
% 1.51/0.54  fof(f29,plain,(
% 1.51/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.51/0.54    inference(ennf_transformation,[],[f10])).
% 1.51/0.54  fof(f10,axiom,(
% 1.51/0.54    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.51/0.54  fof(f99,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.51/0.54    inference(superposition,[],[f60,f48])).
% 1.51/0.54  fof(f48,plain,(
% 1.51/0.54    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.51/0.54    inference(cnf_transformation,[],[f16])).
% 1.51/0.54  fof(f16,axiom,(
% 1.51/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.51/0.54  fof(f60,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f34])).
% 1.51/0.54  fof(f34,plain,(
% 1.51/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.51/0.54    inference(flattening,[],[f33])).
% 1.51/0.54  fof(f33,plain,(
% 1.51/0.54    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.51/0.54    inference(ennf_transformation,[],[f11])).
% 1.51/0.54  fof(f11,axiom,(
% 1.51/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 1.51/0.54  fof(f283,plain,(
% 1.51/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 1.51/0.54    inference(resolution,[],[f163,f95])).
% 1.51/0.54  fof(f95,plain,(
% 1.51/0.54    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0))) )),
% 1.51/0.54    inference(resolution,[],[f88,f45])).
% 1.51/0.54  fof(f88,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X1)) | r1_tarski(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X1))) )),
% 1.51/0.54    inference(superposition,[],[f59,f80])).
% 1.51/0.54  fof(f59,plain,(
% 1.51/0.54    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f32])).
% 1.51/0.54  fof(f32,plain,(
% 1.51/0.54    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.51/0.54    inference(ennf_transformation,[],[f18])).
% 1.51/0.54  fof(f18,axiom,(
% 1.51/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 1.51/0.54  fof(f163,plain,(
% 1.51/0.54    ( ! [X6,X7,X5] : (~r1_tarski(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7)) | r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X5),X6)),X7)) )),
% 1.51/0.54    inference(resolution,[],[f160,f103])).
% 1.51/0.54  fof(f103,plain,(
% 1.51/0.54    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.51/0.54    inference(resolution,[],[f102,f45])).
% 1.51/0.54  fof(f102,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.51/0.54    inference(resolution,[],[f90,f45])).
% 1.51/0.54  fof(f90,plain,(
% 1.51/0.54    ( ! [X4,X5] : (~v1_relat_1(k6_relat_1(X4)) | ~v1_relat_1(k6_relat_1(X5)) | v1_relat_1(k7_relat_1(k6_relat_1(X5),X4))) )),
% 1.51/0.54    inference(superposition,[],[f61,f80])).
% 1.51/0.54  fof(f61,plain,(
% 1.51/0.54    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f36])).
% 1.51/0.54  fof(f36,plain,(
% 1.51/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.51/0.54    inference(flattening,[],[f35])).
% 1.51/0.54  fof(f35,plain,(
% 1.51/0.54    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.51/0.54    inference(ennf_transformation,[],[f6])).
% 1.51/0.54  fof(f6,axiom,(
% 1.51/0.54    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.51/0.54  fof(f160,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | r1_tarski(k2_relat_1(X0),X1) | ~r1_tarski(X0,k6_relat_1(X1))) )),
% 1.51/0.54    inference(resolution,[],[f114,f45])).
% 1.51/0.54  fof(f114,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(X1,k6_relat_1(X0)) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.51/0.54    inference(superposition,[],[f52,f48])).
% 1.51/0.54  fof(f52,plain,(
% 1.51/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f28])).
% 1.51/0.54  fof(f28,plain,(
% 1.51/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.51/0.54    inference(flattening,[],[f27])).
% 1.51/0.54  fof(f27,plain,(
% 1.51/0.54    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.51/0.54    inference(ennf_transformation,[],[f14])).
% 1.51/0.54  fof(f14,axiom,(
% 1.51/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.51/0.54  fof(f177,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.51/0.54    inference(forward_demodulation,[],[f176,f80])).
% 1.51/0.54  fof(f176,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 1.51/0.54    inference(forward_demodulation,[],[f175,f80])).
% 1.51/0.54  fof(f175,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 1.51/0.54    inference(forward_demodulation,[],[f172,f44])).
% 1.51/0.54  fof(f172,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k6_relat_1(X0))) )),
% 1.51/0.54    inference(resolution,[],[f154,f45])).
% 1.51/0.54  fof(f154,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k6_relat_1(X1))) )),
% 1.51/0.54    inference(forward_demodulation,[],[f151,f44])).
% 1.51/0.54  fof(f151,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(k6_relat_1(X1),X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(k6_relat_1(X1)))) )),
% 1.51/0.54    inference(resolution,[],[f50,f45])).
% 1.51/0.54  fof(f50,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.51/0.54    inference(cnf_transformation,[],[f26])).
% 1.51/0.54  fof(f26,plain,(
% 1.51/0.54    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.51/0.54    inference(ennf_transformation,[],[f15])).
% 1.51/0.54  fof(f15,axiom,(
% 1.51/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.51/0.54  fof(f657,plain,(
% 1.51/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2),X3)) )),
% 1.51/0.54    inference(superposition,[],[f141,f119])).
% 1.51/0.54  fof(f119,plain,(
% 1.51/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.51/0.54    inference(forward_demodulation,[],[f116,f87])).
% 1.51/0.54  fof(f116,plain,(
% 1.51/0.54    ( ! [X2,X0,X1] : (k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),X2) = k8_relat_1(X0,k7_relat_1(k6_relat_1(X1),X2))) )),
% 1.51/0.54    inference(resolution,[],[f64,f45])).
% 1.51/0.54  fof(f64,plain,(
% 1.51/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 1.51/0.54    inference(cnf_transformation,[],[f39])).
% 1.51/0.54  fof(f39,plain,(
% 1.51/0.54    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.51/0.54    inference(ennf_transformation,[],[f12])).
% 1.51/0.54  fof(f12,axiom,(
% 1.51/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_relat_1)).
% 1.51/0.54  fof(f141,plain,(
% 1.51/0.54    ( ! [X4,X3] : (k7_relat_1(k6_relat_1(X3),X4) = k8_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X3),X4)),k7_relat_1(k6_relat_1(X3),X4))) )),
% 1.51/0.54    inference(resolution,[],[f135,f103])).
% 1.51/0.54  fof(f135,plain,(
% 1.51/0.54    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 1.51/0.54    inference(resolution,[],[f134,f60])).
% 1.51/0.54  fof(f134,plain,(
% 1.51/0.54    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.51/0.54    inference(resolution,[],[f133,f45])).
% 1.51/0.54  fof(f133,plain,(
% 1.51/0.54    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,X0)) )),
% 1.51/0.54    inference(forward_demodulation,[],[f132,f47])).
% 1.51/0.54  fof(f47,plain,(
% 1.51/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.51/0.54    inference(cnf_transformation,[],[f16])).
% 1.51/0.54  fof(f132,plain,(
% 1.51/0.54    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | r1_tarski(X0,k1_relat_1(k6_relat_1(X0)))) )),
% 1.51/0.54    inference(resolution,[],[f131,f96])).
% 1.51/0.54  fof(f96,plain,(
% 1.51/0.54    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.51/0.54    inference(superposition,[],[f95,f92])).
% 1.51/0.54  fof(f92,plain,(
% 1.51/0.54    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.51/0.54    inference(resolution,[],[f82,f45])).
% 1.51/0.54  fof(f82,plain,(
% 1.51/0.54    ( ! [X0] : (~v1_relat_1(k6_relat_1(X0)) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.51/0.54    inference(resolution,[],[f62,f46])).
% 1.51/0.54  fof(f46,plain,(
% 1.51/0.54    ( ! [X0] : (v4_relat_1(k6_relat_1(X0),X0)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f23])).
% 1.51/0.54  fof(f62,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f38])).
% 1.51/0.54  fof(f38,plain,(
% 1.51/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.51/0.54    inference(flattening,[],[f37])).
% 1.51/0.54  fof(f37,plain,(
% 1.51/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.51/0.54    inference(ennf_transformation,[],[f13])).
% 1.51/0.54  fof(f13,axiom,(
% 1.51/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.51/0.54  fof(f131,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | r1_tarski(X0,k1_relat_1(X1))) )),
% 1.51/0.54    inference(resolution,[],[f110,f45])).
% 1.51/0.54  fof(f110,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(k6_relat_1(X0)) | ~r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1) | r1_tarski(X0,k1_relat_1(X1))) )),
% 1.51/0.54    inference(superposition,[],[f51,f47])).
% 1.51/0.54  fof(f51,plain,(
% 1.51/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f28])).
% 1.51/0.54  fof(f573,plain,(
% 1.51/0.54    ( ! [X23,X22] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))) = k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))),X22)) )),
% 1.51/0.54    inference(forward_demodulation,[],[f546,f44])).
% 1.51/0.54  fof(f546,plain,(
% 1.51/0.54    ( ! [X23,X22] : (k7_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))),X22) = k4_relat_1(k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X23),X22))))) )),
% 1.51/0.54    inference(superposition,[],[f177,f301])).
% 1.51/0.54  fof(f301,plain,(
% 1.51/0.54    ( ! [X2,X3] : (k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3))) = k7_relat_1(k6_relat_1(X3),k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) )),
% 1.51/0.54    inference(resolution,[],[f284,f123])).
% 1.51/0.54  fof(f284,plain,(
% 1.51/0.54    ( ! [X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X3)),X3)) )),
% 1.51/0.54    inference(resolution,[],[f163,f97])).
% 1.51/0.54  fof(f97,plain,(
% 1.51/0.54    ( ! [X0,X1] : (r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1))) )),
% 1.51/0.54    inference(resolution,[],[f89,f45])).
% 1.51/0.54  fof(f89,plain,(
% 1.51/0.54    ( ! [X2,X3] : (~v1_relat_1(k6_relat_1(X2)) | r1_tarski(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))) )),
% 1.51/0.54    inference(superposition,[],[f58,f80])).
% 1.51/0.54  fof(f58,plain,(
% 1.51/0.54    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f32])).
% 1.51/0.54  fof(f2702,plain,(
% 1.51/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 1.51/0.54    inference(forward_demodulation,[],[f2699,f1108])).
% 1.51/0.54  fof(f1108,plain,(
% 1.51/0.54    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k7_relat_1(k6_relat_1(X2),X3)) )),
% 1.51/0.54    inference(superposition,[],[f992,f177])).
% 1.51/0.54  fof(f992,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.51/0.54    inference(superposition,[],[f44,f911])).
% 1.51/0.54  fof(f2699,plain,(
% 1.51/0.54    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k2_relat_1(k7_relat_1(k6_relat_1(sK1),sK0)))),
% 1.51/0.54    inference(backward_demodulation,[],[f91,f1491])).
% 1.51/0.54  fof(f1491,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) )),
% 1.51/0.54    inference(forward_demodulation,[],[f1490,f87])).
% 1.51/0.54  fof(f1490,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X0))) )),
% 1.51/0.54    inference(forward_demodulation,[],[f1484,f48])).
% 1.51/0.54  fof(f1484,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = k1_setfam_1(k4_enumset1(k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),k2_relat_1(k6_relat_1(X1)),X0))) )),
% 1.51/0.54    inference(resolution,[],[f73,f45])).
% 1.51/0.54  fof(f73,plain,(
% 1.51/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k1_setfam_1(k4_enumset1(k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),k2_relat_1(X1),X0))) )),
% 1.51/0.54    inference(definition_unfolding,[],[f57,f71])).
% 1.51/0.54  fof(f71,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.51/0.54    inference(definition_unfolding,[],[f53,f70])).
% 1.51/0.54  fof(f70,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.51/0.54    inference(definition_unfolding,[],[f54,f69])).
% 1.51/0.54  fof(f69,plain,(
% 1.51/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.51/0.54    inference(definition_unfolding,[],[f63,f68])).
% 1.51/0.54  fof(f68,plain,(
% 1.51/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.51/0.54    inference(definition_unfolding,[],[f66,f67])).
% 1.51/0.54  fof(f67,plain,(
% 1.51/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f4])).
% 1.51/0.54  fof(f4,axiom,(
% 1.51/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.51/0.54  fof(f66,plain,(
% 1.51/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f3])).
% 1.51/0.54  fof(f3,axiom,(
% 1.51/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.51/0.54  fof(f63,plain,(
% 1.51/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f2])).
% 1.51/0.54  fof(f2,axiom,(
% 1.51/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.51/0.54  fof(f54,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f1])).
% 1.51/0.54  fof(f1,axiom,(
% 1.51/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.51/0.54  fof(f53,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f5])).
% 1.51/0.54  fof(f5,axiom,(
% 1.51/0.54    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.51/0.54  fof(f57,plain,(
% 1.51/0.54    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.51/0.54    inference(cnf_transformation,[],[f31])).
% 1.51/0.54  fof(f31,plain,(
% 1.51/0.54    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.51/0.54    inference(ennf_transformation,[],[f9])).
% 1.51/0.54  fof(f9,axiom,(
% 1.51/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_relat_1)).
% 1.51/0.54  fof(f91,plain,(
% 1.51/0.54    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.51/0.54    inference(backward_demodulation,[],[f83,f87])).
% 1.51/0.54  fof(f83,plain,(
% 1.51/0.54    k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 1.51/0.54    inference(backward_demodulation,[],[f72,f78])).
% 1.51/0.54  fof(f72,plain,(
% 1.51/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.51/0.54    inference(definition_unfolding,[],[f43,f71])).
% 1.51/0.54  fof(f43,plain,(
% 1.51/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.51/0.54    inference(cnf_transformation,[],[f42])).
% 1.51/0.54  fof(f42,plain,(
% 1.51/0.54    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.51/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f41])).
% 1.51/0.54  fof(f41,plain,(
% 1.51/0.54    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 1.51/0.54    introduced(choice_axiom,[])).
% 1.51/0.54  fof(f24,plain,(
% 1.51/0.54    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 1.51/0.54    inference(ennf_transformation,[],[f22])).
% 1.51/0.54  fof(f22,negated_conjecture,(
% 1.51/0.54    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.51/0.54    inference(negated_conjecture,[],[f21])).
% 1.51/0.54  fof(f21,conjecture,(
% 1.51/0.54    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.51/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.51/0.54  % SZS output end Proof for theBenchmark
% 1.51/0.54  % (23108)------------------------------
% 1.51/0.54  % (23108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.54  % (23108)Termination reason: Refutation
% 1.51/0.54  
% 1.51/0.54  % (23108)Memory used [KB]: 7291
% 1.51/0.54  % (23108)Time elapsed: 0.136 s
% 1.51/0.54  % (23108)------------------------------
% 1.51/0.54  % (23108)------------------------------
% 1.51/0.54  % (23105)Success in time 0.196 s
%------------------------------------------------------------------------------
