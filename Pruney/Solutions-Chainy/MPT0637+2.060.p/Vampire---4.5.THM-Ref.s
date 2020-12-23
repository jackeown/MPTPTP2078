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
% DateTime   : Thu Dec  3 12:52:31 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  152 (3772 expanded)
%              Number of leaves         :   22 (1072 expanded)
%              Depth                    :   33
%              Number of atoms          :  228 (6322 expanded)
%              Number of equality atoms :  113 (2038 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4597,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4523,f4067])).

fof(f4067,plain,(
    ! [X6,X7] : k7_relat_1(k6_relat_1(X7),X6) = k6_relat_1(k9_relat_1(k6_relat_1(X7),X6)) ),
    inference(forward_demodulation,[],[f4066,f182])).

fof(f182,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f181,f88])).

fof(f88,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f57,f46])).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f181,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f180,f88])).

fof(f180,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f177,f47])).

fof(f47,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f177,plain,(
    ! [X0,X1] : k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f176,f46])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f173,f47])).

fof(f173,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f46])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f4066,plain,(
    ! [X6,X7] : k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k6_relat_1(k9_relat_1(k6_relat_1(X7),X6)) ),
    inference(forward_demodulation,[],[f4065,f528])).

fof(f528,plain,(
    ! [X0,X1] : k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1) ),
    inference(resolution,[],[f526,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f131,f46])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f60,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

fof(f526,plain,(
    ! [X0,X1] : r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1) ),
    inference(superposition,[],[f479,f233])).

fof(f233,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(forward_demodulation,[],[f231,f92])).

fof(f92,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f231,plain,(
    ! [X0,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(superposition,[],[f99,f132])).

fof(f132,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) ),
    inference(subsumption_resolution,[],[f129,f98])).

fof(f98,plain,(
    ! [X2,X1] : v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) ),
    inference(subsumption_resolution,[],[f97,f46])).

fof(f97,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f96,f46])).

fof(f96,plain,(
    ! [X2,X1] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f64,f88])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f129,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(resolution,[],[f60,f84])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) ),
    inference(subsumption_resolution,[],[f83,f46])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f55,f48])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f99,plain,(
    ! [X2,X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(resolution,[],[f98,f58])).

fof(f479,plain,(
    ! [X43,X41,X42] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X42),X41),X43),X41) ),
    inference(superposition,[],[f380,f455])).

fof(f455,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2) ),
    inference(superposition,[],[f446,f182])).

fof(f446,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f362,f132])).

fof(f362,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6)) ),
    inference(backward_demodulation,[],[f186,f360])).

fof(f360,plain,(
    ! [X6,X4,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(forward_demodulation,[],[f359,f88])).

fof(f359,plain,(
    ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) ),
    inference(forward_demodulation,[],[f355,f100])).

fof(f100,plain,(
    ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4)) ),
    inference(resolution,[],[f98,f57])).

fof(f355,plain,(
    ! [X6,X4,X5] : k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6)) ),
    inference(resolution,[],[f348,f46])).

fof(f348,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X5)
      | k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k7_relat_1(k6_relat_1(X4),X6)) ) ),
    inference(forward_demodulation,[],[f344,f90])).

fof(f90,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f85,f88])).

fof(f85,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f56,f46])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f344,plain,(
    ! [X6,X4,X5] :
      ( k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k8_relat_1(X4,k6_relat_1(X6)))
      | ~ v1_relat_1(X5) ) ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).

fof(f186,plain,(
    ! [X6,X7,X5] : k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k8_relat_1(X7,k7_relat_1(k6_relat_1(X5),X6))) ),
    inference(forward_demodulation,[],[f185,f101])).

fof(f101,plain,(
    ! [X6,X8,X7] : k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6)) ),
    inference(resolution,[],[f98,f56])).

fof(f185,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) ),
    inference(forward_demodulation,[],[f184,f100])).

fof(f184,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(forward_demodulation,[],[f179,f182])).

fof(f179,plain,(
    ! [X6,X7,X5] : k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k4_relat_1(k7_relat_1(k6_relat_1(X5),X6))) ),
    inference(resolution,[],[f176,f98])).

fof(f380,plain,(
    ! [X2,X0,X1] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),X2) ),
    inference(forward_demodulation,[],[f363,f99])).

fof(f363,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)),X2) ),
    inference(backward_demodulation,[],[f291,f360])).

fof(f291,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2) ),
    inference(subsumption_resolution,[],[f285,f98])).

fof(f285,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2)
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ) ),
    inference(superposition,[],[f119,f101])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f112,f46])).

fof(f112,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f51,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f4065,plain,(
    ! [X6,X7] : k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X7),X6)),X6) ),
    inference(forward_demodulation,[],[f4064,f189])).

fof(f189,plain,(
    ! [X2,X1] : k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2)) ),
    inference(forward_demodulation,[],[f188,f47])).

fof(f188,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2)) = k4_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X1),X2))) ),
    inference(superposition,[],[f182,f141])).

fof(f141,plain,(
    ! [X6,X5] : k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5) ),
    inference(resolution,[],[f133,f118])).

fof(f118,plain,(
    ! [X2,X1] : r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2) ),
    inference(forward_demodulation,[],[f117,f92])).

fof(f117,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2) ),
    inference(forward_demodulation,[],[f116,f49])).

fof(f116,plain,(
    ! [X2,X1] : r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f115,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f111,f46])).

fof(f111,plain,(
    ! [X2,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f51,f88])).

fof(f4064,plain,(
    ! [X6,X7] : k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),k9_relat_1(k6_relat_1(X7),X6)),X6) ),
    inference(forward_demodulation,[],[f4033,f455])).

fof(f4033,plain,(
    ! [X6,X7] : k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X7),X6)),X7),X6) ),
    inference(superposition,[],[f362,f3538])).

fof(f3538,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k9_relat_1(k6_relat_1(X3),X2)) ),
    inference(subsumption_resolution,[],[f3519,f98])).

fof(f3519,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k9_relat_1(k6_relat_1(X3),X2))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(resolution,[],[f3229,f60])).

fof(f3229,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k9_relat_1(k6_relat_1(X1),X0)) ),
    inference(superposition,[],[f3022,f2838])).

fof(f2838,plain,(
    ! [X2,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) ),
    inference(forward_demodulation,[],[f2741,f49])).

fof(f2741,plain,(
    ! [X2,X3] : k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)))) ),
    inference(superposition,[],[f92,f143])).

fof(f143,plain,(
    ! [X10,X9] : k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X9),X10))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X9),X10))),X9) ),
    inference(resolution,[],[f133,f84])).

fof(f3022,plain,(
    ! [X10,X8,X9] : r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X9),X8))),X10),k9_relat_1(k6_relat_1(X8),X10)) ),
    inference(superposition,[],[f2815,f455])).

fof(f2815,plain,(
    ! [X208,X209,X207] : r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X207),X208))),X209),k9_relat_1(k6_relat_1(X207),X209)) ),
    inference(superposition,[],[f1632,f143])).

fof(f1632,plain,(
    ! [X6,X7,X5] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7),k9_relat_1(k6_relat_1(X5),X7)) ),
    inference(superposition,[],[f1581,f455])).

fof(f1581,plain,(
    ! [X14,X15,X13] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X13),X15),X14),k9_relat_1(k6_relat_1(X13),X14)) ),
    inference(superposition,[],[f247,f1540])).

fof(f1540,plain,(
    ! [X4,X5,X3] : k9_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k9_relat_1(k7_relat_1(k6_relat_1(X3),X5),X4) ),
    inference(superposition,[],[f769,f99])).

fof(f769,plain,(
    ! [X14,X15,X13] : k9_relat_1(k7_relat_1(k6_relat_1(X13),X14),X15) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X13),X15),X14)) ),
    inference(superposition,[],[f99,f748])).

fof(f748,plain,(
    ! [X4,X5,X3] : k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X5),X4) ),
    inference(superposition,[],[f476,f360])).

fof(f476,plain,(
    ! [X33,X34,X32] : k7_relat_1(k7_relat_1(k6_relat_1(X34),X32),X33) = k8_relat_1(X34,k7_relat_1(k6_relat_1(X33),X32)) ),
    inference(superposition,[],[f360,f455])).

fof(f247,plain,(
    ! [X4,X2,X3] : r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2),k9_relat_1(k6_relat_1(X3),X4)) ),
    inference(forward_demodulation,[],[f246,f99])).

fof(f246,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2)),k9_relat_1(k6_relat_1(X3),X4)) ),
    inference(subsumption_resolution,[],[f243,f46])).

fof(f243,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2)),k9_relat_1(k6_relat_1(X3),X4))
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f120,f100])).

fof(f120,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X4) ) ),
    inference(subsumption_resolution,[],[f113,f98])).

fof(f113,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f51,f92])).

fof(f4523,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(backward_demodulation,[],[f394,f4247])).

fof(f4247,plain,(
    ! [X4,X5] : k9_relat_1(k6_relat_1(X4),X5) = k1_relat_1(k7_relat_1(k6_relat_1(X4),X5)) ),
    inference(superposition,[],[f48,f4067])).

fof(f394,plain,(
    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) ),
    inference(backward_demodulation,[],[f91,f391])).

fof(f391,plain,(
    ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4)) ),
    inference(forward_demodulation,[],[f388,f48])).

fof(f388,plain,(
    ! [X4,X3] : k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4)) ),
    inference(resolution,[],[f77,f46])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f59,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f91,plain,(
    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(backward_demodulation,[],[f87,f90])).

fof(f87,plain,(
    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f76,f85])).

fof(f76,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f45,f75])).

fof(f45,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f43])).

fof(f43,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:10:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (3506)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (3507)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (3505)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (3504)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (3514)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (3517)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (3515)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (3515)Refutation not found, incomplete strategy% (3515)------------------------------
% 0.22/0.49  % (3515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3515)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3515)Memory used [KB]: 10618
% 0.22/0.49  % (3515)Time elapsed: 0.063 s
% 0.22/0.49  % (3515)------------------------------
% 0.22/0.49  % (3515)------------------------------
% 0.22/0.49  % (3509)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (3510)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (3513)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (3516)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (3512)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % (3519)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (3508)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (3511)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.51  % (3520)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.53  % (3518)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.53  % (3521)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.29/0.66  % (3513)Refutation found. Thanks to Tanya!
% 2.29/0.66  % SZS status Theorem for theBenchmark
% 2.29/0.66  % SZS output start Proof for theBenchmark
% 2.29/0.66  fof(f4597,plain,(
% 2.29/0.66    $false),
% 2.29/0.66    inference(subsumption_resolution,[],[f4523,f4067])).
% 2.29/0.66  fof(f4067,plain,(
% 2.29/0.66    ( ! [X6,X7] : (k7_relat_1(k6_relat_1(X7),X6) = k6_relat_1(k9_relat_1(k6_relat_1(X7),X6))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f4066,f182])).
% 2.29/0.66  fof(f182,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f181,f88])).
% 2.29/0.66  fof(f88,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.29/0.66    inference(resolution,[],[f57,f46])).
% 2.29/0.66  fof(f46,plain,(
% 2.29/0.66    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.29/0.66    inference(cnf_transformation,[],[f9])).
% 2.29/0.66  fof(f9,axiom,(
% 2.29/0.66    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 2.29/0.66  fof(f57,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f32])).
% 2.29/0.66  fof(f32,plain,(
% 2.29/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f22])).
% 2.29/0.66  fof(f22,axiom,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.29/0.66  fof(f181,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k7_relat_1(k6_relat_1(X1),X0))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f180,f88])).
% 2.29/0.66  fof(f180,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f177,f47])).
% 2.29/0.66  fof(f47,plain,(
% 2.29/0.66    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 2.29/0.66    inference(cnf_transformation,[],[f17])).
% 2.29/0.66  fof(f17,axiom,(
% 2.29/0.66    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 2.29/0.66  fof(f177,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0)))) )),
% 2.29/0.66    inference(resolution,[],[f176,f46])).
% 2.29/0.66  fof(f176,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f173,f47])).
% 2.29/0.66  fof(f173,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k4_relat_1(k6_relat_1(X1)),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.29/0.66    inference(resolution,[],[f52,f46])).
% 2.29/0.66  fof(f52,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f29])).
% 2.29/0.66  fof(f29,plain,(
% 2.29/0.66    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.29/0.66    inference(ennf_transformation,[],[f15])).
% 2.29/0.66  fof(f15,axiom,(
% 2.29/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 2.29/0.66  fof(f4066,plain,(
% 2.29/0.66    ( ! [X6,X7] : (k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k6_relat_1(k9_relat_1(k6_relat_1(X7),X6))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f4065,f528])).
% 2.29/0.66  fof(f528,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X0),X1)),X1)) )),
% 2.29/0.66    inference(resolution,[],[f526,f133])).
% 2.29/0.66  fof(f133,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f131,f46])).
% 2.29/0.66  fof(f131,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.29/0.66    inference(superposition,[],[f60,f48])).
% 2.29/0.66  fof(f48,plain,(
% 2.29/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.29/0.66    inference(cnf_transformation,[],[f16])).
% 2.29/0.66  fof(f16,axiom,(
% 2.29/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.29/0.66  fof(f60,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f36])).
% 2.29/0.66  fof(f36,plain,(
% 2.29/0.66    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(flattening,[],[f35])).
% 2.29/0.66  fof(f35,plain,(
% 2.29/0.66    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f23])).
% 2.29/0.66  fof(f23,axiom,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 2.29/0.66  fof(f526,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X0),X1),X1)) )),
% 2.29/0.66    inference(superposition,[],[f479,f233])).
% 2.29/0.66  fof(f233,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f231,f92])).
% 2.29/0.66  fof(f92,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 2.29/0.66    inference(resolution,[],[f58,f46])).
% 2.29/0.66  fof(f58,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f33])).
% 2.29/0.66  fof(f33,plain,(
% 2.29/0.66    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f13])).
% 2.29/0.66  fof(f13,axiom,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 2.29/0.66  fof(f231,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X0)) )),
% 2.29/0.66    inference(superposition,[],[f99,f132])).
% 2.29/0.66  fof(f132,plain,(
% 2.29/0.66    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f129,f98])).
% 2.29/0.66  fof(f98,plain,(
% 2.29/0.66    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1))) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f97,f46])).
% 2.29/0.66  fof(f97,plain,(
% 2.29/0.66    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f96,f46])).
% 2.29/0.66  fof(f96,plain,(
% 2.29/0.66    ( ! [X2,X1] : (v1_relat_1(k7_relat_1(k6_relat_1(X2),X1)) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.29/0.66    inference(superposition,[],[f64,f88])).
% 2.29/0.66  fof(f64,plain,(
% 2.29/0.66    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f42])).
% 2.29/0.66  fof(f42,plain,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 2.29/0.66    inference(flattening,[],[f41])).
% 2.29/0.66  fof(f41,plain,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 2.29/0.66    inference(ennf_transformation,[],[f8])).
% 2.29/0.66  fof(f8,axiom,(
% 2.29/0.66    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 2.29/0.66  fof(f129,plain,(
% 2.29/0.66    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),X2) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 2.29/0.66    inference(resolution,[],[f60,f84])).
% 2.29/0.66  fof(f84,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f83,f46])).
% 2.29/0.66  fof(f83,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 2.29/0.66    inference(superposition,[],[f55,f48])).
% 2.29/0.66  fof(f55,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f30])).
% 2.29/0.66  fof(f30,plain,(
% 2.29/0.66    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f20])).
% 2.29/0.66  fof(f20,axiom,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 2.29/0.66  fof(f99,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) = k9_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) )),
% 2.29/0.66    inference(resolution,[],[f98,f58])).
% 2.29/0.66  fof(f479,plain,(
% 2.29/0.66    ( ! [X43,X41,X42] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X42),X41),X43),X41)) )),
% 2.29/0.66    inference(superposition,[],[f380,f455])).
% 2.29/0.66  fof(f455,plain,(
% 2.29/0.66    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k6_relat_1(X3),X2)) )),
% 2.29/0.66    inference(superposition,[],[f446,f182])).
% 2.29/0.66  fof(f446,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.29/0.66    inference(superposition,[],[f362,f132])).
% 2.29/0.66  fof(f362,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X7),X5),X6))) )),
% 2.29/0.66    inference(backward_demodulation,[],[f186,f360])).
% 2.29/0.66  fof(f360,plain,(
% 2.29/0.66    ( ! [X6,X4,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5) = k8_relat_1(X4,k7_relat_1(k6_relat_1(X6),X5))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f359,f88])).
% 2.29/0.66  fof(f359,plain,(
% 2.29/0.66    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k7_relat_1(k6_relat_1(X4),X6),X5)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f355,f100])).
% 2.29/0.66  fof(f100,plain,(
% 2.29/0.66    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X3),X4))) )),
% 2.29/0.66    inference(resolution,[],[f98,f57])).
% 2.29/0.66  fof(f355,plain,(
% 2.29/0.66    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k5_relat_1(k6_relat_1(X5),k7_relat_1(k6_relat_1(X4),X6))) )),
% 2.29/0.66    inference(resolution,[],[f348,f46])).
% 2.29/0.66  fof(f348,plain,(
% 2.29/0.66    ( ! [X6,X4,X5] : (~v1_relat_1(X5) | k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k7_relat_1(k6_relat_1(X4),X6))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f344,f90])).
% 2.29/0.66  fof(f90,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.29/0.66    inference(backward_demodulation,[],[f85,f88])).
% 2.29/0.66  fof(f85,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.29/0.66    inference(resolution,[],[f56,f46])).
% 2.29/0.66  fof(f56,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 2.29/0.66    inference(cnf_transformation,[],[f31])).
% 2.29/0.66  fof(f31,plain,(
% 2.29/0.66    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f11])).
% 2.29/0.66  fof(f11,axiom,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 2.29/0.66  fof(f344,plain,(
% 2.29/0.66    ( ! [X6,X4,X5] : (k8_relat_1(X4,k5_relat_1(X5,k6_relat_1(X6))) = k5_relat_1(X5,k8_relat_1(X4,k6_relat_1(X6))) | ~v1_relat_1(X5)) )),
% 2.29/0.66    inference(resolution,[],[f62,f46])).
% 2.29/0.66  fof(f62,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X1)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f39])).
% 2.29/0.66  fof(f39,plain,(
% 2.29/0.66    ! [X0,X1] : (! [X2] : (k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f12])).
% 2.29/0.66  fof(f12,axiom,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k8_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(X1,k8_relat_1(X0,X2))))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_relat_1)).
% 2.29/0.66  fof(f186,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7) = k4_relat_1(k8_relat_1(X7,k7_relat_1(k6_relat_1(X5),X6)))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f185,f101])).
% 2.29/0.66  fof(f101,plain,(
% 2.29/0.66    ( ! [X6,X8,X7] : (k8_relat_1(X6,k7_relat_1(k6_relat_1(X7),X8)) = k5_relat_1(k7_relat_1(k6_relat_1(X7),X8),k6_relat_1(X6))) )),
% 2.29/0.66    inference(resolution,[],[f98,f56])).
% 2.29/0.66  fof(f185,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k7_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f184,f100])).
% 2.29/0.66  fof(f184,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k7_relat_1(k6_relat_1(X6),X5))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f179,f182])).
% 2.29/0.66  fof(f179,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (k4_relat_1(k5_relat_1(k7_relat_1(k6_relat_1(X5),X6),k6_relat_1(X7))) = k5_relat_1(k6_relat_1(X7),k4_relat_1(k7_relat_1(k6_relat_1(X5),X6)))) )),
% 2.29/0.66    inference(resolution,[],[f176,f98])).
% 2.29/0.66  fof(f380,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1),X2)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f363,f99])).
% 2.29/0.66  fof(f363,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X2),X0),X1)),X2)) )),
% 2.29/0.66    inference(backward_demodulation,[],[f291,f360])).
% 2.29/0.66  fof(f291,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f285,f98])).
% 2.29/0.66  fof(f285,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1))),X2) | ~v1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.29/0.66    inference(superposition,[],[f119,f101])).
% 2.29/0.66  fof(f119,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(X1)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f112,f46])).
% 2.29/0.66  fof(f112,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 2.29/0.66    inference(superposition,[],[f51,f49])).
% 2.29/0.66  fof(f49,plain,(
% 2.29/0.66    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.29/0.66    inference(cnf_transformation,[],[f16])).
% 2.29/0.66  fof(f51,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f28])).
% 2.29/0.66  fof(f28,plain,(
% 2.29/0.66    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.29/0.66    inference(ennf_transformation,[],[f14])).
% 2.29/0.66  fof(f14,axiom,(
% 2.29/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 2.29/0.66  fof(f4065,plain,(
% 2.29/0.66    ( ! [X6,X7] : (k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X7),X6)),X6)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f4064,f189])).
% 2.29/0.66  fof(f189,plain,(
% 2.29/0.66    ( ! [X2,X1] : (k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f188,f47])).
% 2.29/0.66  fof(f188,plain,(
% 2.29/0.66    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),k9_relat_1(k6_relat_1(X1),X2)) = k4_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X1),X2)))) )),
% 2.29/0.66    inference(superposition,[],[f182,f141])).
% 2.29/0.66  fof(f141,plain,(
% 2.29/0.66    ( ! [X6,X5] : (k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)) = k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X5),X6)),X5)) )),
% 2.29/0.66    inference(resolution,[],[f133,f118])).
% 2.29/0.66  fof(f118,plain,(
% 2.29/0.66    ( ! [X2,X1] : (r1_tarski(k9_relat_1(k6_relat_1(X2),X1),X2)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f117,f92])).
% 2.29/0.66  fof(f117,plain,(
% 2.29/0.66    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),X2)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f116,f49])).
% 2.29/0.66  fof(f116,plain,(
% 2.29/0.66    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2)))) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f115,f46])).
% 2.29/0.66  fof(f115,plain,(
% 2.29/0.66    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f111,f46])).
% 2.29/0.66  fof(f111,plain,(
% 2.29/0.66    ( ! [X2,X1] : (r1_tarski(k2_relat_1(k7_relat_1(k6_relat_1(X2),X1)),k2_relat_1(k6_relat_1(X2))) | ~v1_relat_1(k6_relat_1(X2)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 2.29/0.66    inference(superposition,[],[f51,f88])).
% 2.29/0.66  fof(f4064,plain,(
% 2.29/0.66    ( ! [X6,X7] : (k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(X7),k9_relat_1(k6_relat_1(X7),X6)),X6)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f4033,f455])).
% 2.29/0.66  fof(f4033,plain,(
% 2.29/0.66    ( ! [X6,X7] : (k4_relat_1(k7_relat_1(k6_relat_1(X6),X7)) = k7_relat_1(k7_relat_1(k6_relat_1(k9_relat_1(k6_relat_1(X7),X6)),X7),X6)) )),
% 2.29/0.66    inference(superposition,[],[f362,f3538])).
% 2.29/0.66  fof(f3538,plain,(
% 2.29/0.66    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k9_relat_1(k6_relat_1(X3),X2))) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f3519,f98])).
% 2.29/0.66  fof(f3519,plain,(
% 2.29/0.66    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X3),k9_relat_1(k6_relat_1(X3),X2)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 2.29/0.66    inference(resolution,[],[f3229,f60])).
% 2.29/0.66  fof(f3229,plain,(
% 2.29/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k9_relat_1(k6_relat_1(X1),X0))) )),
% 2.29/0.66    inference(superposition,[],[f3022,f2838])).
% 2.29/0.66  fof(f2838,plain,(
% 2.29/0.66    ( ! [X2,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) = k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2)) )),
% 2.29/0.66    inference(forward_demodulation,[],[f2741,f49])).
% 2.29/0.66  fof(f2741,plain,(
% 2.29/0.66    ( ! [X2,X3] : (k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))),X2) = k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))))) )),
% 2.29/0.66    inference(superposition,[],[f92,f143])).
% 2.29/0.66  fof(f143,plain,(
% 2.29/0.66    ( ! [X10,X9] : (k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X9),X10))) = k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X9),X10))),X9)) )),
% 2.29/0.66    inference(resolution,[],[f133,f84])).
% 2.29/0.66  fof(f3022,plain,(
% 2.29/0.66    ( ! [X10,X8,X9] : (r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X9),X8))),X10),k9_relat_1(k6_relat_1(X8),X10))) )),
% 2.29/0.66    inference(superposition,[],[f2815,f455])).
% 2.29/0.66  fof(f2815,plain,(
% 2.29/0.66    ( ! [X208,X209,X207] : (r1_tarski(k9_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X207),X208))),X209),k9_relat_1(k6_relat_1(X207),X209))) )),
% 2.29/0.66    inference(superposition,[],[f1632,f143])).
% 2.29/0.66  fof(f1632,plain,(
% 2.29/0.66    ( ! [X6,X7,X5] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X6),X5),X7),k9_relat_1(k6_relat_1(X5),X7))) )),
% 2.29/0.66    inference(superposition,[],[f1581,f455])).
% 2.29/0.66  fof(f1581,plain,(
% 2.29/0.66    ( ! [X14,X15,X13] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X13),X15),X14),k9_relat_1(k6_relat_1(X13),X14))) )),
% 2.29/0.66    inference(superposition,[],[f247,f1540])).
% 2.29/0.66  fof(f1540,plain,(
% 2.29/0.66    ( ! [X4,X5,X3] : (k9_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k9_relat_1(k7_relat_1(k6_relat_1(X3),X5),X4)) )),
% 2.29/0.66    inference(superposition,[],[f769,f99])).
% 2.29/0.66  fof(f769,plain,(
% 2.29/0.66    ( ! [X14,X15,X13] : (k9_relat_1(k7_relat_1(k6_relat_1(X13),X14),X15) = k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X13),X15),X14))) )),
% 2.29/0.66    inference(superposition,[],[f99,f748])).
% 2.29/0.66  fof(f748,plain,(
% 2.29/0.66    ( ! [X4,X5,X3] : (k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X5) = k7_relat_1(k7_relat_1(k6_relat_1(X3),X5),X4)) )),
% 2.29/0.66    inference(superposition,[],[f476,f360])).
% 2.29/0.66  fof(f476,plain,(
% 2.29/0.66    ( ! [X33,X34,X32] : (k7_relat_1(k7_relat_1(k6_relat_1(X34),X32),X33) = k8_relat_1(X34,k7_relat_1(k6_relat_1(X33),X32))) )),
% 2.29/0.66    inference(superposition,[],[f360,f455])).
% 2.29/0.66  fof(f247,plain,(
% 2.29/0.66    ( ! [X4,X2,X3] : (r1_tarski(k9_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2),k9_relat_1(k6_relat_1(X3),X4))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f246,f99])).
% 2.29/0.66  fof(f246,plain,(
% 2.29/0.66    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2)),k9_relat_1(k6_relat_1(X3),X4))) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f243,f46])).
% 2.29/0.66  fof(f243,plain,(
% 2.29/0.66    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X3),X4),X2)),k9_relat_1(k6_relat_1(X3),X4)) | ~v1_relat_1(k6_relat_1(X2))) )),
% 2.29/0.66    inference(superposition,[],[f120,f100])).
% 2.29/0.66  fof(f120,plain,(
% 2.29/0.66    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X4)) )),
% 2.29/0.66    inference(subsumption_resolution,[],[f113,f98])).
% 2.29/0.66  fof(f113,plain,(
% 2.29/0.66    ( ! [X4,X2,X3] : (r1_tarski(k2_relat_1(k5_relat_1(X4,k7_relat_1(k6_relat_1(X2),X3))),k9_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) | ~v1_relat_1(X4)) )),
% 2.29/0.66    inference(superposition,[],[f51,f92])).
% 2.29/0.66  fof(f4523,plain,(
% 2.29/0.66    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k9_relat_1(k6_relat_1(sK0),sK1))),
% 2.29/0.66    inference(backward_demodulation,[],[f394,f4247])).
% 2.29/0.66  fof(f4247,plain,(
% 2.29/0.66    ( ! [X4,X5] : (k9_relat_1(k6_relat_1(X4),X5) = k1_relat_1(k7_relat_1(k6_relat_1(X4),X5))) )),
% 2.29/0.66    inference(superposition,[],[f48,f4067])).
% 2.29/0.66  fof(f394,plain,(
% 2.29/0.66    k7_relat_1(k6_relat_1(sK0),sK1) != k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1)))),
% 2.29/0.66    inference(backward_demodulation,[],[f91,f391])).
% 2.29/0.66  fof(f391,plain,(
% 2.29/0.66    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X4))) )),
% 2.29/0.66    inference(forward_demodulation,[],[f388,f48])).
% 2.29/0.66  fof(f388,plain,(
% 2.29/0.66    ( ! [X4,X3] : (k1_relat_1(k7_relat_1(k6_relat_1(X3),X4)) = k1_setfam_1(k6_enumset1(k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),k1_relat_1(k6_relat_1(X3)),X4))) )),
% 2.29/0.66    inference(resolution,[],[f77,f46])).
% 2.29/0.66  fof(f77,plain,(
% 2.29/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k1_setfam_1(k6_enumset1(k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),k1_relat_1(X1),X0))) )),
% 2.29/0.66    inference(definition_unfolding,[],[f59,f75])).
% 2.29/0.66  fof(f75,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.29/0.66    inference(definition_unfolding,[],[f53,f74])).
% 2.29/0.66  fof(f74,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.29/0.66    inference(definition_unfolding,[],[f54,f73])).
% 2.29/0.66  fof(f73,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.29/0.66    inference(definition_unfolding,[],[f65,f72])).
% 2.29/0.66  fof(f72,plain,(
% 2.29/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.29/0.66    inference(definition_unfolding,[],[f66,f71])).
% 2.29/0.66  fof(f71,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.29/0.66    inference(definition_unfolding,[],[f67,f70])).
% 2.29/0.66  fof(f70,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.29/0.66    inference(definition_unfolding,[],[f68,f69])).
% 2.29/0.66  fof(f69,plain,(
% 2.29/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f6])).
% 2.29/0.66  fof(f6,axiom,(
% 2.29/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.29/0.66  fof(f68,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f5])).
% 2.29/0.66  fof(f5,axiom,(
% 2.29/0.66    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.29/0.66  fof(f67,plain,(
% 2.29/0.66    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f4])).
% 2.29/0.66  fof(f4,axiom,(
% 2.29/0.66    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.29/0.66  fof(f66,plain,(
% 2.29/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f3])).
% 2.29/0.66  fof(f3,axiom,(
% 2.29/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.29/0.66  fof(f65,plain,(
% 2.29/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f2])).
% 2.29/0.66  fof(f2,axiom,(
% 2.29/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.29/0.66  fof(f54,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f1])).
% 2.29/0.66  fof(f1,axiom,(
% 2.29/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.29/0.66  fof(f53,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f7])).
% 2.29/0.66  fof(f7,axiom,(
% 2.29/0.66    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.29/0.66  fof(f59,plain,(
% 2.29/0.66    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.29/0.66    inference(cnf_transformation,[],[f34])).
% 2.29/0.66  fof(f34,plain,(
% 2.29/0.66    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f21])).
% 2.29/0.66  fof(f21,axiom,(
% 2.29/0.66    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 2.29/0.66  fof(f91,plain,(
% 2.29/0.66    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 2.29/0.66    inference(backward_demodulation,[],[f87,f90])).
% 2.29/0.66  fof(f87,plain,(
% 2.29/0.66    k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 2.29/0.66    inference(backward_demodulation,[],[f76,f85])).
% 2.29/0.66  fof(f76,plain,(
% 2.29/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k1_setfam_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.29/0.66    inference(definition_unfolding,[],[f45,f75])).
% 2.29/0.66  fof(f45,plain,(
% 2.29/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.29/0.66    inference(cnf_transformation,[],[f44])).
% 2.29/0.66  fof(f44,plain,(
% 2.29/0.66    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.29/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f43])).
% 2.29/0.66  fof(f43,plain,(
% 2.29/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.29/0.66    introduced(choice_axiom,[])).
% 2.29/0.66  fof(f26,plain,(
% 2.29/0.66    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.29/0.66    inference(ennf_transformation,[],[f25])).
% 2.29/0.66  fof(f25,negated_conjecture,(
% 2.29/0.66    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.29/0.66    inference(negated_conjecture,[],[f24])).
% 2.29/0.66  fof(f24,conjecture,(
% 2.29/0.66    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.29/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 2.29/0.66  % SZS output end Proof for theBenchmark
% 2.29/0.66  % (3513)------------------------------
% 2.29/0.66  % (3513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.66  % (3513)Termination reason: Refutation
% 2.29/0.66  
% 2.29/0.66  % (3513)Memory used [KB]: 12920
% 2.29/0.66  % (3513)Time elapsed: 0.232 s
% 2.29/0.66  % (3513)------------------------------
% 2.29/0.66  % (3513)------------------------------
% 2.29/0.67  % (3503)Success in time 0.3 s
%------------------------------------------------------------------------------
