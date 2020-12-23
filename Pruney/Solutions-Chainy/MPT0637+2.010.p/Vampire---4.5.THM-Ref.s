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
% DateTime   : Thu Dec  3 12:52:23 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 221 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  124 ( 345 expanded)
%              Number of equality atoms :   69 ( 140 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3151,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f3086])).

fof(f3086,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(superposition,[],[f89,f2917])).

fof(f2917,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(backward_demodulation,[],[f175,f2916])).

fof(f2916,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f2905,f253])).

fof(f253,plain,(
    ! [X2,X3] : k6_relat_1(k3_xboole_0(X2,X3)) = k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3))) ),
    inference(resolution,[],[f231,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f104,f87])).

fof(f87,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f56,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f102,f46])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f60,f44])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f231,plain,(
    ! [X4,X3] : r1_tarski(k3_xboole_0(X4,X3),X3) ),
    inference(superposition,[],[f49,f134])).

fof(f134,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f71,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2905,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k3_xboole_0(X0,X1)))) ),
    inference(superposition,[],[f649,f221])).

fof(f221,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f211,f98])).

fof(f98,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f97,f94])).

fof(f94,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f92,f87])).

fof(f92,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f57,f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f97,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f95,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f211,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(resolution,[],[f183,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f183,plain,(
    ! [X4,X3] : v1_relat_1(k8_relat_1(X4,k6_relat_1(X3))) ),
    inference(superposition,[],[f70,f101])).

fof(f101,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0)) ),
    inference(forward_demodulation,[],[f99,f45])).

fof(f99,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0)) ),
    inference(resolution,[],[f59,f44])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f55,f44])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f649,plain,(
    ! [X14,X12,X13] : k5_relat_1(k6_relat_1(X12),k8_relat_1(X13,k6_relat_1(X14))) = k8_relat_1(X13,k8_relat_1(X14,k6_relat_1(X12))) ),
    inference(backward_demodulation,[],[f215,f646])).

fof(f646,plain,(
    ! [X28,X26,X27] : k7_relat_1(k8_relat_1(X28,k6_relat_1(X27)),X26) = k8_relat_1(X28,k8_relat_1(X27,k6_relat_1(X26))) ),
    inference(forward_demodulation,[],[f645,f214])).

fof(f214,plain,(
    ! [X10,X11,X9] : k8_relat_1(X9,k8_relat_1(X10,k6_relat_1(X11))) = k5_relat_1(k8_relat_1(X10,k6_relat_1(X11)),k6_relat_1(X9)) ),
    inference(resolution,[],[f183,f56])).

fof(f645,plain,(
    ! [X28,X26,X27] : k7_relat_1(k8_relat_1(X28,k6_relat_1(X27)),X26) = k5_relat_1(k8_relat_1(X27,k6_relat_1(X26)),k6_relat_1(X28)) ),
    inference(forward_demodulation,[],[f644,f87])).

fof(f644,plain,(
    ! [X28,X26,X27] : k5_relat_1(k5_relat_1(k6_relat_1(X26),k6_relat_1(X27)),k6_relat_1(X28)) = k7_relat_1(k8_relat_1(X28,k6_relat_1(X27)),X26) ),
    inference(forward_demodulation,[],[f637,f215])).

fof(f637,plain,(
    ! [X28,X26,X27] : k5_relat_1(k5_relat_1(k6_relat_1(X26),k6_relat_1(X27)),k6_relat_1(X28)) = k5_relat_1(k6_relat_1(X26),k8_relat_1(X28,k6_relat_1(X27))) ),
    inference(resolution,[],[f193,f44])).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f190,f87])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f112,f44])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f48,f44])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f215,plain,(
    ! [X14,X12,X13] : k5_relat_1(k6_relat_1(X12),k8_relat_1(X13,k6_relat_1(X14))) = k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X12) ),
    inference(resolution,[],[f183,f57])).

fof(f175,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2))) ),
    inference(resolution,[],[f105,f49])).

fof(f89,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f43,f87])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:54:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (9930)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (9953)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.21/0.53  % (9940)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.21/0.53  % (9938)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.21/0.53  % (9948)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.21/0.53  % (9940)Refutation not found, incomplete strategy% (9940)------------------------------
% 1.21/0.53  % (9940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (9932)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.53  % (9940)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (9940)Memory used [KB]: 1663
% 1.21/0.53  % (9940)Time elapsed: 0.062 s
% 1.21/0.53  % (9940)------------------------------
% 1.21/0.53  % (9940)------------------------------
% 1.21/0.54  % (9953)Refutation not found, incomplete strategy% (9953)------------------------------
% 1.21/0.54  % (9953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (9938)Refutation not found, incomplete strategy% (9938)------------------------------
% 1.21/0.54  % (9938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (9953)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.54  
% 1.21/0.54  % (9953)Memory used [KB]: 6140
% 1.21/0.54  % (9953)Time elapsed: 0.127 s
% 1.21/0.54  % (9953)------------------------------
% 1.21/0.54  % (9953)------------------------------
% 1.21/0.54  % (9938)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.54  
% 1.21/0.54  % (9938)Memory used [KB]: 10618
% 1.21/0.54  % (9938)Time elapsed: 0.129 s
% 1.21/0.54  % (9938)------------------------------
% 1.21/0.54  % (9938)------------------------------
% 1.21/0.54  % (9933)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.21/0.54  % (9944)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.21/0.54  % (9944)Refutation not found, incomplete strategy% (9944)------------------------------
% 1.21/0.54  % (9944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.54  % (9944)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.54  
% 1.21/0.54  % (9944)Memory used [KB]: 1663
% 1.21/0.54  % (9944)Time elapsed: 0.130 s
% 1.21/0.54  % (9944)------------------------------
% 1.21/0.54  % (9944)------------------------------
% 1.21/0.54  % (9931)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.21/0.54  % (9928)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  % (9952)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (9939)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.55  % (9952)Refutation not found, incomplete strategy% (9952)------------------------------
% 1.39/0.55  % (9952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (9952)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (9952)Memory used [KB]: 6140
% 1.39/0.55  % (9952)Time elapsed: 0.127 s
% 1.39/0.55  % (9952)------------------------------
% 1.39/0.55  % (9952)------------------------------
% 1.39/0.55  % (9937)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.55  % (9929)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.39/0.55  % (9955)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.55  % (9941)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.55  % (9947)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.56  % (9954)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.56  % (9934)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.56  % (9954)Refutation not found, incomplete strategy% (9954)------------------------------
% 1.39/0.56  % (9954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9954)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9954)Memory used [KB]: 10746
% 1.39/0.56  % (9954)Time elapsed: 0.148 s
% 1.39/0.56  % (9954)------------------------------
% 1.39/0.56  % (9954)------------------------------
% 1.39/0.56  % (9943)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.56  % (9955)Refutation not found, incomplete strategy% (9955)------------------------------
% 1.39/0.56  % (9955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9955)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9926)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.56  % (9943)Refutation not found, incomplete strategy% (9943)------------------------------
% 1.39/0.56  % (9943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9943)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9943)Memory used [KB]: 1663
% 1.39/0.56  % (9943)Time elapsed: 0.147 s
% 1.39/0.56  % (9943)------------------------------
% 1.39/0.56  % (9943)------------------------------
% 1.39/0.56  % (9950)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.56  % (9927)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.56  % (9927)Refutation not found, incomplete strategy% (9927)------------------------------
% 1.39/0.56  % (9927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9927)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9927)Memory used [KB]: 1663
% 1.39/0.56  % (9927)Time elapsed: 0.143 s
% 1.39/0.56  % (9927)------------------------------
% 1.39/0.56  % (9927)------------------------------
% 1.39/0.56  % (9946)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.56  % (9937)Refutation not found, incomplete strategy% (9937)------------------------------
% 1.39/0.56  % (9937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9936)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.56  % (9937)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9937)Memory used [KB]: 6140
% 1.39/0.56  % (9937)Time elapsed: 0.151 s
% 1.39/0.56  % (9937)------------------------------
% 1.39/0.56  % (9937)------------------------------
% 1.39/0.56  % (9936)Refutation not found, incomplete strategy% (9936)------------------------------
% 1.39/0.56  % (9936)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (9936)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (9936)Memory used [KB]: 10618
% 1.39/0.56  % (9936)Time elapsed: 0.149 s
% 1.39/0.56  % (9936)------------------------------
% 1.39/0.56  % (9936)------------------------------
% 1.39/0.56  % (9942)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.56  % (9955)Memory used [KB]: 1663
% 1.39/0.56  % (9955)Time elapsed: 0.004 s
% 1.39/0.56  % (9955)------------------------------
% 1.39/0.56  % (9955)------------------------------
% 1.39/0.56  % (9942)Refutation not found, incomplete strategy% (9942)------------------------------
% 1.39/0.56  % (9942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (9951)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.57  % (9935)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.57  % (9950)Refutation not found, incomplete strategy% (9950)------------------------------
% 1.39/0.57  % (9950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (9945)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.58  % (9949)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.58  % (9951)Refutation not found, incomplete strategy% (9951)------------------------------
% 1.39/0.58  % (9951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (9951)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (9951)Memory used [KB]: 6140
% 1.39/0.58  % (9951)Time elapsed: 0.164 s
% 1.39/0.58  % (9951)------------------------------
% 1.39/0.58  % (9951)------------------------------
% 1.39/0.58  % (9942)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (9942)Memory used [KB]: 10618
% 1.39/0.58  % (9942)Time elapsed: 0.147 s
% 1.39/0.58  % (9942)------------------------------
% 1.39/0.58  % (9942)------------------------------
% 1.39/0.58  % (9950)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (9950)Memory used [KB]: 10618
% 1.39/0.58  % (9950)Time elapsed: 0.156 s
% 1.39/0.58  % (9950)------------------------------
% 1.39/0.58  % (9950)------------------------------
% 1.94/0.65  % (10026)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.94/0.66  % (10022)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.94/0.67  % (9929)Refutation not found, incomplete strategy% (9929)------------------------------
% 1.94/0.67  % (9929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.67  % (9929)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.67  
% 1.94/0.67  % (9929)Memory used [KB]: 6140
% 1.94/0.67  % (9929)Time elapsed: 0.246 s
% 1.94/0.67  % (9929)------------------------------
% 1.94/0.67  % (9929)------------------------------
% 1.94/0.67  % (10034)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 1.94/0.67  % (10025)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.94/0.68  % (10027)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.94/0.68  % (10027)Refutation not found, incomplete strategy% (10027)------------------------------
% 1.94/0.68  % (10027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.68  % (10027)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.68  
% 1.94/0.68  % (10027)Memory used [KB]: 10618
% 1.94/0.68  % (10027)Time elapsed: 0.092 s
% 1.94/0.68  % (10027)------------------------------
% 1.94/0.68  % (10027)------------------------------
% 2.16/0.69  % (9928)Refutation not found, incomplete strategy% (9928)------------------------------
% 2.16/0.69  % (9928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.69  % (9928)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.69  
% 2.16/0.69  % (9928)Memory used [KB]: 6140
% 2.16/0.69  % (9928)Time elapsed: 0.265 s
% 2.16/0.69  % (9928)------------------------------
% 2.16/0.69  % (9928)------------------------------
% 2.16/0.69  % (10030)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.16/0.69  % (10029)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.16/0.69  % (10028)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.16/0.69  % (10029)Refutation not found, incomplete strategy% (10029)------------------------------
% 2.16/0.69  % (10029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.69  % (10029)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.69  
% 2.16/0.69  % (10029)Memory used [KB]: 1663
% 2.16/0.69  % (10029)Time elapsed: 0.103 s
% 2.16/0.69  % (10029)------------------------------
% 2.16/0.69  % (10029)------------------------------
% 2.16/0.70  % (9941)Refutation not found, incomplete strategy% (9941)------------------------------
% 2.16/0.70  % (9941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (9941)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (9941)Memory used [KB]: 6140
% 2.16/0.70  % (9941)Time elapsed: 0.219 s
% 2.16/0.70  % (9941)------------------------------
% 2.16/0.70  % (9941)------------------------------
% 2.16/0.70  % (10033)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.16/0.70  % (10033)Refutation not found, incomplete strategy% (10033)------------------------------
% 2.16/0.70  % (10033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (10033)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (10033)Memory used [KB]: 10618
% 2.16/0.70  % (10033)Time elapsed: 0.111 s
% 2.16/0.70  % (10033)------------------------------
% 2.16/0.70  % (10033)------------------------------
% 2.16/0.70  % (10035)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.16/0.70  % (10032)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.16/0.70  % (10035)Refutation not found, incomplete strategy% (10035)------------------------------
% 2.16/0.70  % (10035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (10035)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (10035)Memory used [KB]: 10618
% 2.16/0.70  % (10035)Time elapsed: 0.096 s
% 2.16/0.70  % (10035)------------------------------
% 2.16/0.70  % (10035)------------------------------
% 2.16/0.70  % (9934)Refutation not found, incomplete strategy% (9934)------------------------------
% 2.16/0.70  % (9934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (9934)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.70  
% 2.16/0.70  % (9934)Memory used [KB]: 6140
% 2.16/0.70  % (9934)Time elapsed: 0.291 s
% 2.16/0.70  % (9934)------------------------------
% 2.16/0.70  % (9934)------------------------------
% 2.16/0.70  % (10031)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.16/0.70  % (10036)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.16/0.71  % (10028)Refutation not found, incomplete strategy% (10028)------------------------------
% 2.16/0.71  % (10028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.71  % (10028)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.71  
% 2.16/0.71  % (10028)Memory used [KB]: 10618
% 2.16/0.71  % (10028)Time elapsed: 0.133 s
% 2.16/0.71  % (10028)------------------------------
% 2.16/0.71  % (10028)------------------------------
% 2.16/0.72  % (10037)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.16/0.72  % (10030)Refutation not found, incomplete strategy% (10030)------------------------------
% 2.16/0.72  % (10030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.72  % (10030)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.72  
% 2.16/0.72  % (10030)Memory used [KB]: 10618
% 2.16/0.72  % (10030)Time elapsed: 0.104 s
% 2.16/0.72  % (10030)------------------------------
% 2.16/0.72  % (10030)------------------------------
% 2.16/0.72  % (10037)Refutation not found, incomplete strategy% (10037)------------------------------
% 2.16/0.72  % (10037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.72  % (10037)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.72  
% 2.16/0.72  % (10037)Memory used [KB]: 10618
% 2.16/0.72  % (10037)Time elapsed: 0.115 s
% 2.16/0.72  % (10037)------------------------------
% 2.16/0.72  % (10037)------------------------------
% 2.70/0.76  % (9933)Refutation found. Thanks to Tanya!
% 2.70/0.76  % SZS status Theorem for theBenchmark
% 2.70/0.76  % SZS output start Proof for theBenchmark
% 2.70/0.76  fof(f3151,plain,(
% 2.70/0.76    $false),
% 2.70/0.76    inference(trivial_inequality_removal,[],[f3086])).
% 2.70/0.76  fof(f3086,plain,(
% 2.70/0.76    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 2.70/0.76    inference(superposition,[],[f89,f2917])).
% 2.70/0.76  fof(f2917,plain,(
% 2.70/0.76    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(X2))) )),
% 2.70/0.76    inference(backward_demodulation,[],[f175,f2916])).
% 2.70/0.76  fof(f2916,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k6_relat_1(k3_xboole_0(X0,X1)))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f2905,f253])).
% 2.70/0.76  fof(f253,plain,(
% 2.70/0.76    ( ! [X2,X3] : (k6_relat_1(k3_xboole_0(X2,X3)) = k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3)))) )),
% 2.70/0.76    inference(resolution,[],[f231,f105])).
% 2.70/0.76  fof(f105,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f104,f87])).
% 2.70/0.76  fof(f87,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 2.70/0.76    inference(resolution,[],[f56,f44])).
% 2.70/0.76  fof(f44,plain,(
% 2.70/0.76    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f24])).
% 2.70/0.76  fof(f24,plain,(
% 2.70/0.76    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.70/0.76    inference(pure_predicate_removal,[],[f21])).
% 2.70/0.76  fof(f21,axiom,(
% 2.70/0.76    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.70/0.76  fof(f56,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f29])).
% 2.70/0.76  fof(f29,plain,(
% 2.70/0.76    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 2.70/0.76    inference(ennf_transformation,[],[f12])).
% 2.70/0.76  fof(f12,axiom,(
% 2.70/0.76    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 2.70/0.76  fof(f104,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f102,f46])).
% 2.70/0.76  fof(f46,plain,(
% 2.70/0.76    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.70/0.76    inference(cnf_transformation,[],[f15])).
% 2.70/0.76  fof(f15,axiom,(
% 2.70/0.76    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.70/0.76  fof(f102,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 2.70/0.76    inference(resolution,[],[f60,f44])).
% 2.70/0.76  fof(f60,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 2.70/0.76    inference(cnf_transformation,[],[f34])).
% 2.70/0.76  fof(f34,plain,(
% 2.70/0.76    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.70/0.76    inference(flattening,[],[f33])).
% 2.70/0.76  fof(f33,plain,(
% 2.70/0.76    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.70/0.76    inference(ennf_transformation,[],[f18])).
% 2.70/0.76  fof(f18,axiom,(
% 2.70/0.76    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 2.70/0.76  fof(f231,plain,(
% 2.70/0.76    ( ! [X4,X3] : (r1_tarski(k3_xboole_0(X4,X3),X3)) )),
% 2.70/0.76    inference(superposition,[],[f49,f134])).
% 2.70/0.76  fof(f134,plain,(
% 2.70/0.76    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 2.70/0.76    inference(superposition,[],[f71,f52])).
% 2.70/0.76  fof(f52,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f10])).
% 2.70/0.76  fof(f10,axiom,(
% 2.70/0.76    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.70/0.76  fof(f71,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 2.70/0.76    inference(superposition,[],[f52,f50])).
% 2.70/0.76  fof(f50,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f7])).
% 2.70/0.76  fof(f7,axiom,(
% 2.70/0.76    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.70/0.76  fof(f49,plain,(
% 2.70/0.76    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f3])).
% 2.70/0.76  fof(f3,axiom,(
% 2.70/0.76    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.70/0.76  fof(f2905,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X0,k8_relat_1(X1,k6_relat_1(k3_xboole_0(X0,X1))))) )),
% 2.70/0.76    inference(superposition,[],[f649,f221])).
% 2.70/0.76  fof(f221,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),k8_relat_1(X0,k6_relat_1(X1)))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f211,f98])).
% 2.70/0.76  fof(f98,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f97,f94])).
% 2.70/0.76  fof(f94,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 2.70/0.76    inference(forward_demodulation,[],[f92,f87])).
% 2.70/0.76  fof(f92,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 2.70/0.76    inference(resolution,[],[f57,f44])).
% 2.70/0.76  fof(f57,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f30])).
% 2.70/0.76  fof(f30,plain,(
% 2.70/0.76    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.70/0.76    inference(ennf_transformation,[],[f20])).
% 2.70/0.76  fof(f20,axiom,(
% 2.70/0.76    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.70/0.76  fof(f97,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f95,f45])).
% 2.70/0.76  fof(f45,plain,(
% 2.70/0.76    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.70/0.76    inference(cnf_transformation,[],[f15])).
% 2.70/0.76  fof(f95,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 2.70/0.76    inference(resolution,[],[f58,f44])).
% 2.70/0.76  fof(f58,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f31])).
% 2.70/0.76  fof(f31,plain,(
% 2.70/0.76    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.70/0.76    inference(ennf_transformation,[],[f19])).
% 2.70/0.76  fof(f19,axiom,(
% 2.70/0.76    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 2.70/0.76  fof(f211,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k5_relat_1(k6_relat_1(k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))),k8_relat_1(X0,k6_relat_1(X1)))) )),
% 2.70/0.76    inference(resolution,[],[f183,f47])).
% 2.70/0.76  fof(f47,plain,(
% 2.70/0.76    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.70/0.76    inference(cnf_transformation,[],[f26])).
% 2.70/0.76  fof(f26,plain,(
% 2.70/0.76    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.70/0.76    inference(ennf_transformation,[],[f17])).
% 2.70/0.76  fof(f17,axiom,(
% 2.70/0.76    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 2.70/0.76  fof(f183,plain,(
% 2.70/0.76    ( ! [X4,X3] : (v1_relat_1(k8_relat_1(X4,k6_relat_1(X3)))) )),
% 2.70/0.76    inference(superposition,[],[f70,f101])).
% 2.70/0.76  fof(f101,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(X1,X0))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f99,f45])).
% 2.70/0.76  fof(f99,plain,(
% 2.70/0.76    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k3_xboole_0(k6_relat_1(X1),k2_zfmisc_1(k1_relat_1(k6_relat_1(X1)),X0))) )),
% 2.70/0.76    inference(resolution,[],[f59,f44])).
% 2.70/0.76  fof(f59,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f32])).
% 2.70/0.76  fof(f32,plain,(
% 2.70/0.76    ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.70/0.76    inference(ennf_transformation,[],[f13])).
% 2.70/0.76  fof(f13,axiom,(
% 2.70/0.76    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).
% 2.70/0.76  fof(f70,plain,(
% 2.70/0.76    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) )),
% 2.70/0.76    inference(resolution,[],[f55,f44])).
% 2.70/0.76  fof(f55,plain,(
% 2.70/0.76    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 2.70/0.76    inference(cnf_transformation,[],[f28])).
% 2.70/0.76  fof(f28,plain,(
% 2.70/0.76    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 2.70/0.76    inference(ennf_transformation,[],[f11])).
% 2.70/0.76  fof(f11,axiom,(
% 2.70/0.76    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 2.70/0.76  fof(f649,plain,(
% 2.70/0.76    ( ! [X14,X12,X13] : (k5_relat_1(k6_relat_1(X12),k8_relat_1(X13,k6_relat_1(X14))) = k8_relat_1(X13,k8_relat_1(X14,k6_relat_1(X12)))) )),
% 2.70/0.76    inference(backward_demodulation,[],[f215,f646])).
% 2.70/0.76  fof(f646,plain,(
% 2.70/0.76    ( ! [X28,X26,X27] : (k7_relat_1(k8_relat_1(X28,k6_relat_1(X27)),X26) = k8_relat_1(X28,k8_relat_1(X27,k6_relat_1(X26)))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f645,f214])).
% 2.70/0.76  fof(f214,plain,(
% 2.70/0.76    ( ! [X10,X11,X9] : (k8_relat_1(X9,k8_relat_1(X10,k6_relat_1(X11))) = k5_relat_1(k8_relat_1(X10,k6_relat_1(X11)),k6_relat_1(X9))) )),
% 2.70/0.76    inference(resolution,[],[f183,f56])).
% 2.70/0.76  fof(f645,plain,(
% 2.70/0.76    ( ! [X28,X26,X27] : (k7_relat_1(k8_relat_1(X28,k6_relat_1(X27)),X26) = k5_relat_1(k8_relat_1(X27,k6_relat_1(X26)),k6_relat_1(X28))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f644,f87])).
% 2.70/0.76  fof(f644,plain,(
% 2.70/0.76    ( ! [X28,X26,X27] : (k5_relat_1(k5_relat_1(k6_relat_1(X26),k6_relat_1(X27)),k6_relat_1(X28)) = k7_relat_1(k8_relat_1(X28,k6_relat_1(X27)),X26)) )),
% 2.70/0.76    inference(forward_demodulation,[],[f637,f215])).
% 2.70/0.76  fof(f637,plain,(
% 2.70/0.76    ( ! [X28,X26,X27] : (k5_relat_1(k5_relat_1(k6_relat_1(X26),k6_relat_1(X27)),k6_relat_1(X28)) = k5_relat_1(k6_relat_1(X26),k8_relat_1(X28,k6_relat_1(X27)))) )),
% 2.70/0.76    inference(resolution,[],[f193,f44])).
% 2.70/0.76  fof(f193,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1)))) )),
% 2.70/0.76    inference(forward_demodulation,[],[f190,f87])).
% 2.70/0.76  fof(f190,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.70/0.76    inference(resolution,[],[f112,f44])).
% 2.70/0.76  fof(f112,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 2.70/0.76    inference(resolution,[],[f48,f44])).
% 2.70/0.76  fof(f48,plain,(
% 2.70/0.76    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.70/0.76    inference(cnf_transformation,[],[f27])).
% 2.70/0.76  fof(f27,plain,(
% 2.70/0.76    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.70/0.76    inference(ennf_transformation,[],[f14])).
% 2.70/0.76  fof(f14,axiom,(
% 2.70/0.76    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.70/0.76  fof(f215,plain,(
% 2.70/0.76    ( ! [X14,X12,X13] : (k5_relat_1(k6_relat_1(X12),k8_relat_1(X13,k6_relat_1(X14))) = k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X12)) )),
% 2.70/0.76    inference(resolution,[],[f183,f57])).
% 2.70/0.76  fof(f175,plain,(
% 2.70/0.76    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2)))) )),
% 2.70/0.76    inference(resolution,[],[f105,f49])).
% 2.70/0.76  fof(f89,plain,(
% 2.70/0.76    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 2.70/0.76    inference(backward_demodulation,[],[f43,f87])).
% 2.70/0.76  fof(f43,plain,(
% 2.70/0.76    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.70/0.76    inference(cnf_transformation,[],[f40])).
% 2.70/0.76  fof(f40,plain,(
% 2.70/0.76    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.70/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f39])).
% 2.70/0.76  fof(f39,plain,(
% 2.70/0.76    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 2.70/0.76    introduced(choice_axiom,[])).
% 2.70/0.76  fof(f25,plain,(
% 2.70/0.76    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 2.70/0.76    inference(ennf_transformation,[],[f23])).
% 2.70/0.76  fof(f23,negated_conjecture,(
% 2.70/0.76    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.70/0.76    inference(negated_conjecture,[],[f22])).
% 2.70/0.76  fof(f22,conjecture,(
% 2.70/0.76    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 2.70/0.76    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 2.70/0.76  % SZS output end Proof for theBenchmark
% 2.70/0.76  % (9933)------------------------------
% 2.70/0.76  % (9933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.76  % (9933)Termination reason: Refutation
% 2.70/0.76  
% 2.70/0.76  % (9933)Memory used [KB]: 4221
% 2.70/0.76  % (9933)Time elapsed: 0.319 s
% 2.70/0.76  % (9933)------------------------------
% 2.70/0.76  % (9933)------------------------------
% 2.70/0.77  % (9921)Success in time 0.39 s
%------------------------------------------------------------------------------
