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
% DateTime   : Thu Dec  3 12:53:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 227 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  162 ( 634 expanded)
%              Number of equality atoms :   59 ( 175 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(subsumption_resolution,[],[f192,f33])).

fof(f33,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f192,plain,(
    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f191,f106])).

fof(f106,plain,(
    sK0 = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f103,f30])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,
    ( sK0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f69,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f69,plain,(
    sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f67,f30])).

fof(f67,plain,
    ( ~ v1_relat_1(sK1)
    | sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f32,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

fof(f32,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f191,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(k2_relat_1(sK1),sK0) ),
    inference(forward_demodulation,[],[f189,f170])).

fof(f170,plain,(
    ! [X4] : k3_xboole_0(k2_relat_1(sK1),X4) = k3_xboole_0(X4,k9_relat_1(sK1,k10_relat_1(sK1,X4))) ),
    inference(forward_demodulation,[],[f169,f50])).

fof(f50,plain,(
    ! [X3] : k2_relat_1(k8_relat_1(X3,sK1)) = k3_xboole_0(k2_relat_1(sK1),X3) ),
    inference(resolution,[],[f30,f37])).

fof(f169,plain,(
    ! [X4] : k2_relat_1(k8_relat_1(X4,sK1)) = k3_xboole_0(X4,k9_relat_1(sK1,k10_relat_1(sK1,X4))) ),
    inference(forward_demodulation,[],[f168,f136])).

fof(f136,plain,(
    ! [X1] : k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,X1) ),
    inference(forward_demodulation,[],[f135,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f135,plain,(
    ! [X1] : k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1))) ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f47,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f134,plain,(
    ! [X1] :
      ( k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f133,f30])).

fof(f133,plain,(
    ! [X1] :
      ( k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1)))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f42,f57])).

fof(f57,plain,(
    ! [X9] : k8_relat_1(X9,sK1) = k5_relat_1(sK1,k6_relat_1(X9)) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f168,plain,(
    ! [X4] : k2_relat_1(k8_relat_1(X4,sK1)) = k3_xboole_0(X4,k9_relat_1(sK1,k1_relat_1(k8_relat_1(X4,sK1)))) ),
    inference(subsumption_resolution,[],[f165,f61])).

fof(f61,plain,(
    ! [X7] : v1_relat_1(k8_relat_1(X7,sK1)) ),
    inference(subsumption_resolution,[],[f55,f31])).

fof(f31,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X7] :
      ( ~ v1_funct_1(sK1)
      | v1_relat_1(k8_relat_1(X7,sK1)) ) ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f165,plain,(
    ! [X4] :
      ( k2_relat_1(k8_relat_1(X4,sK1)) = k3_xboole_0(X4,k9_relat_1(sK1,k1_relat_1(k8_relat_1(X4,sK1))))
      | ~ v1_relat_1(k8_relat_1(X4,sK1)) ) ),
    inference(superposition,[],[f58,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f58,plain,(
    ! [X0,X1] : k9_relat_1(k8_relat_1(X0,sK1),X1) = k3_xboole_0(X0,k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f48,f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK1)
      | k9_relat_1(k8_relat_1(X0,sK1),X1) = k3_xboole_0(X0,k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f30,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

fof(f189,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f151,f60])).

fof(f60,plain,(
    ! [X4] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4) ),
    inference(subsumption_resolution,[],[f52,f31])).

fof(f52,plain,(
    ! [X4] :
      ( ~ v1_funct_1(sK1)
      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4) ) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f151,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k3_xboole_0(sK0,X0) = X0 ) ),
    inference(backward_demodulation,[],[f108,f148])).

fof(f148,plain,(
    ! [X1] : k3_xboole_0(sK0,X1) = k3_xboole_0(k2_relat_1(sK1),k3_xboole_0(sK0,X1)) ),
    inference(resolution,[],[f59,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f59,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK1))
      | k3_xboole_0(k2_relat_1(sK1),X2) = X2 ) ),
    inference(backward_demodulation,[],[f49,f50])).

fof(f49,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(sK1))
      | k2_relat_1(k8_relat_1(X2,sK1)) = X2 ) ),
    inference(resolution,[],[f30,f36])).

fof(f108,plain,(
    ! [X0] :
      ( k3_xboole_0(k2_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0
      | ~ r1_tarski(X0,sK0) ) ),
    inference(forward_demodulation,[],[f107,f84])).

fof(f84,plain,(
    ! [X6,X5] : k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k2_relat_1(sK1),k3_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f83,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f83,plain,(
    ! [X6,X5] : k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k3_xboole_0(k2_relat_1(sK1),X6),X5) ),
    inference(forward_demodulation,[],[f72,f50])).

fof(f72,plain,(
    ! [X6,X5] : k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k2_relat_1(k8_relat_1(X6,sK1)),X5) ),
    inference(resolution,[],[f61,f37])).

fof(f107,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k2_relat_1(k8_relat_1(X0,k8_relat_1(sK0,sK1))) = X0 ) ),
    inference(subsumption_resolution,[],[f105,f61])).

fof(f105,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | ~ v1_relat_1(k8_relat_1(sK0,sK1))
      | k2_relat_1(k8_relat_1(X0,k8_relat_1(sK0,sK1))) = X0 ) ),
    inference(superposition,[],[f36,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (4476)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (4477)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (4492)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (4473)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (4494)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (4475)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (4496)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (4495)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (4483)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (4487)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (4476)Refutation not found, incomplete strategy% (4476)------------------------------
% 0.21/0.51  % (4476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4476)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4476)Memory used [KB]: 10490
% 0.21/0.51  % (4476)Time elapsed: 0.101 s
% 0.21/0.51  % (4476)------------------------------
% 0.21/0.51  % (4476)------------------------------
% 0.21/0.51  % (4480)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (4493)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (4478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (4489)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (4496)Refutation not found, incomplete strategy% (4496)------------------------------
% 0.21/0.52  % (4496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4485)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (4494)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % (4490)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.27/0.53  % (4481)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.27/0.53  % (4488)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.27/0.53  % (4482)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.27/0.53  % (4479)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.27/0.53  % (4491)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.27/0.54  % (4496)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (4496)Memory used [KB]: 10618
% 1.27/0.54  % (4496)Time elapsed: 0.106 s
% 1.27/0.54  % (4496)------------------------------
% 1.27/0.54  % (4496)------------------------------
% 1.27/0.54  % (4474)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.27/0.54  % SZS output start Proof for theBenchmark
% 1.27/0.54  fof(f193,plain,(
% 1.27/0.54    $false),
% 1.27/0.54    inference(subsumption_resolution,[],[f192,f33])).
% 1.27/0.54  fof(f33,plain,(
% 1.27/0.54    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 1.27/0.54    inference(cnf_transformation,[],[f16])).
% 1.27/0.54  fof(f16,plain,(
% 1.27/0.54    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.27/0.54    inference(flattening,[],[f15])).
% 1.27/0.54  fof(f15,plain,(
% 1.27/0.54    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.27/0.54    inference(ennf_transformation,[],[f14])).
% 1.27/0.54  fof(f14,negated_conjecture,(
% 1.27/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.27/0.54    inference(negated_conjecture,[],[f13])).
% 1.27/0.54  fof(f13,conjecture,(
% 1.27/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.27/0.54  fof(f192,plain,(
% 1.27/0.54    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 1.27/0.54    inference(forward_demodulation,[],[f191,f106])).
% 1.27/0.54  fof(f106,plain,(
% 1.27/0.54    sK0 = k3_xboole_0(k2_relat_1(sK1),sK0)),
% 1.27/0.54    inference(subsumption_resolution,[],[f103,f30])).
% 1.27/0.54  fof(f30,plain,(
% 1.27/0.54    v1_relat_1(sK1)),
% 1.27/0.54    inference(cnf_transformation,[],[f16])).
% 1.27/0.54  fof(f103,plain,(
% 1.27/0.54    sK0 = k3_xboole_0(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 1.27/0.54    inference(superposition,[],[f69,f37])).
% 1.27/0.54  fof(f37,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f21])).
% 1.27/0.54  fof(f21,plain,(
% 1.27/0.54    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f4])).
% 1.27/0.54  fof(f4,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 1.27/0.54  fof(f69,plain,(
% 1.27/0.54    sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 1.27/0.54    inference(subsumption_resolution,[],[f67,f30])).
% 1.27/0.54  fof(f67,plain,(
% 1.27/0.54    ~v1_relat_1(sK1) | sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 1.27/0.54    inference(resolution,[],[f32,f36])).
% 1.27/0.54  fof(f36,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | k2_relat_1(k8_relat_1(X0,X1)) = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f20])).
% 1.27/0.54  fof(f20,plain,(
% 1.27/0.54    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(flattening,[],[f19])).
% 1.27/0.54  fof(f19,plain,(
% 1.27/0.54    ! [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f5])).
% 1.27/0.54  fof(f5,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).
% 1.27/0.54  fof(f32,plain,(
% 1.27/0.54    r1_tarski(sK0,k2_relat_1(sK1))),
% 1.27/0.54    inference(cnf_transformation,[],[f16])).
% 1.27/0.54  fof(f191,plain,(
% 1.27/0.54    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(k2_relat_1(sK1),sK0)),
% 1.27/0.54    inference(forward_demodulation,[],[f189,f170])).
% 1.27/0.54  fof(f170,plain,(
% 1.27/0.54    ( ! [X4] : (k3_xboole_0(k2_relat_1(sK1),X4) = k3_xboole_0(X4,k9_relat_1(sK1,k10_relat_1(sK1,X4)))) )),
% 1.27/0.54    inference(forward_demodulation,[],[f169,f50])).
% 1.27/0.54  fof(f50,plain,(
% 1.27/0.54    ( ! [X3] : (k2_relat_1(k8_relat_1(X3,sK1)) = k3_xboole_0(k2_relat_1(sK1),X3)) )),
% 1.27/0.54    inference(resolution,[],[f30,f37])).
% 1.27/0.54  fof(f169,plain,(
% 1.27/0.54    ( ! [X4] : (k2_relat_1(k8_relat_1(X4,sK1)) = k3_xboole_0(X4,k9_relat_1(sK1,k10_relat_1(sK1,X4)))) )),
% 1.27/0.54    inference(forward_demodulation,[],[f168,f136])).
% 1.27/0.54  fof(f136,plain,(
% 1.27/0.54    ( ! [X1] : (k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,X1)) )),
% 1.27/0.54    inference(forward_demodulation,[],[f135,f39])).
% 1.27/0.54  fof(f39,plain,(
% 1.27/0.54    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.27/0.54    inference(cnf_transformation,[],[f9])).
% 1.27/0.54  fof(f9,axiom,(
% 1.27/0.54    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.27/0.54  fof(f135,plain,(
% 1.27/0.54    ( ! [X1] : (k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1)))) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f134,f47])).
% 1.27/0.54  fof(f47,plain,(
% 1.27/0.54    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f3])).
% 1.27/0.54  fof(f3,axiom,(
% 1.27/0.54    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.27/0.54  fof(f134,plain,(
% 1.27/0.54    ( ! [X1] : (k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f133,f30])).
% 1.27/0.54  fof(f133,plain,(
% 1.27/0.54    ( ! [X1] : (k1_relat_1(k8_relat_1(X1,sK1)) = k10_relat_1(sK1,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.27/0.54    inference(superposition,[],[f42,f57])).
% 1.27/0.54  fof(f57,plain,(
% 1.27/0.54    ( ! [X9] : (k8_relat_1(X9,sK1) = k5_relat_1(sK1,k6_relat_1(X9))) )),
% 1.27/0.54    inference(resolution,[],[f30,f46])).
% 1.27/0.54  fof(f46,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f29])).
% 1.27/0.54  fof(f29,plain,(
% 1.27/0.54    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f6])).
% 1.27/0.54  fof(f6,axiom,(
% 1.27/0.54    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.27/0.54  fof(f42,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f25])).
% 1.27/0.54  fof(f25,plain,(
% 1.27/0.54    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f8])).
% 1.27/0.54  fof(f8,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 1.27/0.54  fof(f168,plain,(
% 1.27/0.54    ( ! [X4] : (k2_relat_1(k8_relat_1(X4,sK1)) = k3_xboole_0(X4,k9_relat_1(sK1,k1_relat_1(k8_relat_1(X4,sK1))))) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f165,f61])).
% 1.27/0.54  fof(f61,plain,(
% 1.27/0.54    ( ! [X7] : (v1_relat_1(k8_relat_1(X7,sK1))) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f55,f31])).
% 1.27/0.54  fof(f31,plain,(
% 1.27/0.54    v1_funct_1(sK1)),
% 1.27/0.54    inference(cnf_transformation,[],[f16])).
% 1.27/0.54  fof(f55,plain,(
% 1.27/0.54    ( ! [X7] : (~v1_funct_1(sK1) | v1_relat_1(k8_relat_1(X7,sK1))) )),
% 1.27/0.54    inference(resolution,[],[f30,f44])).
% 1.27/0.54  fof(f44,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f28])).
% 1.27/0.54  fof(f28,plain,(
% 1.27/0.54    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(flattening,[],[f27])).
% 1.27/0.54  fof(f27,plain,(
% 1.27/0.54    ! [X0,X1] : ((v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.27/0.54    inference(ennf_transformation,[],[f10])).
% 1.27/0.54  fof(f10,axiom,(
% 1.27/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v1_funct_1(k8_relat_1(X0,X1)) & v1_relat_1(k8_relat_1(X0,X1))))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).
% 1.27/0.54  fof(f165,plain,(
% 1.27/0.54    ( ! [X4] : (k2_relat_1(k8_relat_1(X4,sK1)) = k3_xboole_0(X4,k9_relat_1(sK1,k1_relat_1(k8_relat_1(X4,sK1)))) | ~v1_relat_1(k8_relat_1(X4,sK1))) )),
% 1.27/0.54    inference(superposition,[],[f58,f38])).
% 1.27/0.54  fof(f38,plain,(
% 1.27/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f22])).
% 1.27/0.54  fof(f22,plain,(
% 1.27/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.27/0.54    inference(ennf_transformation,[],[f7])).
% 1.27/0.54  fof(f7,axiom,(
% 1.27/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.27/0.54  fof(f58,plain,(
% 1.27/0.54    ( ! [X0,X1] : (k9_relat_1(k8_relat_1(X0,sK1),X1) = k3_xboole_0(X0,k9_relat_1(sK1,X1))) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f48,f31])).
% 1.27/0.54  fof(f48,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_funct_1(sK1) | k9_relat_1(k8_relat_1(X0,sK1),X1) = k3_xboole_0(X0,k9_relat_1(sK1,X1))) )),
% 1.27/0.54    inference(resolution,[],[f30,f34])).
% 1.27/0.54  fof(f34,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f18])).
% 1.27/0.54  fof(f18,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.27/0.54    inference(flattening,[],[f17])).
% 1.27/0.54  fof(f17,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.27/0.54    inference(ennf_transformation,[],[f11])).
% 1.27/0.54  fof(f11,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(k8_relat_1(X0,X2),X1) = k3_xboole_0(X0,k9_relat_1(X2,X1)))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).
% 1.27/0.54  fof(f189,plain,(
% 1.27/0.54    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) = k3_xboole_0(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 1.27/0.54    inference(resolution,[],[f151,f60])).
% 1.27/0.54  fof(f60,plain,(
% 1.27/0.54    ( ! [X4] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4)) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f52,f31])).
% 1.27/0.54  fof(f52,plain,(
% 1.27/0.54    ( ! [X4] : (~v1_funct_1(sK1) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4)) )),
% 1.27/0.54    inference(resolution,[],[f30,f41])).
% 1.27/0.54  fof(f41,plain,(
% 1.27/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f24])).
% 1.27/0.54  fof(f24,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.27/0.54    inference(flattening,[],[f23])).
% 1.27/0.54  fof(f23,plain,(
% 1.27/0.54    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.27/0.54    inference(ennf_transformation,[],[f12])).
% 1.27/0.54  fof(f12,axiom,(
% 1.27/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.27/0.54  fof(f151,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | k3_xboole_0(sK0,X0) = X0) )),
% 1.27/0.54    inference(backward_demodulation,[],[f108,f148])).
% 1.27/0.54  fof(f148,plain,(
% 1.27/0.54    ( ! [X1] : (k3_xboole_0(sK0,X1) = k3_xboole_0(k2_relat_1(sK1),k3_xboole_0(sK0,X1))) )),
% 1.27/0.54    inference(resolution,[],[f59,f68])).
% 1.27/0.54  fof(f68,plain,(
% 1.27/0.54    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,X0),k2_relat_1(sK1))) )),
% 1.27/0.54    inference(resolution,[],[f32,f43])).
% 1.27/0.54  fof(f43,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 1.27/0.54    inference(cnf_transformation,[],[f26])).
% 1.27/0.54  fof(f26,plain,(
% 1.27/0.54    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.27/0.54    inference(ennf_transformation,[],[f1])).
% 1.27/0.54  fof(f1,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.27/0.54  fof(f59,plain,(
% 1.27/0.54    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK1)) | k3_xboole_0(k2_relat_1(sK1),X2) = X2) )),
% 1.27/0.54    inference(backward_demodulation,[],[f49,f50])).
% 1.27/0.54  fof(f49,plain,(
% 1.27/0.54    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(sK1)) | k2_relat_1(k8_relat_1(X2,sK1)) = X2) )),
% 1.27/0.54    inference(resolution,[],[f30,f36])).
% 1.27/0.54  fof(f108,plain,(
% 1.27/0.54    ( ! [X0] : (k3_xboole_0(k2_relat_1(sK1),k3_xboole_0(sK0,X0)) = X0 | ~r1_tarski(X0,sK0)) )),
% 1.27/0.54    inference(forward_demodulation,[],[f107,f84])).
% 1.27/0.54  fof(f84,plain,(
% 1.27/0.54    ( ! [X6,X5] : (k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k2_relat_1(sK1),k3_xboole_0(X6,X5))) )),
% 1.27/0.54    inference(forward_demodulation,[],[f83,f35])).
% 1.27/0.54  fof(f35,plain,(
% 1.27/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.27/0.54    inference(cnf_transformation,[],[f2])).
% 1.27/0.54  fof(f2,axiom,(
% 1.27/0.54    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.27/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.27/0.54  fof(f83,plain,(
% 1.27/0.54    ( ! [X6,X5] : (k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k3_xboole_0(k2_relat_1(sK1),X6),X5)) )),
% 1.27/0.54    inference(forward_demodulation,[],[f72,f50])).
% 1.27/0.54  fof(f72,plain,(
% 1.27/0.54    ( ! [X6,X5] : (k2_relat_1(k8_relat_1(X5,k8_relat_1(X6,sK1))) = k3_xboole_0(k2_relat_1(k8_relat_1(X6,sK1)),X5)) )),
% 1.27/0.54    inference(resolution,[],[f61,f37])).
% 1.27/0.54  fof(f107,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | k2_relat_1(k8_relat_1(X0,k8_relat_1(sK0,sK1))) = X0) )),
% 1.27/0.54    inference(subsumption_resolution,[],[f105,f61])).
% 1.27/0.54  fof(f105,plain,(
% 1.27/0.54    ( ! [X0] : (~r1_tarski(X0,sK0) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | k2_relat_1(k8_relat_1(X0,k8_relat_1(sK0,sK1))) = X0) )),
% 1.27/0.54    inference(superposition,[],[f36,f69])).
% 1.27/0.54  % SZS output end Proof for theBenchmark
% 1.27/0.54  % (4494)------------------------------
% 1.27/0.54  % (4494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (4494)Termination reason: Refutation
% 1.27/0.54  
% 1.27/0.54  % (4494)Memory used [KB]: 1791
% 1.27/0.54  % (4494)Time elapsed: 0.118 s
% 1.27/0.54  % (4494)------------------------------
% 1.27/0.54  % (4494)------------------------------
% 1.27/0.54  % (4472)Success in time 0.185 s
%------------------------------------------------------------------------------
