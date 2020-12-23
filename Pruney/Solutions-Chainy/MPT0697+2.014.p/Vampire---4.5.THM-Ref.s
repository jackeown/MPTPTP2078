%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:07 EST 2020

% Result     : Theorem 8.48s
% Output     : Refutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 345 expanded)
%              Number of leaves         :   14 (  75 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 ( 896 expanded)
%              Number of equality atoms :   34 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7544,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7537,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7537,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f7531,f6313])).

fof(f6313,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,k1_xboole_0),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f6312,f710])).

fof(f710,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    inference(superposition,[],[f567,f622])).

fof(f622,plain,(
    k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f103,f608])).

fof(f608,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(resolution,[],[f100,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f100,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k9_relat_1(sK1,k10_relat_1(sK1,X8)))
      | k9_relat_1(sK1,k10_relat_1(sK1,X8)) = X8 ) ),
    inference(resolution,[],[f79,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f79,plain,(
    ! [X4] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4) ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f76,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK1)
      | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4) ) ),
    inference(resolution,[],[f40,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X11] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11) ),
    inference(resolution,[],[f79,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f567,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k1_xboole_0,X0)) ),
    inference(superposition,[],[f517,f82])).

fof(f82,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(sK1)
      | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ v1_funct_1(sK1)
      | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f41,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).

fof(f41,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f517,plain,(
    ! [X11] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),X11) ),
    inference(resolution,[],[f493,f65])).

fof(f493,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k1_xboole_0),X0) ),
    inference(resolution,[],[f278,f99])).

fof(f99,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k9_relat_1(sK1,k10_relat_1(sK1,X7)))
      | r1_tarski(X6,X7) ) ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f278,plain,(
    ! [X5] : r1_tarski(k9_relat_1(sK1,k1_xboole_0),k9_relat_1(sK1,k10_relat_1(sK1,X5))) ),
    inference(superposition,[],[f179,f91])).

fof(f91,plain,(
    ! [X12] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k1_relat_1(sK1)) ),
    inference(resolution,[],[f69,f65])).

fof(f69,plain,(
    ! [X2] : r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1)) ),
    inference(resolution,[],[f39,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f179,plain,(
    ! [X6,X7] : r1_tarski(k9_relat_1(sK1,k6_subset_1(X6,X7)),k9_relat_1(sK1,X6)) ),
    inference(superposition,[],[f63,f82])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f6312,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,k9_relat_1(sK1,k1_xboole_0)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f6298,f61])).

fof(f6298,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,k9_relat_1(sK1,k1_xboole_0)),X1)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f287,f965])).

fof(f965,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f920,f67])).

fof(f920,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f740,f65])).

fof(f740,plain,(
    ! [X10] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X10,X10)) ),
    inference(resolution,[],[f171,f67])).

fof(f171,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k10_relat_1(sK1,X4),k10_relat_1(sK1,X5))
      | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X4,X5)) ) ),
    inference(superposition,[],[f78,f65])).

fof(f78,plain,(
    ! [X2,X3] : k10_relat_1(sK1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f75,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | k10_relat_1(sK1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3)) ) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).

fof(f287,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_xboole_0(X5,k9_relat_1(sK1,k10_relat_1(sK1,X3))),X4)
      | ~ r1_tarski(X5,X4)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f98,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f98,plain,(
    ! [X4,X5] :
      ( r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X5)
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f79,f44])).

fof(f7531,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,k1_xboole_0),sK0) ),
    inference(forward_demodulation,[],[f7515,f965])).

fof(f7515,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,k10_relat_1(sK1,k1_xboole_0)),sK0) ),
    inference(superposition,[],[f662,f217])).

fof(f217,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    inference(superposition,[],[f103,f82])).

fof(f662,plain,(
    ! [X17] : ~ r1_tarski(k2_xboole_0(X17,k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X17)))),sK0) ),
    inference(subsumption_resolution,[],[f656,f197])).

fof(f197,plain,(
    ! [X15,X16] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X15),X16),k1_relat_1(sK1)) ),
    inference(resolution,[],[f87,f63])).

fof(f87,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(X7,k10_relat_1(sK1,X8))
      | r1_tarski(X7,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f69,f44])).

fof(f656,plain,(
    ! [X17] :
      ( ~ r1_tarski(k2_xboole_0(X17,k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X17)))),sK0)
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X17),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f147,f70])).

fof(f70,plain,(
    ! [X3] :
      ( r1_tarski(X3,k10_relat_1(sK1,k9_relat_1(sK1,X3)))
      | ~ r1_tarski(X3,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f147,plain,(
    ! [X8,X7] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X7),X8)
      | ~ r1_tarski(k2_xboole_0(X7,X8),sK0) ) ),
    inference(resolution,[],[f95,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f60])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f95,plain,(
    ! [X1] :
      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X1)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(resolution,[],[f42,f44])).

fof(f42,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3956)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (3947)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (3946)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (3948)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (3949)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3967)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (3965)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (3957)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (3950)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (3973)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (3966)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (3972)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (3968)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (3944)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (3960)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (3951)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (3958)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (3963)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (3969)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (3955)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (3971)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3975)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (3970)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (3961)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.46/0.55  % (3961)Refutation not found, incomplete strategy% (3961)------------------------------
% 1.46/0.55  % (3961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (3961)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (3961)Memory used [KB]: 10618
% 1.46/0.55  % (3961)Time elapsed: 0.135 s
% 1.46/0.55  % (3961)------------------------------
% 1.46/0.55  % (3961)------------------------------
% 1.46/0.55  % (3953)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.55  % (3964)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.55  % (3959)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.46/0.56  % (3945)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.62/0.57  % (3962)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.62/0.58  % (3954)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.30/0.68  % (4073)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.10/0.81  % (3969)Time limit reached!
% 3.10/0.81  % (3969)------------------------------
% 3.10/0.81  % (3969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.81  % (3969)Termination reason: Time limit
% 3.10/0.81  % (3969)Termination phase: Saturation
% 3.10/0.81  
% 3.10/0.81  % (3969)Memory used [KB]: 13432
% 3.10/0.81  % (3969)Time elapsed: 0.400 s
% 3.10/0.81  % (3969)------------------------------
% 3.10/0.81  % (3969)------------------------------
% 3.10/0.82  % (3946)Time limit reached!
% 3.10/0.82  % (3946)------------------------------
% 3.10/0.82  % (3946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.84  % (3946)Termination reason: Time limit
% 3.63/0.84  % (3946)Termination phase: Saturation
% 3.63/0.84  
% 3.63/0.84  % (3946)Memory used [KB]: 7419
% 3.63/0.84  % (3946)Time elapsed: 0.400 s
% 3.63/0.84  % (3946)------------------------------
% 3.63/0.84  % (3946)------------------------------
% 3.87/0.90  % (3950)Time limit reached!
% 3.87/0.90  % (3950)------------------------------
% 3.87/0.90  % (3950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.91  % (3975)Time limit reached!
% 3.87/0.91  % (3975)------------------------------
% 3.87/0.91  % (3975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.91  % (3975)Termination reason: Time limit
% 3.87/0.91  
% 3.87/0.91  % (3975)Memory used [KB]: 2046
% 3.87/0.91  % (3975)Time elapsed: 0.508 s
% 3.87/0.91  % (3975)------------------------------
% 3.87/0.91  % (3975)------------------------------
% 3.87/0.91  % (3950)Termination reason: Time limit
% 3.87/0.91  % (3950)Termination phase: Saturation
% 3.87/0.91  
% 3.87/0.91  % (3950)Memory used [KB]: 14839
% 3.87/0.91  % (3950)Time elapsed: 0.500 s
% 3.87/0.91  % (3950)------------------------------
% 3.87/0.91  % (3950)------------------------------
% 3.87/0.92  % (3959)Time limit reached!
% 3.87/0.92  % (3959)------------------------------
% 3.87/0.92  % (3959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.87/0.92  % (3959)Termination reason: Time limit
% 3.87/0.92  % (3959)Termination phase: Saturation
% 3.87/0.92  
% 3.87/0.92  % (3959)Memory used [KB]: 4605
% 3.87/0.92  % (3959)Time elapsed: 0.500 s
% 3.87/0.92  % (3959)------------------------------
% 3.87/0.92  % (3959)------------------------------
% 4.32/0.94  % (4159)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.32/0.95  % (4164)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.52/1.01  % (4165)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.52/1.02  % (4166)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.95/1.04  % (4167)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.95/1.05  % (3951)Time limit reached!
% 4.95/1.05  % (3951)------------------------------
% 4.95/1.05  % (3951)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.95/1.05  % (3951)Termination reason: Time limit
% 4.95/1.05  
% 4.95/1.05  % (3951)Memory used [KB]: 6524
% 4.95/1.05  % (3951)Time elapsed: 0.624 s
% 4.95/1.05  % (3951)------------------------------
% 4.95/1.05  % (3951)------------------------------
% 6.16/1.17  % (4168)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.81/1.24  % (3945)Time limit reached!
% 6.81/1.24  % (3945)------------------------------
% 6.81/1.24  % (3945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.81/1.24  % (3945)Termination reason: Time limit
% 6.81/1.24  
% 6.81/1.24  % (3945)Memory used [KB]: 7675
% 6.81/1.24  % (3945)Time elapsed: 0.827 s
% 6.81/1.24  % (3945)------------------------------
% 6.81/1.24  % (3945)------------------------------
% 7.01/1.31  % (3947)Time limit reached!
% 7.01/1.31  % (3947)------------------------------
% 7.01/1.31  % (3947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.01/1.31  % (3947)Termination reason: Time limit
% 7.01/1.31  
% 7.01/1.31  % (3947)Memory used [KB]: 7803
% 7.01/1.31  % (3947)Time elapsed: 0.901 s
% 7.01/1.31  % (3947)------------------------------
% 7.01/1.31  % (3947)------------------------------
% 7.89/1.37  % (4169)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 7.89/1.41  % (3972)Time limit reached!
% 7.89/1.41  % (3972)------------------------------
% 7.89/1.41  % (3972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.41  % (3972)Termination reason: Time limit
% 7.89/1.41  % (3972)Termination phase: Saturation
% 7.89/1.41  
% 7.89/1.41  % (3972)Memory used [KB]: 9850
% 7.89/1.42  % (3972)Time elapsed: 1.0000 s
% 7.89/1.42  % (3972)------------------------------
% 7.89/1.42  % (3972)------------------------------
% 7.89/1.42  % (3957)Time limit reached!
% 7.89/1.42  % (3957)------------------------------
% 7.89/1.42  % (3957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.89/1.43  % (3957)Termination reason: Time limit
% 7.89/1.43  
% 7.89/1.43  % (3957)Memory used [KB]: 11769
% 7.89/1.43  % (3957)Time elapsed: 1.016 s
% 7.89/1.43  % (3957)------------------------------
% 7.89/1.43  % (3957)------------------------------
% 8.48/1.46  % (4170)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.48/1.47  % (4167)Refutation found. Thanks to Tanya!
% 8.48/1.47  % SZS status Theorem for theBenchmark
% 8.48/1.47  % SZS output start Proof for theBenchmark
% 8.48/1.47  fof(f7544,plain,(
% 8.48/1.47    $false),
% 8.48/1.47    inference(subsumption_resolution,[],[f7537,f67])).
% 8.48/1.47  fof(f67,plain,(
% 8.48/1.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 8.48/1.47    inference(equality_resolution,[],[f47])).
% 8.48/1.47  fof(f47,plain,(
% 8.48/1.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 8.48/1.47    inference(cnf_transformation,[],[f1])).
% 8.48/1.47  fof(f1,axiom,(
% 8.48/1.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 8.48/1.47  fof(f7537,plain,(
% 8.48/1.47    ~r1_tarski(sK0,sK0)),
% 8.48/1.47    inference(resolution,[],[f7531,f6313])).
% 8.48/1.47  fof(f6313,plain,(
% 8.48/1.47    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X0,k1_xboole_0),X1) | ~r1_tarski(X0,X1)) )),
% 8.48/1.47    inference(forward_demodulation,[],[f6312,f710])).
% 8.48/1.47  fof(f710,plain,(
% 8.48/1.47    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 8.48/1.47    inference(superposition,[],[f567,f622])).
% 8.48/1.47  fof(f622,plain,(
% 8.48/1.47    k1_xboole_0 = k6_subset_1(k1_xboole_0,k1_xboole_0)),
% 8.48/1.47    inference(superposition,[],[f103,f608])).
% 8.48/1.47  fof(f608,plain,(
% 8.48/1.47    k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0))),
% 8.48/1.47    inference(resolution,[],[f100,f61])).
% 8.48/1.47  fof(f61,plain,(
% 8.48/1.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 8.48/1.47    inference(cnf_transformation,[],[f6])).
% 8.48/1.47  fof(f6,axiom,(
% 8.48/1.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 8.48/1.47  fof(f100,plain,(
% 8.48/1.47    ( ! [X8] : (~r1_tarski(X8,k9_relat_1(sK1,k10_relat_1(sK1,X8))) | k9_relat_1(sK1,k10_relat_1(sK1,X8)) = X8) )),
% 8.48/1.47    inference(resolution,[],[f79,f49])).
% 8.48/1.47  fof(f49,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 8.48/1.47    inference(cnf_transformation,[],[f1])).
% 8.48/1.47  fof(f79,plain,(
% 8.48/1.47    ( ! [X4] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4)) )),
% 8.48/1.47    inference(subsumption_resolution,[],[f76,f39])).
% 8.48/1.47  fof(f39,plain,(
% 8.48/1.47    v1_relat_1(sK1)),
% 8.48/1.47    inference(cnf_transformation,[],[f21])).
% 8.48/1.47  fof(f21,plain,(
% 8.48/1.47    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 8.48/1.47    inference(flattening,[],[f20])).
% 8.48/1.47  fof(f20,plain,(
% 8.48/1.47    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 8.48/1.47    inference(ennf_transformation,[],[f19])).
% 8.48/1.47  fof(f19,negated_conjecture,(
% 8.48/1.47    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 8.48/1.47    inference(negated_conjecture,[],[f18])).
% 8.48/1.47  fof(f18,conjecture,(
% 8.48/1.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 8.48/1.47  fof(f76,plain,(
% 8.48/1.47    ( ! [X4] : (~v1_relat_1(sK1) | r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X4)) )),
% 8.48/1.47    inference(resolution,[],[f40,f50])).
% 8.48/1.47  fof(f50,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 8.48/1.47    inference(cnf_transformation,[],[f29])).
% 8.48/1.47  fof(f29,plain,(
% 8.48/1.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 8.48/1.47    inference(flattening,[],[f28])).
% 8.48/1.47  fof(f28,plain,(
% 8.48/1.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 8.48/1.47    inference(ennf_transformation,[],[f16])).
% 8.48/1.47  fof(f16,axiom,(
% 8.48/1.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).
% 8.48/1.47  fof(f40,plain,(
% 8.48/1.47    v1_funct_1(sK1)),
% 8.48/1.47    inference(cnf_transformation,[],[f21])).
% 8.48/1.47  fof(f103,plain,(
% 8.48/1.47    ( ! [X11] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X11)),X11)) )),
% 8.48/1.47    inference(resolution,[],[f79,f65])).
% 8.48/1.47  fof(f65,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 8.48/1.47    inference(definition_unfolding,[],[f58,f60])).
% 8.48/1.47  fof(f60,plain,(
% 8.48/1.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 8.48/1.47    inference(cnf_transformation,[],[f10])).
% 8.48/1.47  fof(f10,axiom,(
% 8.48/1.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 8.48/1.47  fof(f58,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 8.48/1.47    inference(cnf_transformation,[],[f2])).
% 8.48/1.47  fof(f2,axiom,(
% 8.48/1.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 8.48/1.47  fof(f567,plain,(
% 8.48/1.47    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k1_xboole_0,X0))) )),
% 8.48/1.47    inference(superposition,[],[f517,f82])).
% 8.48/1.47  fof(f82,plain,(
% 8.48/1.47    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 8.48/1.47    inference(subsumption_resolution,[],[f81,f40])).
% 8.48/1.47  fof(f81,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v1_funct_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 8.48/1.47    inference(subsumption_resolution,[],[f80,f39])).
% 8.48/1.47  fof(f80,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~v1_funct_1(sK1) | k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 8.48/1.47    inference(resolution,[],[f41,f57])).
% 8.48/1.47  fof(f57,plain,(
% 8.48/1.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 8.48/1.47    inference(cnf_transformation,[],[f38])).
% 8.48/1.47  fof(f38,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 8.48/1.47    inference(flattening,[],[f37])).
% 8.48/1.47  fof(f37,plain,(
% 8.48/1.47    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 8.48/1.47    inference(ennf_transformation,[],[f14])).
% 8.48/1.47  fof(f14,axiom,(
% 8.48/1.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_funct_1)).
% 8.48/1.47  fof(f41,plain,(
% 8.48/1.47    v2_funct_1(sK1)),
% 8.48/1.47    inference(cnf_transformation,[],[f21])).
% 8.48/1.47  fof(f517,plain,(
% 8.48/1.47    ( ! [X11] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k1_xboole_0),X11)) )),
% 8.48/1.47    inference(resolution,[],[f493,f65])).
% 8.48/1.47  fof(f493,plain,(
% 8.48/1.47    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k1_xboole_0),X0)) )),
% 8.48/1.47    inference(resolution,[],[f278,f99])).
% 8.48/1.47  fof(f99,plain,(
% 8.48/1.47    ( ! [X6,X7] : (~r1_tarski(X6,k9_relat_1(sK1,k10_relat_1(sK1,X7))) | r1_tarski(X6,X7)) )),
% 8.48/1.47    inference(resolution,[],[f79,f44])).
% 8.48/1.47  fof(f44,plain,(
% 8.48/1.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 8.48/1.47    inference(cnf_transformation,[],[f25])).
% 8.48/1.47  fof(f25,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 8.48/1.47    inference(flattening,[],[f24])).
% 8.48/1.47  fof(f24,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 8.48/1.47    inference(ennf_transformation,[],[f5])).
% 8.48/1.47  fof(f5,axiom,(
% 8.48/1.47    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 8.48/1.47  fof(f278,plain,(
% 8.48/1.47    ( ! [X5] : (r1_tarski(k9_relat_1(sK1,k1_xboole_0),k9_relat_1(sK1,k10_relat_1(sK1,X5)))) )),
% 8.48/1.47    inference(superposition,[],[f179,f91])).
% 8.48/1.47  fof(f91,plain,(
% 8.48/1.47    ( ! [X12] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X12),k1_relat_1(sK1))) )),
% 8.48/1.47    inference(resolution,[],[f69,f65])).
% 8.48/1.47  fof(f69,plain,(
% 8.48/1.47    ( ! [X2] : (r1_tarski(k10_relat_1(sK1,X2),k1_relat_1(sK1))) )),
% 8.48/1.47    inference(resolution,[],[f39,f56])).
% 8.48/1.47  fof(f56,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 8.48/1.47    inference(cnf_transformation,[],[f36])).
% 8.48/1.47  fof(f36,plain,(
% 8.48/1.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.48/1.47    inference(ennf_transformation,[],[f11])).
% 8.48/1.47  fof(f11,axiom,(
% 8.48/1.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 8.48/1.47  fof(f179,plain,(
% 8.48/1.47    ( ! [X6,X7] : (r1_tarski(k9_relat_1(sK1,k6_subset_1(X6,X7)),k9_relat_1(sK1,X6))) )),
% 8.48/1.47    inference(superposition,[],[f63,f82])).
% 8.48/1.47  fof(f63,plain,(
% 8.48/1.47    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 8.48/1.47    inference(definition_unfolding,[],[f52,f60])).
% 8.48/1.47  fof(f52,plain,(
% 8.48/1.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 8.48/1.47    inference(cnf_transformation,[],[f7])).
% 8.48/1.47  fof(f7,axiom,(
% 8.48/1.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 8.48/1.47  fof(f6312,plain,(
% 8.48/1.47    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X0,k9_relat_1(sK1,k1_xboole_0)),X1) | ~r1_tarski(X0,X1)) )),
% 8.48/1.47    inference(subsumption_resolution,[],[f6298,f61])).
% 8.48/1.47  fof(f6298,plain,(
% 8.48/1.47    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(X0,k9_relat_1(sK1,k1_xboole_0)),X1) | ~r1_tarski(X0,X1) | ~r1_tarski(k1_xboole_0,X1)) )),
% 8.48/1.47    inference(superposition,[],[f287,f965])).
% 8.48/1.47  fof(f965,plain,(
% 8.48/1.47    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 8.48/1.47    inference(subsumption_resolution,[],[f920,f67])).
% 8.48/1.47  fof(f920,plain,(
% 8.48/1.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) | ~r1_tarski(X0,X0)) )),
% 8.48/1.47    inference(superposition,[],[f740,f65])).
% 8.48/1.47  fof(f740,plain,(
% 8.48/1.47    ( ! [X10] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X10,X10))) )),
% 8.48/1.47    inference(resolution,[],[f171,f67])).
% 8.48/1.47  fof(f171,plain,(
% 8.48/1.47    ( ! [X4,X5] : (~r1_tarski(k10_relat_1(sK1,X4),k10_relat_1(sK1,X5)) | k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X4,X5))) )),
% 8.48/1.47    inference(superposition,[],[f78,f65])).
% 8.48/1.47  fof(f78,plain,(
% 8.48/1.47    ( ! [X2,X3] : (k10_relat_1(sK1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3))) )),
% 8.48/1.47    inference(subsumption_resolution,[],[f75,f39])).
% 8.48/1.47  fof(f75,plain,(
% 8.48/1.47    ( ! [X2,X3] : (~v1_relat_1(sK1) | k10_relat_1(sK1,k6_subset_1(X2,X3)) = k6_subset_1(k10_relat_1(sK1,X2),k10_relat_1(sK1,X3))) )),
% 8.48/1.47    inference(resolution,[],[f40,f53])).
% 8.48/1.47  fof(f53,plain,(
% 8.48/1.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 8.48/1.47    inference(cnf_transformation,[],[f32])).
% 8.48/1.47  fof(f32,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 8.48/1.47    inference(flattening,[],[f31])).
% 8.48/1.47  fof(f31,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 8.48/1.47    inference(ennf_transformation,[],[f15])).
% 8.48/1.47  fof(f15,axiom,(
% 8.48/1.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_funct_1)).
% 8.48/1.47  fof(f287,plain,(
% 8.48/1.47    ( ! [X4,X5,X3] : (r1_tarski(k2_xboole_0(X5,k9_relat_1(sK1,k10_relat_1(sK1,X3))),X4) | ~r1_tarski(X5,X4) | ~r1_tarski(X3,X4)) )),
% 8.48/1.47    inference(resolution,[],[f98,f43])).
% 8.48/1.47  fof(f43,plain,(
% 8.48/1.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 8.48/1.47    inference(cnf_transformation,[],[f23])).
% 8.48/1.47  fof(f23,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 8.48/1.47    inference(flattening,[],[f22])).
% 8.48/1.47  fof(f22,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 8.48/1.47    inference(ennf_transformation,[],[f9])).
% 8.48/1.47  fof(f9,axiom,(
% 8.48/1.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 8.48/1.47  fof(f98,plain,(
% 8.48/1.47    ( ! [X4,X5] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X4)),X5) | ~r1_tarski(X4,X5)) )),
% 8.48/1.47    inference(resolution,[],[f79,f44])).
% 8.48/1.47  fof(f7531,plain,(
% 8.48/1.47    ~r1_tarski(k2_xboole_0(sK0,k1_xboole_0),sK0)),
% 8.48/1.47    inference(forward_demodulation,[],[f7515,f965])).
% 8.48/1.47  fof(f7515,plain,(
% 8.48/1.47    ~r1_tarski(k2_xboole_0(sK0,k10_relat_1(sK1,k1_xboole_0)),sK0)),
% 8.48/1.47    inference(superposition,[],[f662,f217])).
% 8.48/1.47  fof(f217,plain,(
% 8.48/1.47    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) )),
% 8.48/1.47    inference(superposition,[],[f103,f82])).
% 8.48/1.47  fof(f662,plain,(
% 8.48/1.47    ( ! [X17] : (~r1_tarski(k2_xboole_0(X17,k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X17)))),sK0)) )),
% 8.48/1.47    inference(subsumption_resolution,[],[f656,f197])).
% 8.48/1.47  fof(f197,plain,(
% 8.48/1.47    ( ! [X15,X16] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X15),X16),k1_relat_1(sK1))) )),
% 8.48/1.47    inference(resolution,[],[f87,f63])).
% 8.48/1.47  fof(f87,plain,(
% 8.48/1.47    ( ! [X8,X7] : (~r1_tarski(X7,k10_relat_1(sK1,X8)) | r1_tarski(X7,k1_relat_1(sK1))) )),
% 8.48/1.47    inference(resolution,[],[f69,f44])).
% 8.48/1.47  fof(f656,plain,(
% 8.48/1.47    ( ! [X17] : (~r1_tarski(k2_xboole_0(X17,k10_relat_1(sK1,k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X17)))),sK0) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X17),k1_relat_1(sK1))) )),
% 8.48/1.47    inference(resolution,[],[f147,f70])).
% 8.48/1.47  fof(f70,plain,(
% 8.48/1.47    ( ! [X3] : (r1_tarski(X3,k10_relat_1(sK1,k9_relat_1(sK1,X3))) | ~r1_tarski(X3,k1_relat_1(sK1))) )),
% 8.48/1.47    inference(resolution,[],[f39,f55])).
% 8.48/1.47  fof(f55,plain,(
% 8.48/1.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 8.48/1.47    inference(cnf_transformation,[],[f35])).
% 8.48/1.47  fof(f35,plain,(
% 8.48/1.47    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.48/1.47    inference(flattening,[],[f34])).
% 8.48/1.47  fof(f34,plain,(
% 8.48/1.47    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 8.48/1.47    inference(ennf_transformation,[],[f17])).
% 8.48/1.47  fof(f17,axiom,(
% 8.48/1.47    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).
% 8.48/1.47  fof(f147,plain,(
% 8.48/1.47    ( ! [X8,X7] : (~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X7),X8) | ~r1_tarski(k2_xboole_0(X7,X8),sK0)) )),
% 8.48/1.47    inference(resolution,[],[f95,f62])).
% 8.48/1.47  fof(f62,plain,(
% 8.48/1.47    ( ! [X2,X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 8.48/1.47    inference(definition_unfolding,[],[f46,f60])).
% 8.48/1.47  fof(f46,plain,(
% 8.48/1.47    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 8.48/1.47    inference(cnf_transformation,[],[f27])).
% 8.48/1.47  fof(f27,plain,(
% 8.48/1.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 8.48/1.47    inference(ennf_transformation,[],[f8])).
% 8.48/1.47  fof(f8,axiom,(
% 8.48/1.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 8.48/1.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 8.48/1.47  fof(f95,plain,(
% 8.48/1.47    ( ! [X1] : (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),X1) | ~r1_tarski(X1,sK0)) )),
% 8.48/1.47    inference(resolution,[],[f42,f44])).
% 8.48/1.47  fof(f42,plain,(
% 8.48/1.47    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 8.48/1.47    inference(cnf_transformation,[],[f21])).
% 8.48/1.47  % SZS output end Proof for theBenchmark
% 8.48/1.47  % (4167)------------------------------
% 8.48/1.47  % (4167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.48/1.47  % (4167)Termination reason: Refutation
% 8.48/1.47  
% 8.48/1.47  % (4167)Memory used [KB]: 4477
% 8.48/1.47  % (4167)Time elapsed: 0.491 s
% 8.48/1.47  % (4167)------------------------------
% 8.48/1.47  % (4167)------------------------------
% 8.48/1.47  % (3942)Success in time 1.11 s
%------------------------------------------------------------------------------
