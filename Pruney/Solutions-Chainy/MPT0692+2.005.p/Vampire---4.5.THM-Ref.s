%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:56 EST 2020

% Result     : Theorem 5.00s
% Output     : Refutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 440 expanded)
%              Number of leaves         :   14 ( 113 expanded)
%              Depth                    :   22
%              Number of atoms          :  157 (1004 expanded)
%              Number of equality atoms :   53 ( 326 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7159,plain,(
    $false ),
    inference(resolution,[],[f7101,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7101,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f127,f7046])).

fof(f7046,plain,(
    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f5784,f1371])).

fof(f1371,plain,(
    ! [X0] : k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(backward_demodulation,[],[f371,f1357])).

fof(f1357,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(unit_resulting_resolution,[],[f55,f1321,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1321,plain,(
    ! [X0] : r1_tarski(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f926,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f926,plain,(
    ! [X3] : k1_xboole_0 = k6_subset_1(X3,k6_subset_1(X3,k1_xboole_0)) ),
    inference(superposition,[],[f842,f60])).

fof(f60,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f53,f54,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f48,f52,f52])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f842,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f55,f822,f38])).

fof(f822,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,X6)) ),
    inference(forward_demodulation,[],[f792,f625])).

fof(f625,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f384,f624])).

fof(f624,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f617,f87])).

fof(f87,plain,(
    k1_xboole_0 = k6_subset_1(k1_xboole_0,sK0) ),
    inference(unit_resulting_resolution,[],[f84,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f84,plain,(
    r1_tarski(k1_xboole_0,sK0) ),
    inference(superposition,[],[f55,f74])).

fof(f74,plain,(
    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f59])).

fof(f34,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f617,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(k1_xboole_0,sK0)) ),
    inference(superposition,[],[f495,f70])).

fof(f70,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f32,f33,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f33,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f495,plain,(
    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f493,f59])).

fof(f493,plain,(
    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f358,f74])).

fof(f358,plain,(
    ! [X8,X9] : r1_tarski(k10_relat_1(sK1,k6_subset_1(X8,X9)),k10_relat_1(sK1,X8)) ),
    inference(superposition,[],[f55,f70])).

fof(f384,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f71,f375,f38])).

fof(f375,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,k9_relat_1(sK1,k10_relat_1(sK1,X4))) ),
    inference(superposition,[],[f55,f123])).

fof(f123,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f71,f59])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f32,f33,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f792,plain,(
    ! [X6] : r1_tarski(k9_relat_1(sK1,k1_xboole_0),k6_subset_1(k1_xboole_0,X6)) ),
    inference(superposition,[],[f71,f682])).

fof(f682,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f664,f200])).

fof(f200,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f189,f59])).

fof(f189,plain,(
    ! [X4] : r1_tarski(k1_xboole_0,k10_relat_1(sK1,X4)) ),
    inference(superposition,[],[f55,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f63,f59])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f664,plain,(
    ! [X0] : k10_relat_1(sK1,k6_subset_1(k1_xboole_0,X0)) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X0)) ),
    inference(superposition,[],[f70,f624])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f371,plain,(
    ! [X0] : k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),k1_xboole_0) ),
    inference(superposition,[],[f60,f123])).

fof(f5784,plain,(
    ! [X0] : sK0 = k6_subset_1(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f5496,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) = X0 ) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f5496,plain,(
    ! [X0] : r1_xboole_0(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f34,f3305,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f3305,plain,(
    ! [X0] : r1_xboole_0(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f32,f3194,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f3194,plain,(
    ! [X1] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X1,k9_relat_1(sK1,k10_relat_1(sK1,X1)))) ),
    inference(superposition,[],[f536,f70])).

fof(f536,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f77,f59])).

fof(f77,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) ),
    inference(unit_resulting_resolution,[],[f32,f63,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

fof(f127,plain,(
    ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f35,f71,f38])).

fof(f35,plain,(
    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.57  % (3815)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.57  % (3824)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.58/0.58  % (3814)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.58/0.59  % (3823)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.58/0.60  % (3819)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.58/0.60  % (3821)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.60  % (3817)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.58/0.60  % (3818)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.87/0.61  % (3843)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.87/0.61  % (3838)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.87/0.61  % (3831)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.87/0.61  % (3831)Refutation not found, incomplete strategy% (3831)------------------------------
% 1.87/0.61  % (3831)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (3830)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.87/0.61  % (3831)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (3831)Memory used [KB]: 10618
% 1.87/0.61  % (3831)Time elapsed: 0.164 s
% 1.87/0.61  % (3816)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.87/0.61  % (3831)------------------------------
% 1.87/0.61  % (3831)------------------------------
% 1.87/0.62  % (3822)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.87/0.62  % (3837)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.87/0.63  % (3844)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.87/0.63  % (3841)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.87/0.63  % (3835)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.87/0.63  % (3844)Refutation not found, incomplete strategy% (3844)------------------------------
% 1.87/0.63  % (3844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (3844)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (3844)Memory used [KB]: 1663
% 1.87/0.63  % (3844)Time elapsed: 0.197 s
% 1.87/0.63  % (3844)------------------------------
% 1.87/0.63  % (3844)------------------------------
% 1.87/0.63  % (3842)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.87/0.63  % (3834)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.87/0.63  % (3832)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.87/0.63  % (3836)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.87/0.64  % (3828)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.87/0.64  % (3833)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.87/0.64  % (3827)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.87/0.65  % (3829)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.87/0.65  % (3825)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.87/0.65  % (3826)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.87/0.65  % (3840)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.19/0.66  % (3839)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 3.66/0.86  % (3816)Time limit reached!
% 3.66/0.86  % (3816)------------------------------
% 3.66/0.86  % (3816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.86  % (3816)Termination reason: Time limit
% 3.66/0.86  
% 3.66/0.86  % (3816)Memory used [KB]: 6140
% 3.66/0.86  % (3816)Time elapsed: 0.428 s
% 3.66/0.86  % (3816)------------------------------
% 3.66/0.86  % (3816)------------------------------
% 3.66/0.87  % (3817)Refutation not found, incomplete strategy% (3817)------------------------------
% 3.66/0.87  % (3817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.87  % (3817)Termination reason: Refutation not found, incomplete strategy
% 3.66/0.87  
% 3.66/0.87  % (3817)Memory used [KB]: 6140
% 3.66/0.87  % (3817)Time elapsed: 0.412 s
% 3.66/0.87  % (3817)------------------------------
% 3.66/0.87  % (3817)------------------------------
% 3.66/0.88  % (3882)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.66/0.88  % (3839)Time limit reached!
% 3.66/0.88  % (3839)------------------------------
% 3.66/0.88  % (3839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.88  % (3839)Termination reason: Time limit
% 3.66/0.88  
% 3.66/0.88  % (3839)Memory used [KB]: 12153
% 3.66/0.88  % (3839)Time elapsed: 0.404 s
% 3.66/0.88  % (3839)------------------------------
% 3.66/0.88  % (3839)------------------------------
% 4.05/0.92  % (3881)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 4.05/0.95  % (3821)Time limit reached!
% 4.05/0.95  % (3821)------------------------------
% 4.05/0.95  % (3821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.95  % (3821)Termination reason: Time limit
% 4.05/0.95  
% 4.05/0.95  % (3821)Memory used [KB]: 12665
% 4.05/0.95  % (3821)Time elapsed: 0.508 s
% 4.05/0.95  % (3821)------------------------------
% 4.05/0.95  % (3821)------------------------------
% 4.05/0.95  % (3829)Time limit reached!
% 4.05/0.95  % (3829)------------------------------
% 4.05/0.95  % (3829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.95  % (3829)Termination reason: Time limit
% 4.05/0.95  % (3829)Termination phase: Saturation
% 4.05/0.95  
% 4.05/0.95  % (3829)Memory used [KB]: 3454
% 4.05/0.95  % (3829)Time elapsed: 0.516 s
% 4.05/0.95  % (3829)------------------------------
% 4.05/0.95  % (3829)------------------------------
% 5.00/1.07  % (3840)Refutation found. Thanks to Tanya!
% 5.00/1.07  % SZS status Theorem for theBenchmark
% 5.00/1.07  % SZS output start Proof for theBenchmark
% 5.00/1.07  fof(f7159,plain,(
% 5.00/1.07    $false),
% 5.00/1.07    inference(resolution,[],[f7101,f61])).
% 5.00/1.07  fof(f61,plain,(
% 5.00/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 5.00/1.07    inference(equality_resolution,[],[f37])).
% 5.00/1.07  fof(f37,plain,(
% 5.00/1.07    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 5.00/1.07    inference(cnf_transformation,[],[f2])).
% 5.00/1.07  fof(f2,axiom,(
% 5.00/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 5.00/1.07  fof(f7101,plain,(
% 5.00/1.07    ~r1_tarski(sK0,sK0)),
% 5.00/1.07    inference(backward_demodulation,[],[f127,f7046])).
% 5.00/1.07  fof(f7046,plain,(
% 5.00/1.07    sK0 = k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 5.00/1.07    inference(superposition,[],[f5784,f1371])).
% 5.00/1.07  fof(f1371,plain,(
% 5.00/1.07    ( ! [X0] : (k9_relat_1(sK1,k10_relat_1(sK1,X0)) = k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 5.00/1.07    inference(backward_demodulation,[],[f371,f1357])).
% 5.00/1.07  fof(f1357,plain,(
% 5.00/1.07    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f55,f1321,f38])).
% 5.00/1.07  fof(f38,plain,(
% 5.00/1.07    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 5.00/1.07    inference(cnf_transformation,[],[f2])).
% 5.00/1.07  fof(f1321,plain,(
% 5.00/1.07    ( ! [X0] : (r1_tarski(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f926,f58])).
% 5.00/1.07  fof(f58,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 5.00/1.07    inference(definition_unfolding,[],[f51,f52])).
% 5.00/1.07  fof(f52,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 5.00/1.07    inference(cnf_transformation,[],[f11])).
% 5.00/1.07  fof(f11,axiom,(
% 5.00/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 5.00/1.07  fof(f51,plain,(
% 5.00/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 5.00/1.07    inference(cnf_transformation,[],[f3])).
% 5.00/1.07  fof(f3,axiom,(
% 5.00/1.07    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.00/1.07  fof(f926,plain,(
% 5.00/1.07    ( ! [X3] : (k1_xboole_0 = k6_subset_1(X3,k6_subset_1(X3,k1_xboole_0))) )),
% 5.00/1.07    inference(superposition,[],[f842,f60])).
% 5.00/1.07  fof(f60,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 5.00/1.07    inference(definition_unfolding,[],[f53,f54,f54])).
% 5.00/1.07  fof(f54,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 5.00/1.07    inference(definition_unfolding,[],[f48,f52,f52])).
% 5.00/1.07  fof(f48,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 5.00/1.07    inference(cnf_transformation,[],[f5])).
% 5.00/1.07  fof(f5,axiom,(
% 5.00/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 5.00/1.07  fof(f53,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.00/1.07    inference(cnf_transformation,[],[f1])).
% 5.00/1.07  fof(f1,axiom,(
% 5.00/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.00/1.07  fof(f842,plain,(
% 5.00/1.07    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f55,f822,f38])).
% 5.00/1.07  fof(f822,plain,(
% 5.00/1.07    ( ! [X6] : (r1_tarski(k1_xboole_0,k6_subset_1(k1_xboole_0,X6))) )),
% 5.00/1.07    inference(forward_demodulation,[],[f792,f625])).
% 5.00/1.07  fof(f625,plain,(
% 5.00/1.07    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 5.00/1.07    inference(backward_demodulation,[],[f384,f624])).
% 5.00/1.07  fof(f624,plain,(
% 5.00/1.07    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 5.00/1.07    inference(forward_demodulation,[],[f617,f87])).
% 5.00/1.07  fof(f87,plain,(
% 5.00/1.07    k1_xboole_0 = k6_subset_1(k1_xboole_0,sK0)),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f84,f59])).
% 5.00/1.07  fof(f59,plain,(
% 5.00/1.07    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 5.00/1.07    inference(definition_unfolding,[],[f50,f52])).
% 5.00/1.07  fof(f50,plain,(
% 5.00/1.07    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 5.00/1.07    inference(cnf_transformation,[],[f3])).
% 5.00/1.07  fof(f84,plain,(
% 5.00/1.07    r1_tarski(k1_xboole_0,sK0)),
% 5.00/1.07    inference(superposition,[],[f55,f74])).
% 5.00/1.07  fof(f74,plain,(
% 5.00/1.07    k1_xboole_0 = k6_subset_1(sK0,k2_relat_1(sK1))),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f34,f59])).
% 5.00/1.07  fof(f34,plain,(
% 5.00/1.07    r1_tarski(sK0,k2_relat_1(sK1))),
% 5.00/1.07    inference(cnf_transformation,[],[f21])).
% 5.00/1.07  fof(f21,plain,(
% 5.00/1.07    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 5.00/1.07    inference(flattening,[],[f20])).
% 5.00/1.07  fof(f20,plain,(
% 5.00/1.07    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 5.00/1.07    inference(ennf_transformation,[],[f19])).
% 5.00/1.07  fof(f19,negated_conjecture,(
% 5.00/1.07    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 5.00/1.07    inference(negated_conjecture,[],[f18])).
% 5.00/1.07  fof(f18,conjecture,(
% 5.00/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 5.00/1.07  fof(f617,plain,(
% 5.00/1.07    k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(k1_xboole_0,sK0))),
% 5.00/1.07    inference(superposition,[],[f495,f70])).
% 5.00/1.07  fof(f70,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f32,f33,f44])).
% 5.00/1.07  fof(f44,plain,(
% 5.00/1.07    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) )),
% 5.00/1.07    inference(cnf_transformation,[],[f28])).
% 5.00/1.07  fof(f28,plain,(
% 5.00/1.07    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 5.00/1.07    inference(flattening,[],[f27])).
% 5.00/1.07  fof(f27,plain,(
% 5.00/1.07    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 5.00/1.07    inference(ennf_transformation,[],[f15])).
% 5.00/1.07  fof(f15,axiom,(
% 5.00/1.07    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 5.00/1.07  fof(f33,plain,(
% 5.00/1.07    v1_funct_1(sK1)),
% 5.00/1.07    inference(cnf_transformation,[],[f21])).
% 5.00/1.07  fof(f32,plain,(
% 5.00/1.07    v1_relat_1(sK1)),
% 5.00/1.07    inference(cnf_transformation,[],[f21])).
% 5.00/1.07  fof(f495,plain,(
% 5.00/1.07    k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0))),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f493,f59])).
% 5.00/1.07  fof(f493,plain,(
% 5.00/1.07    r1_tarski(k10_relat_1(sK1,k1_xboole_0),k10_relat_1(sK1,sK0))),
% 5.00/1.07    inference(superposition,[],[f358,f74])).
% 5.00/1.07  fof(f358,plain,(
% 5.00/1.07    ( ! [X8,X9] : (r1_tarski(k10_relat_1(sK1,k6_subset_1(X8,X9)),k10_relat_1(sK1,X8))) )),
% 5.00/1.07    inference(superposition,[],[f55,f70])).
% 5.00/1.07  fof(f384,plain,(
% 5.00/1.07    k1_xboole_0 = k9_relat_1(sK1,k10_relat_1(sK1,k1_xboole_0))),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f71,f375,f38])).
% 5.00/1.07  fof(f375,plain,(
% 5.00/1.07    ( ! [X4] : (r1_tarski(k1_xboole_0,k9_relat_1(sK1,k10_relat_1(sK1,X4)))) )),
% 5.00/1.07    inference(superposition,[],[f55,f123])).
% 5.00/1.07  fof(f123,plain,(
% 5.00/1.07    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f71,f59])).
% 5.00/1.07  fof(f71,plain,(
% 5.00/1.07    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f32,f33,f39])).
% 5.00/1.07  fof(f39,plain,(
% 5.00/1.07    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)) )),
% 5.00/1.07    inference(cnf_transformation,[],[f23])).
% 5.00/1.07  fof(f23,plain,(
% 5.00/1.07    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 5.00/1.07    inference(flattening,[],[f22])).
% 5.00/1.07  fof(f22,plain,(
% 5.00/1.07    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 5.00/1.07    inference(ennf_transformation,[],[f16])).
% 5.00/1.07  fof(f16,axiom,(
% 5.00/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 5.00/1.07  fof(f792,plain,(
% 5.00/1.07    ( ! [X6] : (r1_tarski(k9_relat_1(sK1,k1_xboole_0),k6_subset_1(k1_xboole_0,X6))) )),
% 5.00/1.07    inference(superposition,[],[f71,f682])).
% 5.00/1.07  fof(f682,plain,(
% 5.00/1.07    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(k1_xboole_0,X0))) )),
% 5.00/1.07    inference(forward_demodulation,[],[f664,f200])).
% 5.00/1.07  fof(f200,plain,(
% 5.00/1.07    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X0))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f189,f59])).
% 5.00/1.07  fof(f189,plain,(
% 5.00/1.07    ( ! [X4] : (r1_tarski(k1_xboole_0,k10_relat_1(sK1,X4))) )),
% 5.00/1.07    inference(superposition,[],[f55,f78])).
% 5.00/1.07  fof(f78,plain,(
% 5.00/1.07    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f63,f59])).
% 5.00/1.07  fof(f63,plain,(
% 5.00/1.07    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f32,f45])).
% 5.00/1.07  fof(f45,plain,(
% 5.00/1.07    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))) )),
% 5.00/1.07    inference(cnf_transformation,[],[f29])).
% 5.00/1.07  fof(f29,plain,(
% 5.00/1.07    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.00/1.07    inference(ennf_transformation,[],[f13])).
% 5.00/1.07  fof(f13,axiom,(
% 5.00/1.07    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 5.00/1.07  fof(f664,plain,(
% 5.00/1.07    ( ! [X0] : (k10_relat_1(sK1,k6_subset_1(k1_xboole_0,X0)) = k6_subset_1(k1_xboole_0,k10_relat_1(sK1,X0))) )),
% 5.00/1.07    inference(superposition,[],[f70,f624])).
% 5.00/1.07  fof(f55,plain,(
% 5.00/1.07    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 5.00/1.07    inference(definition_unfolding,[],[f41,f52])).
% 5.00/1.07  fof(f41,plain,(
% 5.00/1.07    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 5.00/1.07    inference(cnf_transformation,[],[f4])).
% 5.00/1.07  fof(f4,axiom,(
% 5.00/1.07    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 5.00/1.07  fof(f371,plain,(
% 5.00/1.07    ( ! [X0] : (k6_subset_1(X0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0)))) = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),k1_xboole_0)) )),
% 5.00/1.07    inference(superposition,[],[f60,f123])).
% 5.00/1.07  fof(f5784,plain,(
% 5.00/1.07    ( ! [X0] : (sK0 = k6_subset_1(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f5496,f56])).
% 5.00/1.07  fof(f56,plain,(
% 5.00/1.07    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0) )),
% 5.00/1.07    inference(definition_unfolding,[],[f47,f52])).
% 5.00/1.07  fof(f47,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 5.00/1.07    inference(cnf_transformation,[],[f7])).
% 5.00/1.07  fof(f7,axiom,(
% 5.00/1.07    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 5.00/1.07  fof(f5496,plain,(
% 5.00/1.07    ( ! [X0] : (r1_xboole_0(sK0,k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f34,f3305,f49])).
% 5.00/1.07  fof(f49,plain,(
% 5.00/1.07    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 5.00/1.07    inference(cnf_transformation,[],[f31])).
% 5.00/1.07  fof(f31,plain,(
% 5.00/1.07    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 5.00/1.07    inference(flattening,[],[f30])).
% 5.00/1.07  fof(f30,plain,(
% 5.00/1.07    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 5.00/1.07    inference(ennf_transformation,[],[f6])).
% 5.00/1.07  fof(f6,axiom,(
% 5.00/1.07    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 5.00/1.07  fof(f3305,plain,(
% 5.00/1.07    ( ! [X0] : (r1_xboole_0(k2_relat_1(sK1),k6_subset_1(X0,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f32,f3194,f43])).
% 5.00/1.07  fof(f43,plain,(
% 5.00/1.07    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 5.00/1.07    inference(cnf_transformation,[],[f26])).
% 5.00/1.07  fof(f26,plain,(
% 5.00/1.07    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 5.00/1.07    inference(ennf_transformation,[],[f14])).
% 5.00/1.07  fof(f14,axiom,(
% 5.00/1.07    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 5.00/1.07  fof(f3194,plain,(
% 5.00/1.07    ( ! [X1] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X1,k9_relat_1(sK1,k10_relat_1(sK1,X1))))) )),
% 5.00/1.07    inference(superposition,[],[f536,f70])).
% 5.00/1.07  fof(f536,plain,(
% 5.00/1.07    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f77,f59])).
% 5.00/1.07  fof(f77,plain,(
% 5.00/1.07    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,X0))))) )),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f32,f63,f40])).
% 5.00/1.07  fof(f40,plain,(
% 5.00/1.07    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))) )),
% 5.00/1.07    inference(cnf_transformation,[],[f25])).
% 5.00/1.07  fof(f25,plain,(
% 5.00/1.07    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 5.00/1.07    inference(flattening,[],[f24])).
% 5.00/1.07  fof(f24,plain,(
% 5.00/1.07    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 5.00/1.07    inference(ennf_transformation,[],[f17])).
% 5.00/1.07  fof(f17,axiom,(
% 5.00/1.07    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 5.00/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 5.00/1.07  fof(f127,plain,(
% 5.00/1.07    ~r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))),
% 5.00/1.07    inference(unit_resulting_resolution,[],[f35,f71,f38])).
% 5.00/1.07  fof(f35,plain,(
% 5.00/1.07    sK0 != k9_relat_1(sK1,k10_relat_1(sK1,sK0))),
% 5.00/1.07    inference(cnf_transformation,[],[f21])).
% 5.00/1.07  % SZS output end Proof for theBenchmark
% 5.00/1.07  % (3840)------------------------------
% 5.00/1.07  % (3840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.00/1.07  % (3840)Termination reason: Refutation
% 5.00/1.07  
% 5.00/1.07  % (3840)Memory used [KB]: 8315
% 5.00/1.07  % (3840)Time elapsed: 0.612 s
% 5.00/1.07  % (3840)------------------------------
% 5.00/1.07  % (3840)------------------------------
% 5.00/1.07  % (3813)Success in time 0.698 s
%------------------------------------------------------------------------------
