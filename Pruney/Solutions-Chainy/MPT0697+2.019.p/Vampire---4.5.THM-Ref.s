%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:08 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 190 expanded)
%              Number of leaves         :   13 (  47 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 580 expanded)
%              Number of equality atoms :   40 (  89 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1119,plain,(
    $false ),
    inference(resolution,[],[f1098,f37])).

fof(f37,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

fof(f1098,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) ),
    inference(resolution,[],[f1050,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(superposition,[],[f54,f60])).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k6_subset_1(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(extensionality_resolution,[],[f47,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f41])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1050,plain,(
    ! [X18] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1049,f324])).

fof(f324,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f310,f60])).

fof(f310,plain,(
    ! [X2] : k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2)) ),
    inference(superposition,[],[f210,f60])).

fof(f210,plain,(
    ! [X0,X1] : k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f209,f34])).

fof(f34,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f209,plain,(
    ! [X0,X1] :
      ( k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).

fof(f1049,plain,(
    ! [X18] : r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k10_relat_1(sK1,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f1048,f34])).

fof(f1048,plain,(
    ! [X18] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k10_relat_1(sK1,k1_xboole_0))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f1033,f153])).

fof(f153,plain,(
    ! [X2,X3] : r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1)) ),
    inference(resolution,[],[f138,f54])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k10_relat_1(sK1,X1))
      | r1_tarski(X0,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f137,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f137,plain,(
    ! [X0] : r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f136,f34])).

fof(f136,plain,(
    ! [X0] :
      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f42,f70])).

fof(f70,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(resolution,[],[f39,f34])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

fof(f1033,plain,(
    ! [X18] :
      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k10_relat_1(sK1,k1_xboole_0))
      | ~ r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f43,f495])).

fof(f495,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) ),
    inference(superposition,[],[f491,f250])).

fof(f250,plain,(
    ! [X0,X1] : k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) ),
    inference(subsumption_resolution,[],[f249,f34])).

fof(f249,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f248,f35])).

fof(f248,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).

fof(f491,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ),
    inference(subsumption_resolution,[],[f490,f34])).

fof(f490,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f159,f35])).

fof(f159,plain,(
    ! [X6,X5] :
      ( ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5)
      | k1_xboole_0 = k6_subset_1(k9_relat_1(X5,k10_relat_1(X5,X6)),X6) ) ),
    inference(resolution,[],[f44,f55])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:55:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (15076)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (15074)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (15096)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (15075)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.30/0.54  % (15087)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.30/0.54  % (15082)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.54  % (15098)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.54  % (15090)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.54  % (15088)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.30/0.54  % (15091)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.54  % (15084)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.54  % (15097)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.54  % (15077)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.30/0.54  % (15079)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.54  % (15080)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.30/0.54  % (15085)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.30/0.55  % (15102)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.55  % (15073)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.55  % (15095)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.30/0.55  % (15083)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.49/0.55  % (15101)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.49/0.56  % (15099)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.56  % (15100)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.49/0.56  % (15081)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.49/0.56  % (15093)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.49/0.56  % (15078)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.49/0.56  % (15092)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.49/0.56  % (15089)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.56  % (15089)Refutation not found, incomplete strategy% (15089)------------------------------
% 1.49/0.56  % (15089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (15089)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (15089)Memory used [KB]: 10618
% 1.49/0.56  % (15089)Time elapsed: 0.148 s
% 1.49/0.56  % (15089)------------------------------
% 1.49/0.56  % (15089)------------------------------
% 1.49/0.57  % (15094)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.59  % (15086)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.49/0.60  % (15079)Refutation found. Thanks to Tanya!
% 1.49/0.60  % SZS status Theorem for theBenchmark
% 1.49/0.60  % SZS output start Proof for theBenchmark
% 1.49/0.60  fof(f1119,plain,(
% 1.49/0.60    $false),
% 1.49/0.60    inference(resolution,[],[f1098,f37])).
% 1.49/0.60  fof(f37,plain,(
% 1.49/0.60    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 1.49/0.60    inference(cnf_transformation,[],[f30])).
% 1.49/0.60  fof(f30,plain,(
% 1.49/0.60    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 1.49/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29])).
% 1.49/0.60  fof(f29,plain,(
% 1.49/0.60    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 1.49/0.60    introduced(choice_axiom,[])).
% 1.49/0.60  fof(f16,plain,(
% 1.49/0.60    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.49/0.60    inference(flattening,[],[f15])).
% 1.49/0.60  fof(f15,plain,(
% 1.49/0.60    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.49/0.60    inference(ennf_transformation,[],[f14])).
% 1.49/0.60  fof(f14,negated_conjecture,(
% 1.49/0.60    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.49/0.60    inference(negated_conjecture,[],[f13])).
% 1.49/0.60  fof(f13,conjecture,(
% 1.49/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).
% 1.49/0.60  fof(f1098,plain,(
% 1.49/0.60    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) )),
% 1.49/0.60    inference(resolution,[],[f1050,f88])).
% 1.49/0.60  fof(f88,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f81,f64])).
% 1.49/0.60  fof(f64,plain,(
% 1.49/0.60    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 1.49/0.60    inference(superposition,[],[f54,f60])).
% 1.49/0.60  fof(f60,plain,(
% 1.49/0.60    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.49/0.60    inference(resolution,[],[f55,f57])).
% 1.49/0.60  fof(f57,plain,(
% 1.49/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.49/0.60    inference(equality_resolution,[],[f46])).
% 1.49/0.60  fof(f46,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.49/0.60    inference(cnf_transformation,[],[f32])).
% 1.49/0.60  fof(f32,plain,(
% 1.49/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.60    inference(flattening,[],[f31])).
% 1.49/0.60  fof(f31,plain,(
% 1.49/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.49/0.60    inference(nnf_transformation,[],[f1])).
% 1.49/0.60  fof(f1,axiom,(
% 1.49/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.49/0.60  fof(f55,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k6_subset_1(X0,X1)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f49,f41])).
% 1.49/0.60  fof(f41,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f6])).
% 1.49/0.60  fof(f6,axiom,(
% 1.49/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.49/0.60  fof(f49,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f33])).
% 1.49/0.60  fof(f33,plain,(
% 1.49/0.60    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.49/0.60    inference(nnf_transformation,[],[f2])).
% 1.49/0.60  fof(f2,axiom,(
% 1.49/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.49/0.60  fof(f54,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f40,f41])).
% 1.49/0.60  fof(f40,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f4])).
% 1.49/0.60  fof(f4,axiom,(
% 1.49/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.49/0.60  fof(f81,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k6_subset_1(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(extensionality_resolution,[],[f47,f56])).
% 1.49/0.60  fof(f56,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X0,X1) | r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(definition_unfolding,[],[f48,f41])).
% 1.49/0.60  fof(f48,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.49/0.60    inference(cnf_transformation,[],[f33])).
% 1.49/0.60  fof(f47,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f32])).
% 1.49/0.60  fof(f1050,plain,(
% 1.49/0.60    ( ! [X18] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k1_xboole_0)) )),
% 1.49/0.60    inference(forward_demodulation,[],[f1049,f324])).
% 1.49/0.60  fof(f324,plain,(
% 1.49/0.60    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.49/0.60    inference(forward_demodulation,[],[f310,f60])).
% 1.49/0.60  fof(f310,plain,(
% 1.49/0.60    ( ! [X2] : (k1_xboole_0 = k10_relat_1(sK1,k6_subset_1(X2,X2))) )),
% 1.49/0.60    inference(superposition,[],[f210,f60])).
% 1.49/0.60  fof(f210,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1))) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f209,f34])).
% 1.49/0.60  fof(f34,plain,(
% 1.49/0.60    v1_relat_1(sK1)),
% 1.49/0.60    inference(cnf_transformation,[],[f30])).
% 1.49/0.60  fof(f209,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k10_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.49/0.60    inference(resolution,[],[f50,f35])).
% 1.49/0.60  fof(f35,plain,(
% 1.49/0.60    v1_funct_1(sK1)),
% 1.49/0.60    inference(cnf_transformation,[],[f30])).
% 1.49/0.60  fof(f50,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f24])).
% 1.49/0.60  fof(f24,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.49/0.60    inference(flattening,[],[f23])).
% 1.49/0.60  fof(f23,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.49/0.60    inference(ennf_transformation,[],[f10])).
% 1.49/0.60  fof(f10,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k10_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_funct_1)).
% 1.49/0.60  fof(f1049,plain,(
% 1.49/0.60    ( ! [X18] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k10_relat_1(sK1,k1_xboole_0))) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f1048,f34])).
% 1.49/0.60  fof(f1048,plain,(
% 1.49/0.60    ( ! [X18] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k10_relat_1(sK1,k1_xboole_0)) | ~v1_relat_1(sK1)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f1033,f153])).
% 1.49/0.60  fof(f153,plain,(
% 1.49/0.60    ( ! [X2,X3] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,X2),X3),k1_relat_1(sK1))) )),
% 1.49/0.60    inference(resolution,[],[f138,f54])).
% 1.49/0.60  fof(f138,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k10_relat_1(sK1,X1)) | r1_tarski(X0,k1_relat_1(sK1))) )),
% 1.49/0.60    inference(resolution,[],[f137,f52])).
% 1.49/0.60  fof(f52,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f28])).
% 1.49/0.60  fof(f28,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.49/0.60    inference(flattening,[],[f27])).
% 1.49/0.60  fof(f27,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.49/0.60    inference(ennf_transformation,[],[f3])).
% 1.49/0.60  fof(f3,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.49/0.60  fof(f137,plain,(
% 1.49/0.60    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1))) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f136,f34])).
% 1.49/0.60  fof(f136,plain,(
% 1.49/0.60    ( ! [X0] : (r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.49/0.60    inference(superposition,[],[f42,f70])).
% 1.49/0.60  fof(f70,plain,(
% 1.49/0.60    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 1.49/0.60    inference(resolution,[],[f39,f34])).
% 1.49/0.60  fof(f39,plain,(
% 1.49/0.60    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f17])).
% 1.49/0.60  fof(f17,plain,(
% 1.49/0.60    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.60    inference(ennf_transformation,[],[f7])).
% 1.49/0.60  fof(f7,axiom,(
% 1.49/0.60    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.49/0.60  fof(f42,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f18])).
% 1.49/0.60  fof(f18,plain,(
% 1.49/0.60    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.49/0.60    inference(ennf_transformation,[],[f8])).
% 1.49/0.60  fof(f8,axiom,(
% 1.49/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k10_relat_1(X1,k2_relat_1(X1))))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).
% 1.49/0.60  fof(f1033,plain,(
% 1.49/0.60    ( ! [X18] : (r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k10_relat_1(sK1,k1_xboole_0)) | ~r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X18)),X18),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.49/0.60    inference(superposition,[],[f43,f495])).
% 1.49/0.60  fof(f495,plain,(
% 1.49/0.60    ( ! [X0] : (k1_xboole_0 = k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0))) )),
% 1.49/0.60    inference(superposition,[],[f491,f250])).
% 1.49/0.60  fof(f250,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1))) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f249,f34])).
% 1.49/0.60  fof(f249,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_relat_1(sK1)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f248,f35])).
% 1.49/0.60  fof(f248,plain,(
% 1.49/0.60    ( ! [X0,X1] : (k9_relat_1(sK1,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 1.49/0.60    inference(resolution,[],[f51,f36])).
% 1.49/0.60  fof(f36,plain,(
% 1.49/0.60    v2_funct_1(sK1)),
% 1.49/0.60    inference(cnf_transformation,[],[f30])).
% 1.49/0.60  fof(f51,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f26])).
% 1.49/0.60  fof(f26,plain,(
% 1.49/0.60    ! [X0,X1,X2] : (k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.49/0.60    inference(flattening,[],[f25])).
% 1.49/0.60  fof(f25,plain,(
% 1.49/0.60    ! [X0,X1,X2] : ((k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.49/0.60    inference(ennf_transformation,[],[f9])).
% 1.49/0.60  fof(f9,axiom,(
% 1.49/0.60    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k9_relat_1(X2,k6_subset_1(X0,X1)) = k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_funct_1)).
% 1.49/0.60  fof(f491,plain,(
% 1.49/0.60    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f490,f34])).
% 1.49/0.60  fof(f490,plain,(
% 1.49/0.60    ( ! [X0] : (~v1_relat_1(sK1) | k1_xboole_0 = k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0)) )),
% 1.49/0.60    inference(resolution,[],[f159,f35])).
% 1.49/0.60  fof(f159,plain,(
% 1.49/0.60    ( ! [X6,X5] : (~v1_funct_1(X5) | ~v1_relat_1(X5) | k1_xboole_0 = k6_subset_1(k9_relat_1(X5,k10_relat_1(X5,X6)),X6)) )),
% 1.49/0.60    inference(resolution,[],[f44,f55])).
% 1.49/0.60  fof(f44,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f22])).
% 1.49/0.60  fof(f22,plain,(
% 1.49/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.49/0.60    inference(flattening,[],[f21])).
% 1.49/0.60  fof(f21,plain,(
% 1.49/0.60    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.49/0.60    inference(ennf_transformation,[],[f11])).
% 1.49/0.60  fof(f11,axiom,(
% 1.49/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 1.49/0.60  fof(f43,plain,(
% 1.49/0.60    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f20])).
% 1.49/0.60  fof(f20,plain,(
% 1.49/0.60    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.49/0.60    inference(flattening,[],[f19])).
% 1.49/0.60  fof(f19,plain,(
% 1.49/0.60    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.49/0.60    inference(ennf_transformation,[],[f12])).
% 1.49/0.60  fof(f12,axiom,(
% 1.49/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).
% 1.49/0.60  % SZS output end Proof for theBenchmark
% 1.49/0.60  % (15079)------------------------------
% 1.49/0.60  % (15079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.60  % (15079)Termination reason: Refutation
% 1.49/0.60  
% 1.49/0.60  % (15079)Memory used [KB]: 11385
% 1.49/0.60  % (15079)Time elapsed: 0.186 s
% 1.49/0.60  % (15079)------------------------------
% 1.49/0.60  % (15079)------------------------------
% 1.49/0.60  % (15072)Success in time 0.238 s
%------------------------------------------------------------------------------
